#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
运动轨迹格式互转工具 —— GPX / TCX / FIT 三种格式任意互转
================================================================

特点
----
* 纯标准库实现（含 FIT 二进制格式的编码与解码），不需要安装任何第三方包。
* ttk + clam 主题，界面只保留必需控件：
    1) 「选择文件」按钮 —— 打开系统文件对话框挑一个 .gpx / .tcx / .fit
    2) 「开始转换」按钮 —— 执行转换
    3) 「退出」按钮
* 处理过程与处理后的汇总信息输出到命令行窗口，同时镜像显示在界面日志区
  （Windows 上双击运行没有控制台时也能看到全部信息）。
* 转换完成后会立刻回读输出文件做一次自校验，确认写入的数据可被再次解析。

时间口径说明（重要）
--------------------
GPX / TCX 的 <time> 按 xsd:dateTime 规定应为 UTC（以 Z 结尾），FIT 内部是
「1989-12-31T00:00:00Z 起的秒数」。但部分国行设备导出的轨迹把**北京墙钟**直接
挂上 Z 后缀（俗称"伪 Z"），若一律当真 UTC 处理，时间会整体差 8 小时。
因此本工具提供两种口径：

  A. 按文件声明（默认）：带 +08:00 这类数字偏移的按偏移真换算；Z 或裸时间视为 UTC。
  B. 伪 Z 修正：把 Z 后缀与裸时间都当作 UTC+8 墙钟，减去 8 小时得到真实 UTC。

无论选哪种，汇总区都会同时列出「另一种口径」对应的时间范围，便于人工核对。

格式能力边界（转换时会明确提示，不静默丢数据）
---------------------------------------------
  GPX : trkpt 必须带 lat/lon 属性 → 无坐标的点无法表示；<time> 可选；
        心率/步频/温度/速度写入 Garmin 扩展 gpxtpx，功率无标准字段会丢弃。
  TCX : Trackpoint 的 Time 是必需项 → 无时间戳的点无法表示；Position 可选；
        无温度字段，温度会丢弃。
  FIT : 坐标、时间、海拔、心率、步频、速度、功率、温度全部可表达（缺失写无效值），
        不丢任何点。

命令行用法（可选，便于脚本化）
------------------------------
    python3 track_converter.py <输入文件> <目标格式 gpx|tcx|fit> [--fake-z]
  不带参数启动则打开图形界面。
"""

from __future__ import annotations

import math
import os
import queue
import struct
import sys
import tempfile
import threading
import time
import traceback
import datetime as dt
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple

try:
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox
    TK_AVAILABLE = True
    TK_ERROR = None
except Exception as _tk_exc:      # 极少数环境没有 tkinter：命令行模式仍可用
    tk = None                     # type: ignore
    ttk = filedialog = messagebox = None   # type: ignore
    TK_AVAILABLE = False
    TK_ERROR = _tk_exc

APP_NAME = "运动轨迹格式互转工具"
APP_VER = "1.0"
CREATOR = "TrackConverter %s" % APP_VER

FORMAT_LABEL = {"gpx": "GPX", "tcx": "TCX", "fit": "FIT"}
EXT_OF = {"gpx": ".gpx", "tcx": ".tcx", "fit": ".fit"}

# 时间口径
MODE_DECLARED = "declared"   # 按文件声明
MODE_FAKE_Z = "fakez"        # 伪 Z 修正（墙钟按 UTC+8 解释）
MODE_LABEL = {
    MODE_DECLARED: "按文件声明（Z 视为 UTC）",
    MODE_FAKE_Z: "伪 Z 修正（Z/裸时间按 UTC+8 墙钟）",
}
MODE_BY_LABEL = {v: k for k, v in MODE_LABEL.items()}

TZ_CN = dt.timezone(dt.timedelta(hours=8))

NS_GPX = "http://www.topografix.com/GPX/1/1"
NS_GPX_OLD = "http://www.topografix.com/GPX/1/0"
NS_TCX = "http://www.garmin.com/xmlschemas/TrainingCenterDatabase/v2"
NS_TCX_AX = "http://www.garmin.com/xmlschemas/ActivityExtension/v2"
NS_GPXTPX = "http://www.garmin.com/xmlschemas/TrackPointExtension/v1"
NS_XSI = "http://www.w3.org/2001/XMLSchema-instance"

FIT_EPOCH = dt.datetime(1989, 12, 31, tzinfo=dt.timezone.utc)

# ============================================================================
#  FIT 基础类型表（base_type 字节 → (字节宽度, 逻辑类型)）
# ============================================================================
BASE_TYPES: Dict[int, Tuple[int, str]] = {
    0x00: (1, "enum"),
    0x01: (1, "sint8"),
    0x02: (1, "uint8"),
    0x83: (2, "sint16"),
    0x84: (2, "uint16"),
    0x85: (4, "sint32"),
    0x86: (4, "uint32"),
    0x07: (1, "string"),
    0x88: (4, "float32"),
    0x89: (8, "float64"),
    0x0A: (1, "uint8z"),
    0x8B: (2, "uint16z"),
    0x8C: (4, "uint32z"),
    0x0D: (1, "byte"),
    0x8E: (8, "sint64"),
    0x8F: (8, "uint64"),
    0x90: (8, "uint64z"),
}

# 各逻辑类型的「无效值」
FIT_INVALID = {
    "enum": 0xFF, "sint8": 0x7F, "uint8": 0xFF,
    "sint16": 0x7FFF, "uint16": 0xFFFF,
    "sint32": 0x7FFFFFFF, "uint32": 0xFFFFFFFF,
    "uint8z": 0, "uint16z": 0, "uint32z": 0,
    "sint64": 0x7FFFFFFFFFFFFFFF, "uint64": 0xFFFFFFFFFFFFFFFF, "uint64z": 0,
}

# 各逻辑类型的取值范围（写入前钳位，超出会记录告警）
FIT_RANGE = {
    "enum": (0, 0xFE), "byte": (0, 0xFF),
    "sint8": (-128, 0x7E), "uint8": (0, 0xFE), "uint8z": (1, 0xFF),
    "sint16": (-32768, 0x7FFE), "uint16": (0, 0xFFFE), "uint16z": (1, 0xFFFF),
    "sint32": (-2147483648, 0x7FFFFFFE), "uint32": (0, 0xFFFFFFFE),
    "uint32z": (1, 0xFFFFFFFF),
}

FIT_CRC_TABLE = (
    0x0000, 0xCC01, 0xD801, 0x1400, 0xF001, 0x3C00, 0x2800, 0xE401,
    0xA001, 0x6C00, 0x7800, 0xB401, 0x5000, 0x9C01, 0x8801, 0x4400,
)

# FIT 消息号 / 字段号（已对照 Garmin profile 核实）
MESG_FILE_ID = 0
MESG_SESSION = 18
MESG_LAP = 19
MESG_RECORD = 20
MESG_ACTIVITY = 34

FILE_TYPE_ACTIVITY = 4
EVENT_SESSION = 8
EVENT_LAP = 9
EVENT_ACTIVITY = 26
EVENT_TYPE_STOP = 1
ACTIVITY_TYPE_MANUAL = 0

# 运动类型（统一内部名 → FIT sport 枚举）
SPORT_TO_FIT = {
    "running": 1, "cycling": 2, "swimming": 5, "walking": 11, "hiking": 17,
    "rowing": 15, "skiing": 12, "snowboarding": 14, "e_biking": 21,
    "skating": 30, "paddling": 37, "other": 0,
}
# FIT sport 枚举 → 统一内部名
FIT_TO_SPORT = {v: k for k, v in SPORT_TO_FIT.items()}
FIT_TO_SPORT[0] = "other"

SPORT_ALIAS = {
    "run": "running", "running": "running", "跑步": "running", "跑": "running",
    "bike": "cycling", "biking": "cycling", "cycling": "cycling", "ride": "cycling",
    "骑行": "cycling", "单车": "cycling", "cycle": "cycling",
    "walk": "walking", "walking": "walking", "徒步旅行": "walking", "步行": "walking",
    "hike": "hiking", "hiking": "hiking", "登山": "hiking", "越野跑": "hiking",
    "swim": "swimming", "swimming": "swimming", "游泳": "swimming",
    "row": "rowing", "rowing": "rowing", "划船": "rowing",
    "ski": "skiing", "skiing": "skiing", "cross_country_skiing": "skiing",
    "alpine_skiing": "skiing", "滑雪": "skiing",
    "snowboard": "snowboarding", "snowboarding": "snowboarding",
    "e_biking": "e_biking", "e-bike": "e_biking",
    "skate": "skating", "inline_skating": "skating", "ice_skating": "skating",
}


class TrackError(Exception):
    """可预期的业务错误，直接把 message 显示给用户。"""


# ============================================================================
#  通用小工具
# ============================================================================
def local_name(tag: Any) -> str:
    """去掉 XML 命名空间，取元素本地名；注释/处理指令不是 str，返回 ''。"""
    if not isinstance(tag, str):
        return ""
    return tag.rsplit("}", 1)[-1]


def disp_width(text: str) -> int:
    """按等宽终端显示宽度计算（中日韩字符算 2 列）。"""
    w = 0
    for ch in text:
        w += 2 if ord(ch) > 0x2E7F else 1
    return w


def ljust_disp(text: str, width: int) -> str:
    pad = width - disp_width(text)
    return text + " " * max(0, pad)


def fmt_size(nbytes: int) -> str:
    if nbytes < 1024:
        return "%d B" % nbytes
    if nbytes < 1024 * 1024:
        return "%.1f KB" % (nbytes / 1024.0)
    return "%.2f MB" % (nbytes / 1048576.0)


def fmt_dur(seconds: Optional[float]) -> str:
    if seconds is None:
        return "-"
    s = int(round(seconds))
    h, rem = divmod(s, 3600)
    m, sec = divmod(rem, 60)
    if h:
        return "%d:%02d:%02d" % (h, m, sec)
    return "%d:%02d" % (m, sec)


def fmt_utc(t: Optional[dt.datetime]) -> str:
    if t is None:
        return "-"
    return t.astimezone(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def fmt_local(t: Optional[dt.datetime], tz: dt.timezone = TZ_CN) -> str:
    if t is None:
        return "-"
    return t.astimezone(tz).strftime("%Y-%m-%d %H:%M:%S")


def num_str(v: Optional[float], nd: int = 1) -> str:
    if v is None:
        return "-"
    s = ("%%.%df" % nd) % v
    if "." in s:
        s = s.rstrip("0").rstrip(".")
    return s or "0"


def norm_sport(raw: Optional[str]) -> str:
    if not raw:
        return "other"
    key = str(raw).strip().lower().replace(" ", "_")
    if key in SPORT_ALIAS:
        return SPORT_ALIAS[key]
    for k, v in SPORT_ALIAS.items():
        if k and k in key:
            return v
    return "other"


def sport_to_tcx(sport: str) -> str:
    if sport == "running":
        return "Running"
    if sport in ("cycling", "e_biking"):
        return "Biking"
    return "Other"


def sport_from_tcx(raw: Optional[str]) -> str:
    if not raw:
        return "other"
    key = raw.strip().lower()
    if key.startswith("run"):
        return "running"
    if key.startswith("bik") or key.startswith("cycl"):
        return "cycling"
    return "other"


def haversine(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    """两点间大圆距离（米）。"""
    r = 6371008.8
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp = p2 - p1
    dl = math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(min(1.0, math.sqrt(a)))


def to_float(text: Optional[str]) -> Optional[float]:
    if text is None:
        return None
    s = str(text).strip()
    if not s:
        return None
    try:
        return float(s)
    except ValueError:
        return None


def to_int(text: Optional[str]) -> Optional[int]:
    v = to_float(text)
    return None if v is None else int(round(v))


def find_first_child(elem: ET.Element, *names: str) -> Optional[ET.Element]:
    """在自己的直接子元素里按本地名查找。"""
    wanted = set(names)
    for c in elem:
        if local_name(c.tag) in wanted:
            return c
    return None


def find_descendant(elem: ET.Element, *names: str, skip_self: bool = True) -> Optional[ET.Element]:
    """在整棵子树里按本地名查找（跳过自身）。"""
    wanted = set(names)
    for e in elem.iter():
        if skip_self and e is elem:
            continue
        if local_name(e.tag) in wanted:
            return e
    return None


def child_text(elem: ET.Element, *names: str) -> Optional[str]:
    c = find_first_child(elem, *names)
    if c is None:
        return None
    return c.text


def desc_text(elem: ET.Element, *names: str) -> Optional[str]:
    c = find_descendant(elem, *names)
    if c is None:
        return None
    return c.text


# ============================================================================
#  数据模型
# ============================================================================
@dataclass
class Point:
    time: Optional[dt.datetime] = None   # 带时区的 UTC 时间
    lat: Optional[float] = None
    lon: Optional[float] = None
    ele: Optional[float] = None          # 海拔 m
    hr: Optional[int] = None             # 心率 bpm
    cad: Optional[int] = None            # 步频 / 踏频
    speed: Optional[float] = None        # m/s
    power: Optional[float] = None        # W
    temp: Optional[float] = None         # ℃
    dist: Optional[float] = None         # 累计距离 m（源文件提供或后续推算）


@dataclass
class Track:
    points: List[Point] = field(default_factory=list)
    sport: str = "other"
    name: str = ""
    src_format: str = ""
    src_version: str = ""
    src_path: str = ""
    tz_offset: Optional[int] = None      # 源文件能确定的录制时区偏移（秒）
    notes: List[str] = field(default_factory=list)   # 解析阶段的提示
    meta: Dict[str, Any] = field(default_factory=dict)

    def times(self) -> List[dt.datetime]:
        return [p.time for p in self.points if p.time is not None]


# ============================================================================
#  时间解析
# ============================================================================
_TIME_FORMATS = (
    "%Y-%m-%dT%H:%M:%S.%f", "%Y-%m-%dT%H:%M:%S", "%Y-%m-%dT%H:%M",
    "%Y-%m-%d %H:%M:%S.%f", "%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M",
    "%Y/%m/%d %H:%M:%S", "%Y/%m/%d %H:%M",
)


def parse_time_text(text: Optional[str]) -> Optional[Tuple[dt.datetime, Optional[int]]]:
    """
    解析时间文本，返回 (墙钟 naive datetime, 声明的偏移秒)。
    偏移为 None 表示文本没有携带**可用的时区信息**——裸时间，或只有 Z 后缀
    （Z 只能说明"作者认为这是 UTC"，不能说明录制时区，伪 Z 文件正是这种情况）。
    """
    if not text:
        return None
    s = str(text).strip()
    if not s:
        return None

    has_z = s.endswith("Z") or s.endswith("z")
    core = s[:-1].strip() if has_z else s

    # 优先用 fromisoformat（能吃到 +08:00 / +0800 这类偏移）
    try:
        d = dt.datetime.fromisoformat(core)
    except ValueError:
        d = None
    if d is not None:
        if d.tzinfo is not None:
            off = d.utcoffset()
            return d.replace(tzinfo=None), (int(off.total_seconds()) if off else 0)
        return d, None

    for fmt in _TIME_FORMATS:
        try:
            d = dt.datetime.strptime(core, fmt)
        except ValueError:
            continue
        if d.tzinfo is not None:
            off = d.utcoffset()
            return d.replace(tzinfo=None), int(off.total_seconds())
        return d, None
    return None


def resolve_time(text: Optional[str], mode: str) -> Optional[Tuple[dt.datetime, int, bool]]:
    """
    返回 (带时区的 UTC 时间, 采用的偏移秒, 该偏移是否"已知/可信")。
    tz_known=False 表示只能按假定处理，用于决定 FIT 的 local_timestamp 是否写入。
    """
    parsed = parse_time_text(text)
    if parsed is None:
        return None
    wall, offset = parsed
    if offset is None:
        # 裸时间或只有 Z：按所选口径解释
        if mode == MODE_FAKE_Z:
            utc = wall.replace(tzinfo=dt.timezone.utc) - dt.timedelta(hours=8)
            return utc, 8 * 3600, True
        utc = wall.replace(tzinfo=dt.timezone.utc)
        return utc, 0, False
    utc = wall.replace(tzinfo=dt.timezone.utc) - dt.timedelta(seconds=offset)
    return utc, offset, True


def fit_ts(t: dt.datetime) -> int:
    return int(round((t.astimezone(dt.timezone.utc) - FIT_EPOCH).total_seconds()))


def fit_ts_to_dt(seconds: int) -> dt.datetime:
    return FIT_EPOCH + dt.timedelta(seconds=seconds)


# ============================================================================
#  读取：GPX
# ============================================================================
def read_gpx(path: str, mode: str) -> Track:
    try:
        root = ET.parse(path).getroot()
    except Exception as exc:
        raise TrackError("GPX 文件解析失败：%s" % exc)
    if local_name(root.tag) != "gpx":
        raise TrackError("不是 GPX 文件（根元素为 <%s>）" % local_name(root.tag))

    trk = find_descendant(root, "trk")
    pts_els: List[ET.Element] = []
    kind = ""
    if trk is not None:
        pts_els = [e for e in trk.iter() if local_name(e.tag) == "trkpt"]
        kind = "trk/trkseg/trkpt"
    if not pts_els:
        pts_els = [e for e in root.iter() if local_name(e.tag) == "rtept"]
        kind = "rte/rtept" if pts_els else kind
    if not pts_els:
        pts_els = [e for e in root.iter() if local_name(e.tag) == "wpt"]
        kind = "wpt" if pts_els else kind
    if not pts_els:
        raise TrackError("GPX 里没有找到任何轨迹点（trkpt/rtept/wpt）")

    track = Track(src_format="gpx", src_path=path)
    ver = ""
    for k, v in (root.attrib or {}).items():
        if local_name(k) == "version":
            ver = v
    track.src_version = "GPX %s" % (ver or "1.0/1.1")
    track.meta["point_kind"] = kind
    creator = ""
    for k, v in (root.attrib or {}).items():
        if local_name(k) == "creator":
            creator = v
    if creator:
        track.meta["creator"] = creator

    name_txt = None
    if trk is not None:
        name_txt = child_text(trk, "name")
    if not name_txt:
        name_txt = desc_text(find_descendant(root, "metadata") or root, "name")
    track.name = (name_txt or "").strip()

    type_txt = None
    if trk is not None:
        type_txt = child_text(trk, "type")
    if type_txt:
        track.sport = norm_sport(type_txt)

    offsets_seen: List[int] = []
    bad_coord = bad_time = 0
    for el in pts_els:
        lat = to_float(el.get("lat"))
        lon = to_float(el.get("lon"))
        if lat is None or lon is None or not (-90.0 <= lat <= 90.0 and -180.0 <= lon <= 180.0):
            bad_coord += 1
            continue                       # 坐标非法/缺失：GPX 里本就无法表示，跳过并统计
        p = Point(lat=lat, lon=lon)
        p.ele = to_float(child_text(el, "ele"))
        t_raw = child_text(el, "time")
        if t_raw:
            r = resolve_time(t_raw, mode)
            if r is None:
                bad_time += 1
            else:
                p.time, off, known = r
                if known:
                    offsets_seen.append(off)
        else:
            if kind == "trkpt":
                bad_time += 1
        # 心率 / 步频 / 温度 / 速度：GPX 1.0 直接子元素 或 各版本扩展
        for key, setter in (
            (("hr", "heartrate", "heart_rate", "bpm"), "hr"),
            (("cad", "cadence"), "cad"),
            (("atemp", "temp", "temperature", "wtemp"), "temp"),
            (("speed", "enhancedspeed"), "speed"),
            (("power", "watts", "pwr"), "power"),
        ):
            v = to_float(desc_text(el, *key))
            if v is None:
                v = to_float(child_text(el, *key))
            if v is None:
                continue
            if setter in ("hr", "cad"):
                setattr(p, setter, int(round(v)))
            else:
                setattr(p, setter, v)
        track.points.append(p)

    if not track.points:
        raise TrackError("GPX 里的轨迹点全部缺失或坐标非法，无可用数据")
    if bad_coord:
        track.notes.append("跳过 %d 个坐标缺失/越界的点（GPX 的 trkpt 必须有合法 lat/lon）" % bad_coord)
    if bad_time and kind == "trkpt":
        track.notes.append("%d 个点没有可解析的 <time>（写 GPX 时会省略 time，写 TCX/FIT 时会被丢弃）" % bad_time)
    track.tz_offset = unique_offset(offsets_seen)
    return track


# ============================================================================
#  读取：TCX
# ============================================================================
def read_tcx(path: str, mode: str) -> Track:
    try:
        root = ET.parse(path).getroot()
    except Exception as exc:
        raise TrackError("TCX 文件解析失败：%s" % exc)
    if local_name(root.tag) != "TrainingCenterDatabase":
        raise TrackError("不是 TCX 文件（根元素为 <%s>）" % local_name(root.tag))

    activity = find_descendant(root, "Activity")
    if activity is None:
        raise TrackError("TCX 里没有 <Activity>（本工具转换的是活动记录，不处理 Course）")

    track = Track(src_format="tcx", src_path=path, src_version="TCX (TrainingCenterDatabase v2)")
    track.sport = sport_from_tcx(activity.get("Sport"))
    track.name = (child_text(activity, "Id") or "").strip()
    track.meta["laps"] = sum(1 for e in activity.iter() if local_name(e.tag) == "Lap")

    pts_els = [e for e in activity.iter() if local_name(e.tag) == "Trackpoint"]
    if not pts_els:
        raise TrackError("TCX 里没有找到任何 <Trackpoint>")

    offsets_seen: List[int] = []
    bad_time = 0
    for el in pts_els:
        t_raw = child_text(el, "Time")
        r = resolve_time(t_raw, mode) if t_raw else None
        if r is None:
            bad_time += 1
            continue                       # TCX 的 Time 是必需项，没时间无法表示
        p = Point(time=r[0])
        if r[2]:
            offsets_seen.append(r[1])
        pos = find_first_child(el, "Position")
        if pos is not None:
            p.lat = to_float(child_text(pos, "LatitudeDegrees"))
            p.lon = to_float(child_text(pos, "LongitudeDegrees"))
            if p.lat is not None and (not -90.0 <= p.lat <= 90.0):
                p.lat = p.lon = None
            if p.lon is not None and (not -180.0 <= p.lon <= 180.0):
                p.lat = p.lon = None
        p.ele = to_float(child_text(el, "AltitudeMeters"))
        p.dist = to_float(child_text(el, "DistanceMeters"))
        hr = find_first_child(el, "HeartRateBpm")
        if hr is not None:
            p.hr = to_int(child_text(hr, "Value"))
        p.cad = to_int(child_text(el, "Cadence"))
        ext = find_first_child(el, "Extensions")
        if ext is not None:
            p.speed = to_float(desc_text(ext, "Speed"))
            p.power = to_float(desc_text(ext, "Watts"))
            p.temp = to_float(desc_text(ext, "Temp", "Temperature"))
        track.points.append(p)

    if not track.points:
        raise TrackError("TCX 里的轨迹点全部缺失时间戳，无可用数据")
    if bad_time:
        track.notes.append("跳过 %d 个缺少/无法解析 <Time> 的 Trackpoint（TCX 要求 Time 必需）" % bad_time)
    n_lap = track.meta.get("laps") or 0
    if n_lap > 1:
        track.notes.append("源文件含 %d 个 Lap 分段，转换后按「单一分段」写出（只保留全部轨迹点）" % n_lap)
    track.tz_offset = unique_offset(offsets_seen)
    return track


def unique_offset(offsets: Sequence[int]) -> Optional[int]:
    if not offsets:
        return None
    first = offsets[0]
    if all(o == first for o in offsets):
        return first
    return None


# ============================================================================
#  读取：FIT
# ============================================================================
def fit_crc(data: bytes, crc: int = 0) -> int:
    for byte in data:
        tmp = FIT_CRC_TABLE[crc & 0xF]
        crc = (crc >> 4) & 0x0FFF
        crc = crc ^ tmp ^ FIT_CRC_TABLE[byte & 0xF]
        tmp = FIT_CRC_TABLE[crc & 0xF]
        crc = (crc >> 4) & 0x0FFF
        crc = crc ^ tmp ^ FIT_CRC_TABLE[(byte >> 4) & 0xF]
    return crc


_FIT_UNPACK = {
    "sint8": "b", "uint8": "B", "sint16": "h", "uint16": "H",
    "sint32": "i", "uint32": "I", "sint64": "q", "uint64": "Q",
    "float32": "f", "float64": "d",
    "enum": "B", "byte": "B", "uint8z": "B", "uint16z": "H", "uint32z": "I",
    "string": None,
}


def _fit_decode(raw: bytes, kind: str, arch: str) -> Any:
    if kind == "byte":
        return raw
    if kind == "string":
        try:
            return raw.rstrip(b"\x00").decode("utf-8", "replace")
        except Exception:
            return None
    fmt = _FIT_UNPACK.get(kind)
    if fmt is None:
        return None
    try:
        return struct.unpack(arch + fmt, raw)[0]
    except struct.error:
        return None


def _fit_valid(value: Any, kind: str) -> bool:
    if value is None:
        return False
    if kind in ("float32", "float64"):
        return not (isinstance(value, float) and math.isnan(value))
    inv = FIT_INVALID.get(kind)
    if inv is None:
        return True
    return value != inv


def parse_fit_messages(raw: bytes) -> Tuple[List[Tuple[int, Dict[int, Any]]], Dict[str, Any]]:
    """把 FIT 二进制解析成 [(global_msg_num, {field_num: 值})]，并返回头部信息。"""
    if len(raw) < 12:
        raise TrackError("FIT 文件长度不足 12 字节，不是有效文件")
    if raw[8:12] != b".FIT":
        raise TrackError("缺少 .FIT 标识，不是有效的 FIT 文件")

    header_size = raw[0]
    proto = raw[1]
    profile = struct.unpack("<H", raw[2:4])[0]
    data_size = struct.unpack("<I", raw[4:8])[0]
    if header_size < 12 or header_size > len(raw):
        raise TrackError("FIT 头部长度字段异常（%d）" % header_size)
    if header_size + data_size > len(raw):
        raise TrackError("FIT 数据区被截断（声明 %d 字节，实际剩 %d）"
                         % (data_size, len(raw) - header_size))
    body = raw[header_size:header_size + data_size]

    info: Dict[str, Any] = {
        "header_size": header_size,
        "protocol": "%.1f" % (proto / 16.0),
        "profile": profile,
        "data_size": data_size,
    }
    if header_size >= 14:
        hcrc = struct.unpack("<H", raw[12:14])[0]
        info["header_crc_ok"] = (hcrc == 0) or (fit_crc(raw[0:12]) == hcrc)
        info["header_crc"] = hcrc
    tail = raw[header_size + data_size:header_size + data_size + 2]
    if len(tail) == 2:
        fcrc = struct.unpack("<H", tail)[0]
        info["file_crc"] = fcrc
        info["file_crc_ok"] = (fit_crc(raw[0:header_size + data_size]) == fcrc)
    else:
        info["file_crc_ok"] = None
    info["trailing"] = max(0, len(raw) - header_size - data_size - 2)

    messages: List[Tuple[int, Dict[int, Any]]] = []
    defs: Dict[int, Tuple[int, str, List[Tuple[int, int, int]]]] = {}
    last_ts = 0
    pos = 0
    n = len(body)
    while pos < n:
        hdr = body[pos]
        pos += 1
        if hdr & 0x80:
            # 压缩时间戳数据消息：时间戳由头部推算，数据里**不包含** timestamp 字段
            local = (hdr >> 5) & 0x03
            offset = hdr & 0x1F
            if local not in defs:
                raise TrackError("FIT 结构异常：压缩消息引用了未定义的 local type %d" % local)
            gmn, arch, fields = defs[local]
            values: Dict[int, Any] = {}
            has_ts_field = any(f[0] == 253 for f in fields)
            for fnum, size, btype in fields:
                if fnum == 253:
                    continue
                if pos + size > n:
                    raise TrackError("FIT 数据区在读取字段时被截断")
                kind = BASE_TYPES.get(btype, (size, "byte"))[1]
                val = _fit_decode(body[pos:pos + size], kind, arch)
                pos += size
                if _fit_valid(val, kind):
                    values[fnum] = val
            if has_ts_field:
                # 时间戳由头部 5 bit 偏移与上一次的完整时间戳拼出（32 秒回绕）
                ts = (last_ts & ~0x1F) + offset
                if ts < last_ts:
                    ts += 0x20
                values[253] = ts
                last_ts = ts
            messages.append((gmn, values))
            continue

        local = hdr & 0x0F
        if hdr & 0x40:
            has_dev = bool(hdr & 0x20)
            if pos + 6 > n:
                raise TrackError("FIT 定义消息被截断")
            pos += 1                                  # reserved
            arch_flag = body[pos]
            pos += 1
            arch = ">" if arch_flag else "<"
            gmn = struct.unpack(arch + "H", body[pos:pos + 2])[0]
            pos += 2
            nfields = body[pos]
            pos += 1
            fields = []
            for _ in range(nfields):
                if pos + 3 > n:
                    raise TrackError("FIT 字段定义被截断")
                fields.append((body[pos], body[pos + 1], body[pos + 2]))
                pos += 3
            if has_dev:
                if pos >= n:
                    raise TrackError("FIT 开发者字段定义被截断")
                ndev = body[pos]
                pos += 1
                pos += 3 * ndev
            defs[local] = (gmn, arch, fields)
            messages.append((-1, {"gmn": gmn, "nfields": nfields}))
        else:
            if local not in defs:
                raise TrackError("FIT 结构异常：数据消息引用了未定义的 local type %d" % local)
            gmn, arch, fields = defs[local]
            values = {}
            for fnum, size, btype in fields:
                if pos + size > n:
                    raise TrackError("FIT 数据区在读取字段时被截断")
                kind = BASE_TYPES.get(btype, (size, "byte"))[1]
                val = _fit_decode(body[pos:pos + size], kind, arch)
                pos += size
                if _fit_valid(val, kind):
                    values[fnum] = val
            if 253 in values and isinstance(values[253], int):
                last_ts = values[253]
            messages.append((gmn, values))
    return messages, info


SEMI = 180.0 / 2147483648.0        # 半圆 → 度


def read_fit(path: str, mode: str) -> Track:
    with open(path, "rb") as f:
        raw = f.read()
    messages, info = parse_fit_messages(raw)

    track = Track(src_format="fit", src_path=path)
    track.src_version = "FIT 协议 %s / profile %s" % (info["protocol"], info["profile"])
    track.meta["fit_info"] = info

    if info.get("header_crc_ok") is False:
        track.notes.append("FIT 头部 CRC 不匹配（文件可能被改动过，仍继续解析）")
    if info.get("file_crc_ok") is False:
        track.notes.append("FIT 文件 CRC 不匹配（文件可能被截断或改动过，仍继续解析）")
    if info.get("trailing"):
        track.notes.append("文件尾部有 %d 字节的多余数据（可能含有第二个 FIT 文件，已忽略）"
                           % info["trailing"])

    created = None
    for gmn, values in messages:
        if gmn == MESG_FILE_ID:
            track.meta["manufacturer"] = values.get(1)
            track.meta["product"] = values.get(2)
            if 4 in values:
                created = values[4]
        elif gmn == MESG_SESSION:
            if 5 in values:
                track.sport = FIT_TO_SPORT.get(int(values[5]), "other")
            if 6 in values:
                track.meta["sub_sport"] = values[6]
            if 20 in values:
                track.meta["avg_power"] = values[20]
        elif gmn == MESG_ACTIVITY and 5 in values:
            track.meta["local_timestamp"] = values[5]

    bad = 0
    for gmn, values in messages:
        if gmn != MESG_RECORD:
            continue
        p = Point()
        if 253 in values:
            p.time = fit_ts_to_dt(int(values[253]))
        if 0 in values and 1 in values:
            lat = float(values[0]) * SEMI
            lon = float(values[1]) * SEMI
            if -90.0 <= lat <= 90.0 and -180.0 <= lon <= 180.0 and not (lat == 0.0 and lon == 0.0):
                p.lat, p.lon = lat, lon
        if 2 in values:
            p.ele = float(values[2]) / 5.0 - 500.0
        elif 78 in values:                                   # enhanced_altitude
            p.ele = float(values[78]) / 5.0 - 500.0
        if 3 in values:
            p.hr = int(values[3])
        if 4 in values:
            p.cad = int(values[4])
        if 6 in values:
            p.speed = float(values[6]) / 1000.0
        elif 73 in values:
            p.speed = float(values[73]) / 1000.0
        if 5 in values:
            p.dist = float(values[5]) / 100.0
        if 7 in values:
            p.power = float(values[7])
        elif 29 in values:                                   # accumulated_power
            p.power = float(values[29])
        if 13 in values:
            p.temp = float(values[13])
        if p.time is None and p.lat is None:
            bad += 1
            continue
        track.points.append(p)

    if not track.points:
        raise TrackError("FIT 里没有找到任何 record 轨迹点")
    if bad:
        track.notes.append("跳过 %d 个既无时间戳也无坐标的 record" % bad)
    # FIT 内部一律是 UTC 秒数，时区信息只可能存在 local_timestamp 里
    # （local_timestamp 对应活动结束时刻，所以用最后一个带时间的点去反推偏移）
    if track.meta.get("local_timestamp") and track.points:
        tail = [p.time for p in track.points if p.time is not None]
        if tail:
            off = int(track.meta["local_timestamp"]) - fit_ts(tail[-1])
            if -14 * 3600 <= off <= 14 * 3600 and off != 0:
                track.tz_offset = off
    if created:
        track.meta["created"] = fit_ts_to_dt(int(created))
    return track


# ============================================================================
#  读取入口
# ============================================================================
def guess_format(path: str) -> Optional[str]:
    ext = os.path.splitext(path)[1].lower().lstrip(".")
    if ext in ("gpx", "tcx", "fit"):
        return ext
    try:
        with open(path, "rb") as f:
            head = f.read(4096)
    except OSError:
        return None
    if len(head) > 12 and head[8:12] == b".FIT":
        return "fit"
    text = head.decode("utf-8", "ignore")
    if "<gpx" in text or "topografix.com/GPX" in text:
        return "gpx"
    if "TrainingCenterDatabase" in text:
        return "tcx"
    return None


def read_track(path: str, mode: str) -> Track:
    fmt = guess_format(path)
    if fmt is None:
        raise TrackError("无法识别文件格式（按扩展名与内容判断都不是 GPX/TCX/FIT）")
    reader = {"gpx": read_gpx, "tcx": read_tcx, "fit": read_fit}[fmt]
    track = reader(path, mode)
    if not track.points:
        raise TrackError("没有解析到任何轨迹点")
    return track


# ============================================================================
#  派生数据：累计距离 / 速度
# ============================================================================
@dataclass
class Derived:
    cum: List[Optional[float]] = field(default_factory=list)     # 每点累计距离 m
    speed: List[Optional[float]] = field(default_factory=list)   # 每点速度 m/s
    dist_source: str = "计算"      # 「源字段」或「计算」
    speed_source: str = "无"       # 「源字段」/「推算」/「无」
    non_monotonic: int = 0
    gaps: int = 0


def derive(points: Sequence[Point]) -> Derived:
    """给每个点补出累计距离与速度。源文件已提供且可信的优先使用。"""
    d = Derived()
    n = len(points)

    # --- 累计距离 ---
    have_src = sum(1 for p in points if p.dist is not None)
    src_ok = have_src >= max(1, int(n * 0.8))
    if src_ok:
        prev = None
        for p in points:
            if p.dist is None:
                src_ok = False
                break
            if prev is not None and p.dist + 1e-6 < prev:
                d.non_monotonic += 1
            prev = p.dist
        if d.non_monotonic > 0:
            src_ok = False
    if src_ok:
        d.cum = [p.dist for p in points]
        d.dist_source = "源字段"
    else:
        acc = 0.0
        prev: Optional[Point] = None
        for p in points:
            if prev is not None and p.lat is not None and prev.lat is not None:
                acc += haversine(prev.lat, prev.lon, p.lat, p.lon)
            d.cum.append(acc)
            if p.lat is not None:
                prev = p
        d.dist_source = "计算"
        if have_src and not src_ok:
            d.non_monotonic = max(d.non_monotonic, 1)

    # --- 速度 ---
    src_speed = sum(1 for p in points if p.speed is not None)
    used_computed = False
    for i, p in enumerate(points):
        if p.speed is not None and p.speed >= 0:
            d.speed.append(p.speed)
            continue
        v = None
        if i > 0:
            a, b = points[i - 1], points[i]
            if (a.time is not None and b.time is not None and a.lat is not None
                    and b.lat is not None):
                dts = (b.time - a.time).total_seconds()
                dd = (d.cum[i] or 0.0) - (d.cum[i - 1] or 0.0)
                if 0.0 < dts <= 60.0 and dd >= 0.0:
                    v = dd / dts
                    used_computed = True
        d.speed.append(v)
    if src_speed and used_computed:
        d.speed_source = "源字段+推算"
    elif src_speed:
        d.speed_source = "源字段"
    elif used_computed:
        d.speed_source = "推算"
    else:
        d.speed_source = "无"

    # 时间断点（间隔 > 60s 视为一次暂停/中断）
    for i in range(1, len(points)):
        a, b = points[i - 1].time, points[i].time
        if a is not None and b is not None and (b - a).total_seconds() > 60.0:
            d.gaps += 1
    return d


# ============================================================================
#  写出：GPX 1.1
# ============================================================================
def _indent(elem: ET.Element, level: int = 0, space: str = "  ") -> None:
    pad = "\n" + level * space
    if len(elem):
        if not (elem.text or "").strip():
            elem.text = pad + space
        if not (elem.tail or "").strip():
            elem.tail = pad
        for c in elem:
            _indent(c, level + 1, space)
        if not (elem[-1].tail or "").strip():
            elem[-1].tail = pad
    else:
        if level and not (elem.tail or "").strip():
            elem.tail = pad


def _serialize(root: ET.Element) -> bytes:
    _indent(root)
    if not (root.tail or "").strip():
        root.tail = "\n"
    xml = ET.tostring(root, encoding="unicode")
    return ('<?xml version="1.0" encoding="UTF-8"?>\n' + xml).encode("utf-8")


def _num(v: Optional[float], nd: int, plus: bool = False) -> Optional[str]:
    if v is None:
        return None
    s = ("%%.%df" % nd) % v
    if plus and v >= 0:
        s = "+" + s
    return s


def write_gpx(track: Track, derived: Derived, path: str) -> Tuple[bytes, Dict[str, Any]]:
    ET.register_namespace("", NS_GPX)
    ET.register_namespace("xsi", NS_XSI)
    ET.register_namespace("gpxtpx", NS_GPXTPX)
    info: Dict[str, Any] = {"dropped_no_pos": 0, "dropped_fields": []}

    gpx = ET.Element("{%s}gpx" % NS_GPX, {
        "version": "1.1",
        "creator": CREATOR,
        "{%s}schemaLocation" % NS_XSI: "%s http://www.topografix.com/GPX/1/1/gpx.xsd "
                                       "%s http://www.garmin.com/xmlschemas/TrackPointExtensionv1.xsd"
                                       % (NS_GPX, NS_GPXTPX),
    })
    meta = ET.SubElement(gpx, "metadata")
    if track.name:
        ET.SubElement(meta, "name").text = track.name
    t0 = track.times()
    if t0:
        ET.SubElement(meta, "time").text = fmt_utc(t0[0])

    trk = ET.SubElement(gpx, "trk")
    ET.SubElement(trk, "name").text = track.name or os.path.basename(track.src_path)
    ET.SubElement(trk, "type").text = track.sport
    seg = ET.SubElement(trk, "trkseg")

    wrote = 0
    for i, p in enumerate(track.points):
        if p.lat is None or p.lon is None:
            info["dropped_no_pos"] += 1
            continue
        el = ET.SubElement(seg, "trkpt", {
            "lat": _num(p.lat, 7) or "0",
            "lon": _num(p.lon, 7) or "0",
        })
        if p.ele is not None:
            ET.SubElement(el, "ele").text = _num(p.ele, 2)
        if p.time is not None:
            ET.SubElement(el, "time").text = fmt_utc(p.time)
        if any(v is not None for v in (p.hr, p.cad, p.speed, p.temp)):
            ext = ET.SubElement(el, "extensions")
            tpx = ET.SubElement(ext, "{%s}TrackPointExtension" % NS_GPXTPX)
            if p.temp is not None:
                ET.SubElement(tpx, "{%s}atemp" % NS_GPXTPX).text = _num(p.temp, 1)
            if p.hr is not None:
                ET.SubElement(tpx, "{%s}hr" % NS_GPXTPX).text = str(int(p.hr))
            if p.cad is not None:
                ET.SubElement(tpx, "{%s}cad" % NS_GPXTPX).text = str(int(p.cad))
            if p.speed is not None:
                ET.SubElement(tpx, "{%s}speed" % NS_GPXTPX).text = _num(p.speed, 3)
        wrote += 1

    if any(p.power is not None for p in track.points):
        info["dropped_fields"].append("功率（GPX 无标准字段）")
    info["wrote"] = wrote
    return _serialize(gpx), info


# ============================================================================
#  写出：TCX
# ============================================================================
def write_tcx(track: Track, derived: Derived, path: str) -> Tuple[bytes, Dict[str, Any]]:
    ET.register_namespace("", NS_TCX)
    ET.register_namespace("xsi", NS_XSI)
    info: Dict[str, Any] = {"dropped_no_time": 0, "dropped_fields": ["温度（TCX 无对应字段）"]
                            if any(p.temp is not None for p in track.points) else []}

    pts = [(i, p) for i, p in enumerate(track.points) if p.time is not None]
    info["dropped_no_time"] = len(track.points) - len(pts)
    if not pts:
        raise TrackError("源文件没有任何可用的时间戳，无法生成 TCX（TCX 的 Trackpoint 必须有 Time）")
    if info["dropped_no_time"]:
        info["dropped_fields"].append("详见日志：%d 个无时间戳的点" % info["dropped_no_time"])

    db = ET.Element("{%s}TrainingCenterDatabase" % NS_TCX, {
        "{%s}schemaLocation" % NS_XSI:
            "%s http://www.garmin.com/xmlschemas/TrainingCenterDatabasev2.xsd" % NS_TCX,
    })
    acts = ET.SubElement(db, "Activities")
    act = ET.SubElement(acts, "Activity", {"Sport": sport_to_tcx(track.sport)})

    first_p, last_p = pts[0][1], pts[-1][1]
    ET.SubElement(act, "Id").text = fmt_utc(first_p.time)
    lap = ET.SubElement(act, "Lap", {"StartTime": fmt_utc(first_p.time)})

    elapsed = max(0.0, (last_p.time - first_p.time).total_seconds())
    total_dist = 0.0
    for i, p in pts:
        if derived.cum[i] is not None:
            total_dist = max(total_dist, derived.cum[i])

    ET.SubElement(lap, "TotalTimeSeconds").text = "%.1f" % elapsed
    ET.SubElement(lap, "DistanceMeters").text = "%.2f" % total_dist
    speeds = [v for v in derived.speed if v is not None]
    if speeds:
        ET.SubElement(lap, "MaximumSpeed").text = "%.3f" % max(speeds)
    ET.SubElement(lap, "Calories").text = "0"        # TCX 要求该项，源文件无卡路里数据时写 0
    hrs = [p.hr for _, p in pts if p.hr is not None]
    if hrs:
        avg = ET.SubElement(lap, "AverageHeartRateBpm")
        ET.SubElement(avg, "Value").text = str(int(round(sum(hrs) / float(len(hrs)))))
        mx = ET.SubElement(lap, "MaximumHeartRateBpm")
        ET.SubElement(mx, "Value").text = str(max(hrs))
    ET.SubElement(lap, "Intensity").text = "Active"
    cads = [p.cad for _, p in pts if p.cad is not None]
    if cads:
        ET.SubElement(lap, "Cadence").text = str(int(round(sum(cads) / float(len(cads)))))
    ET.SubElement(lap, "TriggerMethod").text = "Manual"

    trk = ET.SubElement(lap, "Track")
    wrote = 0
    for i, p in pts:
        tp = ET.SubElement(trk, "Trackpoint")
        ET.SubElement(tp, "Time").text = fmt_utc(p.time)
        if p.lat is not None and p.lon is not None:
            pos = ET.SubElement(tp, "Position")
            ET.SubElement(pos, "LatitudeDegrees").text = _num(p.lat, 7)
            ET.SubElement(pos, "LongitudeDegrees").text = _num(p.lon, 7)
        if p.ele is not None:
            ET.SubElement(tp, "AltitudeMeters").text = _num(p.ele, 2)
        if derived.cum[i] is not None:
            ET.SubElement(tp, "DistanceMeters").text = "%.2f" % derived.cum[i]
        if p.hr is not None:
            hr = ET.SubElement(tp, "HeartRateBpm")
            ET.SubElement(hr, "Value").text = str(int(p.hr))
        if p.cad is not None:
            ET.SubElement(tp, "Cadence").text = str(int(p.cad))
        sp = derived.speed[i]
        if sp is not None or p.power is not None:
            ext = ET.SubElement(tp, "Extensions")
            tpx = ET.SubElement(ext, "{%s}TPX" % NS_TCX_AX)
            if sp is not None:
                ET.SubElement(tpx, "{%s}Speed" % NS_TCX_AX).text = _num(sp, 3)
            if p.power is not None:
                ET.SubElement(tpx, "{%s}Watts" % NS_TCX_AX).text = str(int(round(p.power)))
        wrote += 1
    info["wrote"] = wrote

    creator = ET.SubElement(act, "Creator", {"{%s}type" % NS_XSI: "Device_t"})
    ET.SubElement(creator, "Name").text = CREATOR
    ET.SubElement(creator, "UnitId").text = "0"
    ET.SubElement(creator, "ProductID").text = "0"
    ver = ET.SubElement(creator, "Version")
    ET.SubElement(ver, "VersionMajor").text = "1"
    ET.SubElement(ver, "VersionMinor").text = "0"

    return _serialize(db), info


# ============================================================================
#  写出：FIT
# ============================================================================
class FitWriter:
    """极简 FIT 编码器：只写本工具需要的几种消息。"""

    def __init__(self) -> None:
        self.buf = bytearray()
        self.warnings: List[str] = []

    def _clamp(self, kind: str, value: float, label: str) -> int:
        lo, hi = FIT_RANGE.get(kind, (-2 ** 63, 2 ** 63 - 1))
        # 四舍五入（半数远离零），而不是用了银行家舍入的 round()：
        # FIT 全是整型字段，20.5℃ 应写成 21 而不是 20
        v = int(math.floor(value + 0.5)) if value >= 0 else int(math.ceil(value - 0.5))
        if v < lo or v > hi:
            self.warnings.append("%s 超出 FIT 可表示范围（%s），已钳位" % (label, value))
            v = max(lo, min(hi, v))
        return v

    def _encode(self, base: int, value: Any, label: str) -> bytes:
        size, kind = BASE_TYPES[base]
        if value is None:
            inv = FIT_INVALID.get(kind)
            if inv is None:
                return b"\xFF" * size
            try:
                return int(inv).to_bytes(size, "little")
            except OverflowError:
                return b"\xFF" * size
        if kind in ("sint8", "sint16", "sint32", "sint64", "uint8", "uint16", "uint32",
                    "uint64", "uint8z", "uint16z", "uint32z", "enum", "byte"):
            v = self._clamp(kind, float(value), label)
            return v.to_bytes(size, "little", signed=kind.startswith("sint"))
        if kind in ("float32", "float64"):
            fmt = "f" if kind == "float32" else "d"
            return struct.pack("<" + fmt, float(value))
        if kind == "string":
            b = str(value).encode("utf-8")[:size]
            return b + b"\x00" * (size - len(b))
        return b"\xFF" * size

    def define(self, local: int, gmn: int, fields: Sequence[Tuple[int, int]]) -> None:
        self.buf.append(0x40 | (local & 0x0F))
        self.buf += bytes((0, 0))                       # reserved + 小端架构
        self.buf += struct.pack("<H", gmn)
        self.buf.append(len(fields))
        for num, base in fields:
            size, _ = BASE_TYPES[base]
            self.buf += bytes((num, size, base))

    def data(self, local: int, fields: Sequence[Tuple[int, int]],
             values: Dict[int, Any], labels: Optional[Dict[int, str]] = None) -> None:
        self.buf.append(local & 0x0F)
        for num, base in fields:
            labels = labels or {}
            self.buf += self._encode(base, values.get(num), labels.get(num, "字段%d" % num))

    def build(self, profile_version: int = 2140) -> bytes:
        data_bytes = bytes(self.buf)
        header = struct.pack("<BBHI4s", 14, 0x20, profile_version, len(data_bytes), b".FIT")
        header += struct.pack("<H", fit_crc(header))     # 头部 CRC：仅覆盖前 12 字节
        body = header + data_bytes
        return body + struct.pack("<H", fit_crc(body))   # 文件 CRC：覆盖头部+数据区


def write_fit(track: Track, derived: Derived, path: str) -> Tuple[bytes, Dict[str, Any]]:
    w = FitWriter()
    info: Dict[str, Any] = {"dropped_fields": [], "wrote": len(track.points)}
    pts = track.points

    # ---- file_id ----
    t0 = track.times()
    created = fit_ts(t0[0]) if t0 else None
    w.define(0, MESG_FILE_ID, [(0, 0x00), (1, 0x84), (2, 0x84), (4, 0x86)])
    w.data(0, [(0, 0x00), (1, 0x84), (2, 0x84), (4, 0x86)],
           {0: FILE_TYPE_ACTIVITY, 1: 1, 2: 0, 4: created})   # 厂商 1 = Garmin（通用标识）

    # ---- record：只声明数据里真正存在的字段 ----
    def has(name: str) -> bool:
        return any(getattr(p, name) is not None for p in pts)

    rec_fields: List[Tuple[int, int]] = []
    if has("time"):
        rec_fields.append((253, 0x86))
    if has("lat"):
        rec_fields.append((0, 0x85))
    if has("lon"):
        rec_fields.append((1, 0x85))
    if has("ele"):
        rec_fields.append((2, 0x84))
    if has("hr"):
        rec_fields.append((3, 0x02))
    if has("cad"):
        rec_fields.append((4, 0x02))
    if derived.dist_source:
        rec_fields.append((5, 0x86))
    if derived.speed_source != "无":
        rec_fields.append((6, 0x84))
    if has("power"):
        rec_fields.append((7, 0x84))
    if has("temp"):
        rec_fields.append((13, 0x01))
        if any(p.temp is not None and abs(p.temp - float(int(p.temp))) > 1e-9 for p in pts):
            info["dropped_fields"].append(
                "温度的小数精度（FIT 的 temperature 字段是整度，已四舍五入）")
    if not rec_fields:
        raise TrackError("没有任何可写入 FIT 的字段（源数据为空）")

    w.define(1, MESG_RECORD, rec_fields)
    field_nums = {f[0] for f in rec_fields}
    for i, p in enumerate(pts):
        vals: Dict[int, Any] = {}
        if 253 in field_nums:
            vals[253] = fit_ts(p.time) if p.time is not None else None
        if p.lat is not None:
            vals[0] = p.lat / SEMI
        if p.lon is not None:
            vals[1] = p.lon / SEMI
        if p.ele is not None:
            vals[2] = (p.ele + 500.0) * 5.0
        if p.hr is not None:
            vals[3] = p.hr
        if p.cad is not None:
            vals[4] = p.cad
        if derived.cum[i] is not None:
            vals[5] = derived.cum[i] * 100.0
        sp = derived.speed[i]
        if sp is not None:
            vals[6] = sp * 1000.0
        if p.power is not None:
            vals[7] = p.power
        if p.temp is not None:
            vals[13] = p.temp
        labels = {0: "纬度", 1: "经度", 2: "海拔", 5: "累计距离", 6: "速度"}
        w.data(1, rec_fields, vals, labels)

    # ---- 汇总统计（lap / session 共用）----
    st = basic_stats(track, derived)
    mins = [p for p in pts if p.time is not None]
    start_ts = fit_ts(mins[0].time) if mins else None
    end_ts = fit_ts(mins[-1].time) if mins else None
    elapsed = st["elapsed"] or 0.0
    timer = st["moving"] if st["moving"] else elapsed
    total_dist = st["distance"] or 0.0
    sport = SPORT_TO_FIT.get(track.sport, 0)

    def ms(v: Optional[float]) -> Optional[int]:            # m/s → mm/s
        return None if v is None else int(round(v * 1000.0))

    lap_fields: List[Tuple[int, int]] = [
        (253, 0x86), (0, 0x00), (1, 0x00), (2, 0x86),
        (3, 0x85), (4, 0x85), (5, 0x85), (6, 0x85),
        (7, 0x86), (8, 0x86), (9, 0x86), (11, 0x84),
        (13, 0x84), (14, 0x84), (15, 0x02), (16, 0x02),
        (17, 0x02), (18, 0x02), (19, 0x84), (20, 0x84),
        (21, 0x84), (22, 0x84), (25, 0x00),
    ]
    lap_vals = {
        253: end_ts, 0: EVENT_LAP, 1: EVENT_TYPE_STOP, 2: start_ts,
        3: (mins[0].lat / SEMI) if (mins and mins[0].lat is not None) else None,
        4: (mins[0].lon / SEMI) if (mins and mins[0].lon is not None) else None,
        5: (mins[-1].lat / SEMI) if (mins and mins[-1].lat is not None) else None,
        6: (mins[-1].lon / SEMI) if (mins and mins[-1].lon is not None) else None,
        7: int(round(elapsed * 1000.0)), 8: int(round(timer * 1000.0)),
        9: int(round(total_dist * 100.0)), 11: 0,
        13: ms(st["avg_speed"]), 14: ms(st["max_speed"]),
        15: st["hr_avg"], 16: st["hr_max"], 17: st["cad_avg"], 18: st["cad_max"],
        19: st["pwr_avg"], 20: st["pwr_max"],
        21: st["ascent"], 22: st["descent"], 25: sport,
    }
    w.define(2, MESG_LAP, lap_fields)
    w.data(2, lap_fields, lap_vals,
           {2: "分段起始时间", 9: "总距离", 7: "总耗时"})

    ses_fields: List[Tuple[int, int]] = [
        (253, 0x86), (0, 0x00), (1, 0x00), (2, 0x86),
        (3, 0x85), (4, 0x85), (5, 0x00), (6, 0x00),
        (7, 0x86), (8, 0x86), (9, 0x86), (11, 0x84),
        (14, 0x84), (15, 0x84), (16, 0x02), (17, 0x02),
        (18, 0x02), (19, 0x02), (20, 0x84), (21, 0x84),
        (22, 0x84), (23, 0x84), (25, 0x84), (26, 0x84), (28, 0x00),
        (49, 0x84), (50, 0x84), (57, 0x01), (58, 0x01),
    ]
    ses_vals = {
        253: end_ts, 0: EVENT_SESSION, 1: EVENT_TYPE_STOP, 2: start_ts,
        3: lap_vals[3], 4: lap_vals[4], 5: sport, 6: 0,
        7: int(round(elapsed * 1000.0)), 8: int(round(timer * 1000.0)),
        9: int(round(total_dist * 100.0)), 11: 0,
        14: ms(st["avg_speed"]), 15: ms(st["max_speed"]),
        16: st["hr_avg"], 17: st["hr_max"], 18: st["cad_avg"], 19: st["cad_max"],
        20: st["pwr_avg"], 21: st["pwr_max"],
        22: st["ascent"], 23: st["descent"],
        25: 0, 26: 1, 28: 0,                       # first_lap_index / num_laps / trigger
        49: (st["ele_avg"] + 500.0) * 5.0 if st["ele_avg"] is not None else None,
        50: (st["ele_max"] + 500.0) * 5.0 if st["ele_max"] is not None else None,
        57: st["temp_avg"], 58: st["temp_max"],
    }
    w.define(3, MESG_SESSION, ses_fields)
    w.data(3, ses_fields, ses_vals, {9: "总距离", 7: "总耗时", 49: "平均海拔"})

    act_fields: List[Tuple[int, int]] = [
        (253, 0x86), (0, 0x86), (1, 0x84), (2, 0x00), (3, 0x00), (4, 0x00), (5, 0x86),
    ]
    local_ts = None
    if track.tz_offset is not None and end_ts is not None:
        local_ts = end_ts + track.tz_offset
    act_vals = {
        253: end_ts,
        0: int(round(elapsed * 1000.0)),
        1: 1, 2: ACTIVITY_TYPE_MANUAL, 3: EVENT_ACTIVITY, 4: EVENT_TYPE_STOP,
        5: local_ts,
    }
    if local_ts is None:
        info["dropped_fields"].append("local_timestamp（源文件未声明录制时区，无法写入本地时间）")
    w.define(4, MESG_ACTIVITY, act_fields)
    w.data(4, act_fields, act_vals, {0: "总耗时"})

    info["warnings"] = list(w.warnings)
    return w.build(), info


# ============================================================================
#  统计
# ============================================================================
def basic_stats(track: Track, derived: Derived) -> Dict[str, Any]:
    pts = track.points
    st: Dict[str, Any] = {"n": len(pts)}
    st["n_pos"] = sum(1 for p in pts if p.lat is not None and p.lon is not None)
    st["n_time"] = sum(1 for p in pts if p.time is not None)
    st["n_ele"] = sum(1 for p in pts if p.ele is not None)
    st["n_hr"] = sum(1 for p in pts if p.hr is not None)
    st["n_cad"] = sum(1 for p in pts if p.cad is not None)
    st["n_pwr"] = sum(1 for p in pts if p.power is not None)
    st["n_temp"] = sum(1 for p in pts if p.temp is not None)

    times = track.times()
    st["t_first"] = times[0] if times else None
    st["t_last"] = times[-1] if times else None
    st["elapsed"] = ((st["t_last"] - st["t_first"]).total_seconds()
                     if st["t_first"] and st["t_last"] else None)
    st["distance"] = derived.cum[-1] if derived.cum else None
    # 移动时长：把相邻点间隔 > 60 秒的部分视为暂停/中断，不计入
    moving = 0.0
    for i in range(1, len(pts)):
        a, b = pts[i - 1].time, pts[i].time
        if a is not None and b is not None:
            dts = (b - a).total_seconds()
            if 0.0 < dts <= 60.0:
                moving += dts
    st["moving"] = moving if times else None
    speeds = [v for v in derived.speed if v is not None]
    st["speed_avg_src"] = (sum(speeds) / float(len(speeds))) if speeds else None
    st["max_speed"] = max(speeds) if speeds else None
    base = st["moving"] if st["moving"] else st["elapsed"]
    if base and base > 0 and st["distance"] is not None:
        st["avg_speed"] = st["distance"] / base
        st["avg_speed_base"] = "移动时长" if st["moving"] else "总时长"
    else:
        st["avg_speed"] = st["speed_avg_src"]
        st["avg_speed_base"] = "各点速度均值"

    eles = [p.ele for p in pts if p.ele is not None]
    if eles:
        st["ele_min"], st["ele_max"] = min(eles), max(eles)
        st["ele_avg"] = sum(eles) / float(len(eles))
    else:
        st["ele_min"] = st["ele_max"] = st["ele_avg"] = None
    asc = desc = 0.0
    prev_ele = None
    for p in pts:
        if p.ele is None:
            continue
        if prev_ele is not None:
            d = p.ele - prev_ele
            if d > 0:
                asc += d
            else:
                desc += -d
        prev_ele = p.ele
    st["ascent"] = int(round(asc)) if eles else None
    st["descent"] = int(round(desc)) if eles else None

    def agg(vals: Sequence[Optional[float]]) -> Tuple[Optional[int], Optional[int], Optional[float]]:
        v = [x for x in vals if x is not None]
        if not v:
            return None, None, None
        return (int(round(sum(v) / float(len(v)))), max(int(round(x)) for x in v),
                sum(v) / float(len(v)))

    st["hr_avg"], st["hr_max"], _ = agg([p.hr for p in pts])
    st["cad_avg"], st["cad_max"], _ = agg([p.cad for p in pts])
    st["pwr_avg"], st["pwr_max"], _ = agg([p.power for p in pts])
    temps = [p.temp for p in pts if p.temp is not None]
    if temps:
        st["temp_min"], st["temp_max"] = min(temps), max(temps)
        st["temp_avg"] = sum(temps) / float(len(temps))
    else:
        st["temp_min"] = st["temp_max"] = st["temp_avg"] = None
    return st


# ============================================================================
#  转换主流程
# ============================================================================
def unique_out_path(src: str, target: str) -> str:
    folder = os.path.dirname(os.path.abspath(src))
    stem = os.path.splitext(os.path.basename(src))[0]
    cand = os.path.join(folder, stem + EXT_OF[target])
    if not os.path.exists(cand):
        return cand
    n = 2
    while True:
        cand = os.path.join(folder, "%s_R%d%s" % (stem, n, EXT_OF[target]))
        if not os.path.exists(cand):
            return cand
        n += 1


def atomic_write(path: str, data: bytes, perm_src: Optional[str] = None) -> None:
    folder = os.path.dirname(os.path.abspath(path)) or "."
    fd, tmp = tempfile.mkstemp(dir=folder, prefix=".tc_", suffix=".tmp")
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(data)
        if perm_src and os.path.exists(perm_src):
            try:
                os.chmod(tmp, os.stat(perm_src).st_mode & 0o777)
            except OSError:
                pass
        os.replace(tmp, path)
    except Exception:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


def convert_file(src_path: str, target: str, mode: str,
                 log: Callable[[str], None]) -> Dict[str, Any]:
    """执行一次转换，返回结构化结果。log 用于输出过程信息。"""
    t_start = time.time()
    result: Dict[str, Any] = {}
    src_size = os.path.getsize(src_path)

    # ---------- 1. 读取 ----------
    log("[1/5] 读取源文件：%s" % src_path)
    log("      文件大小：%s" % fmt_size(src_size))
    src_fmt = guess_format(src_path)
    if src_fmt is None:
        raise TrackError("无法识别文件格式（按扩展名与内容都不是 GPX/TCX/FIT）")
    log("      格式识别：%s" % FORMAT_LABEL[src_fmt].upper())
    track = read_track(src_path, mode)
    if target == src_fmt:
        raise TrackError("目标格式与源格式相同（都是 %s），请选择其它格式" % FORMAT_LABEL[target])
    log("      解析结果：%d 个轨迹点" % len(track.points))
    result["src_format"] = src_fmt

    # ---------- 2. 摘要 ----------
    derived = derive(track.points)
    st = basic_stats(track, derived)
    log("[2/5] 轨迹内容")
    log("      版本/来源：%s%s" % (track.src_version,
                                ("（%s）" % track.meta["creator"]) if track.meta.get("creator") else ""))
    log("      运动类型：%s" % track.sport)
    if st["t_first"]:
        log("      时间范围：%s ~ %s" % (fmt_utc(st["t_first"]), fmt_utc(st["t_last"])))
        log("      本地时间(UTC+8)：%s ~ %s"
            % (fmt_local(st["t_first"]), fmt_local(st["t_last"])))
        log("      总时长：%s" % fmt_dur(st["elapsed"]))
        if st["moving"] and st["elapsed"] and st["elapsed"] - st["moving"] > 1.0:
            log("      移动时长：%s（已排除 %d 处 >60 秒的间断）"
                % (fmt_dur(st["moving"]), derived.gaps))
    if st["distance"] is not None:
        log("      总距离：%.2f km（%s）" % (st["distance"] / 1000.0, derived.dist_source))
    log("      数据完整度：坐标 %d / 时间 %d / 海拔 %d / 心率 %d / 步频 %d / 功率 %d / 温度 %d"
        % (st["n_pos"], st["n_time"], st["n_ele"], st["n_hr"], st["n_cad"],
           st["n_pwr"], st["n_temp"]))
    for note in track.notes:
        log("      提示：%s" % note)
    if derived.non_monotonic and derived.dist_source == "计算":
        log("      提示：源文件的累计距离不是单调递增，已改用按坐标计算的累计距离")
    if derived.gaps:
        log("      提示：检测到 %d 处时间断点（相邻点间隔 > 60 秒）" % derived.gaps)
    log("[3/5] 时间口径：%s" % MODE_LABEL[mode])
    if track.tz_offset is not None:
        log("      源文件声明时区：UTC%+d:%02d" % (track.tz_offset // 3600,
                                                 abs(track.tz_offset % 3600) // 60))
    else:
        log("      源文件未声明时区：一律按 UTC 处理（可用「伪 Z 修正」重新转换）")
    if st["t_first"]:
        delta = dt.timedelta(hours=8)
        alt_first = st["t_first"] - delta if mode == MODE_DECLARED else st["t_first"] + delta
        alt_last = st["t_last"] - delta if mode == MODE_DECLARED else st["t_last"] + delta
        if mode == MODE_DECLARED:
            log("      口径核对：若该文件实为「伪 Z」导出，真实 UTC 应为 %s ~ %s（北京 %s ~ %s）"
                % (fmt_utc(alt_first), fmt_utc(alt_last),
                   fmt_local(alt_first)[11:], fmt_local(alt_last)[11:]))
        else:
            log("      口径核对：若该文件本就是真 UTC，则应为 %s ~ %s（北京 %s ~ %s）"
                % (fmt_utc(alt_first), fmt_utc(alt_last),
                   fmt_local(alt_first)[11:], fmt_local(alt_last)[11:]))

    # ---------- 3. 写出 ----------
    out_path = unique_out_path(src_path, target)
    writer = {"gpx": write_gpx, "tcx": write_tcx, "fit": write_fit}[target]
    data, winfo = writer(track, derived, out_path)
    t_write = time.time()
    log("[4/5] 写出 %s：%s" % (FORMAT_LABEL[target].upper(), out_path))
    if winfo.get("dropped_no_time"):
        log("      丢弃 %d 个无时间戳的点（%s 要求每个点必须有时间）"
            % (winfo["dropped_no_time"], FORMAT_LABEL[target].upper()))
    if winfo.get("dropped_no_pos"):
        log("      丢弃 %d 个无坐标的点（%s 的轨迹点必须有经纬度）"
            % (winfo["dropped_no_pos"], FORMAT_LABEL[target].upper()))
    for f in winfo.get("dropped_fields", []):
        log("      字段丢弃：%s" % f)
    for wmsg in winfo.get("warnings", []):
        log("      警告：%s" % wmsg)
    atomic_write(out_path, data, src_path)
    out_size = os.path.getsize(out_path)
    log("      写入 %d 个点，%s，用时 %.2f s" % (winfo.get("wrote", 0),
                                              fmt_size(out_size), time.time() - t_write))

    # ---------- 4. 回读自校验 ----------
    log("[5/5] 回读校验（确认输出文件可被再次解析）")
    verify = "跳过"
    try:
        back = read_track(out_path, MODE_DECLARED)
        n_back = len(back.points)
        b_first = back.times()[0] if back.times() else None
        b_last = back.times()[-1] if back.times() else None
        same_n = n_back == winfo.get("wrote")
        fwd_times = [p.time for p in track.points if p.time is not None]
        exp_first = fwd_times[0] if fwd_times else None
        exp_last = fwd_times[-1] if fwd_times else None
        if back.src_format == "fit":
            exp_first = fwd_times[0] if fwd_times else None
        time_ok = (b_first == exp_first and b_last == exp_last) or (target != "fit" and exp_first is None)
        if same_n and time_ok:
            verify = "通过"
            log("      [OK] 回读 %d 个点，与写入数量一致，首末时间一致" % n_back)
        else:
            verify = "不一致"
            log("      [!] 回读 %d 个点（写入 %d），首末时间 %s / %s"
                % (n_back, winfo.get("wrote"), fmt_utc(b_first), fmt_utc(b_last)))
    except Exception as exc:
        verify = "失败"
        log("      [!] 输出文件回读失败：%s" % exc)
        log(traceback.format_exc())

    result.update({
        "out_path": out_path,
        "out_size": out_size,
        "verify": verify,
        "written": winfo.get("wrote", 0),
        "derived": derived,
        "stats": st,
        "track": track,
        "winfo": winfo,
        "elapsed_wall": time.time() - t_start,
    })

    report = format_report(src_path, src_size, out_path, out_size, track, st, derived,
                           winfo, verify, target)
    for line in report:
        log(line)
    return result


def format_report(src_path: str, src_size: int, out_path: str, out_size: int,
                  track: Track, st: Dict[str, Any], derived: Derived,
                  winfo: Dict[str, Any], verify: str, target: str) -> List[str]:
    """生成「处理后的汇总信息」文本块。"""
    L: List[str] = []
    L.append("-" * 72)
    L.append("处理汇总")
    L.append("-" * 72)

    def row(label: str, value: str) -> None:
        L.append("  %s: %s" % (ljust_disp(label, 18), value))

    row("源文件", "%s（%s，%s）" % (os.path.basename(src_path),
                                  FORMAT_LABEL[track.src_format].upper(), fmt_size(src_size)))
    row("输出文件", "%s（%s，%s）" % (os.path.basename(out_path),
                                    FORMAT_LABEL[target].upper(), fmt_size(out_size)))
    row("来源版本", track.src_version)
    if track.meta.get("creator"):
        row("源创建程序", str(track.meta["creator"]))
    row("运动类型", track.sport)
    n_src = len(track.points)
    if winfo.get("wrote") is not None and winfo["wrote"] != n_src:
        row("轨迹点数", "%d 个 → 写入 %d 个（丢弃 %d）"
            % (n_src, winfo["wrote"], n_src - winfo["wrote"]))
    else:
        row("轨迹点数", "%d 个（全部写入）" % n_src)
    if st["t_first"]:
        L.append("")
        row("时间范围(UTC)", "%s ~ %s" % (fmt_utc(st["t_first"]), fmt_utc(st["t_last"])))
        row("时间范围(北京)", "%s ~ %s" % (fmt_local(st["t_first"]), fmt_local(st["t_last"])))
        row("总时长", fmt_dur(st["elapsed"]))
        if st["moving"] and st["elapsed"] and st["elapsed"] - st["moving"] > 1.0:
            row("移动时长", "%s（排除 %d 处 >60 秒的间断）"
                % (fmt_dur(st["moving"]), derived.gaps))
    if st["distance"] is not None:
        row("总距离", "%.3f km（%s）" % (st["distance"] / 1000.0, derived.dist_source))
    if st["avg_speed"] is not None:
        row("平均速度", "%.2f km/h（按%s）" % (st["avg_speed"] * 3.6,
                                             st.get("avg_speed_base", "总时长")))
    if st["max_speed"] is not None:
        row("最高速度", "%.2f km/h（%s）" % (st["max_speed"] * 3.6, derived.speed_source))
    if st["ele_min"] is not None:
        row("海拔", "%.1f ~ %.1f m，平均 %.1f m" % (st["ele_min"], st["ele_max"], st["ele_avg"]))
        row("累计爬升/下降", "%s m / %s m" % (st["ascent"], st["descent"]))
    if st["hr_avg"] is not None:
        row("心率", "平均 %d / 最高 %d bpm（%d 个点）" % (st["hr_avg"], st["hr_max"], st["n_hr"]))
    if st["cad_avg"] is not None:
        row("步频/踏频", "平均 %d / 最高 %d（%d 个点）" % (st["cad_avg"], st["cad_max"], st["n_cad"]))
    if st["pwr_avg"] is not None:
        row("功率", "平均 %d / 最高 %d W（%d 个点）" % (st["pwr_avg"], st["pwr_max"], st["n_pwr"]))
    if st["temp_min"] is not None:
        row("温度", "%.1f ~ %.1f ℃（%d 个点）" % (st["temp_min"], st["temp_max"], st["n_temp"]))
    L.append("")
    row("数据完整度", "坐标 %d / 时间 %d / 海拔 %d / 心率 %d / 步频 %d / 功率 %d / 温度 %d"
        % (st["n_pos"], st["n_time"], st["n_ele"], st["n_hr"], st["n_cad"], st["n_pwr"], st["n_temp"]))
    if derived.gaps:
        row("时间断点", "%d 处（相邻点间隔 > 60 秒）" % derived.gaps)
    dropped = winfo.get("dropped_fields", [])
    if dropped:
        row("字段丢弃", "；".join(dropped))
    row("输出自校验", verify)
    L.append("-" * 72)
    return L


# ============================================================================
#  图形界面（ttk + clam）
# ============================================================================
UI_FONT_CANDIDATES = (
    "PingFang SC", "Microsoft YaHei UI", "Microsoft YaHei", "Hiragino Sans GB",
    "Noto Sans CJK SC", "Source Han Sans SC", "WenQuanYi Micro Hei", "Heiti SC",
    "SimHei", "Arial Unicode MS",
)
MONO_FONT_CANDIDATES = (
    "Menlo", "SF Mono", "Consolas", "DejaVu Sans Mono", "Monaco", "Courier New",
)

TARGET_CHOICES = ["GPX (.gpx)", "TCX (.tcx)", "FIT (.fit)"]
TARGET_BY_CHOICE = {"GPX (.gpx)": "gpx", "TCX (.tcx)": "tcx", "FIT (.fit)": "fit"}
CHOICE_BY_TARGET = {v: k for k, v in TARGET_BY_CHOICE.items()}


def pick_font(root: tk.Misc, candidates: Sequence[str], fallback: str) -> str:
    try:
        import tkinter.font as tkfont
        families = set(tkfont.families(root))
    except Exception:
        return fallback
    for name in candidates:
        if name in families:
            return name
    return fallback


class TrackConverterApp:
    """主窗口。"""

    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.log_q: "queue.Queue[Tuple[str, Any]]" = queue.Queue()
        self.busy = False
        self.var_input = tk.StringVar()
        self.var_target = tk.StringVar(value=TARGET_CHOICES[1])
        self.var_mode = tk.StringVar(value=MODE_LABEL[MODE_DECLARED])
        self.var_out = tk.StringVar(value="（自动）与原文件同目录，扩展名改为目标格式")
        self.var_status = tk.StringVar(value="就绪")

        root.title("%s  v%s" % (APP_NAME, APP_VER))
        root.geometry("900x660")
        root.minsize(780, 540)

        style = ttk.Style(root)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        base_font = pick_font(root, UI_FONT_CANDIDATES, "TkDefaultFont")
        mono_font = pick_font(root, MONO_FONT_CANDIDATES, "TkFixedFont")
        self.font_ui = (base_font, 12)
        self.font_ui_bold = (base_font, 12, "bold")
        self.font_mono = (mono_font, 11)
        for pattern in ("TLabel", "TButton", "TEntry", "TCombobox",
                        "TLabelframe.Label", "TCheckbutton", "TRadiobutton"):
            style.configure(pattern, font=self.font_ui)
        style.configure("Title.TLabel", font=(base_font, 15, "bold"))
        style.configure("Hint.TLabel", foreground="#5A5A5A")
        style.configure("Submit.TButton", font=(base_font, 12, "bold"))

        outer = ttk.Frame(root, padding=12)
        outer.pack(fill="both", expand=True)

        # ---------- 标题 ----------
        head = ttk.Frame(outer)
        head.pack(fill="x", pady=(0, 8))
        ttk.Label(head, text="运动轨迹格式互转（GPX / TCX / FIT）",
                  style="Title.TLabel").pack(anchor="w")
        ttk.Label(head, text="处理过程与汇总信息会同步输出到命令行窗口；纯标准库实现，无需安装第三方包。",
                  style="Hint.TLabel").pack(anchor="w", pady=(2, 0))

        # ---------- 文件与选项 ----------
        box = ttk.LabelFrame(outer, text="文件与选项", padding=10)
        box.pack(fill="x")
        box.columnconfigure(1, weight=1)

        ttk.Label(box, text="轨迹文件").grid(row=0, column=0, sticky="w", pady=5, padx=(0, 8))
        self.entry_in = ttk.Entry(box, textvariable=self.var_input)
        self.entry_in.grid(row=0, column=1, sticky="ew", pady=5)
        self.btn_pick = ttk.Button(box, text="选择文件", command=self.on_pick)
        self.btn_pick.grid(row=0, column=2, sticky="e", padx=(8, 0), pady=5)

        ttk.Label(box, text="目标格式").grid(row=1, column=0, sticky="w", pady=5, padx=(0, 8))
        self.cmb_target = ttk.Combobox(box, textvariable=self.var_target,
                                       values=TARGET_CHOICES, state="readonly", width=18)
        self.cmb_target.grid(row=1, column=1, sticky="w", pady=5)
        self.cmb_target.bind("<<ComboboxSelected>>", lambda e: self.refresh_out())

        ttk.Label(box, text="时间口径").grid(row=2, column=0, sticky="w", pady=5, padx=(0, 8))
        self.cmb_mode = ttk.Combobox(box, textvariable=self.var_mode,
                                     values=list(MODE_LABEL.values()),
                                     state="readonly", width=34)
        self.cmb_mode.grid(row=2, column=1, sticky="w", pady=5)

        ttk.Label(box, text="输出文件").grid(row=3, column=0, sticky="w", pady=5, padx=(0, 8))
        ttk.Label(box, textvariable=self.var_out, style="Hint.TLabel",
                  wraplength=640, justify="left").grid(row=3, column=1, columnspan=2,
                                                       sticky="w", pady=5)

        # ---------- 按钮 ----------
        bar = ttk.Frame(outer)
        bar.pack(fill="x", pady=(12, 8))
        self.btn_submit = ttk.Button(bar, text="开始转换", style="Submit.TButton",
                                     command=self.on_submit)
        self.btn_submit.pack(side="left", ipadx=18, ipady=4)
        self.btn_exit = ttk.Button(bar, text="退出", command=self.on_exit)
        self.btn_exit.pack(side="right", ipadx=18, ipady=4)
        self.btn_clear = ttk.Button(bar, text="清空日志", command=self.clear_log)
        self.btn_clear.pack(side="right", ipadx=10, ipady=4, padx=(0, 10))

        # ---------- 日志区 ----------
        logbox = ttk.LabelFrame(outer, text="处理日志", padding=6)
        logbox.pack(fill="both", expand=True)
        self.txt = tk.Text(logbox, height=18, wrap="none", font=self.font_mono,
                           background="#FFFFFF", foreground="#1A1A1A",
                           insertbackground="#1A1A1A", relief="flat", state="disabled")
        vsb = ttk.Scrollbar(logbox, orient="vertical", command=self.txt.yview)
        hsb = ttk.Scrollbar(logbox, orient="horizontal", command=self.txt.xview)
        self.txt.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        self.txt.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")
        logbox.rowconfigure(0, weight=1)
        logbox.columnconfigure(0, weight=1)

        # ---------- 状态栏 ----------
        ttk.Label(outer, textvariable=self.var_status, anchor="w",
                  style="Hint.TLabel").pack(fill="x", pady=(6, 0))

        root.protocol("WM_DELETE_WINDOW", self.on_exit)
        self.root.after(80, self._pump)
        self.log("=" * 72)
        self.log(" %s v%s" % (APP_NAME, APP_VER))
        self.log(" 支持 GPX / TCX / FIT 三种格式任意互转")
        self.log(" 使用步骤：① 选择文件 ② 选目标格式 ③ 开始转换")
        self.log("=" * 72)

    # ---------------- 日志 ----------------
    def log(self, msg: str) -> None:
        """线程安全：命令行直接打印，界面通过队列镜像。"""
        try:
            print(msg, flush=True)
        except (UnicodeEncodeError, OSError):
            try:
                print(str(msg).encode("utf-8", "replace").decode("ascii", "replace"),
                      flush=True)
            except Exception:
                pass
        self.log_q.put(("log", msg))

    def _append(self, msg: str) -> None:
        self.txt.configure(state="normal")
        self.txt.insert("end", str(msg) + "\n")
        self.txt.see("end")
        self.txt.configure(state="disabled")

    def clear_log(self) -> None:
        self.txt.configure(state="normal")
        self.txt.delete("1.0", "end")
        self.txt.configure(state="disabled")

    def _pump(self) -> None:
        try:
            while True:
                kind, payload = self.log_q.get_nowait()
                if kind == "log":
                    self._append(payload)
                elif kind == "status":
                    self.var_status.set(payload)
                elif kind == "done":
                    self._on_done(*payload)
        except queue.Empty:
            pass
        except Exception:
            traceback.print_exc()
        finally:
            self.root.after(80, self._pump)

    # ---------------- 交互 ----------------
    def refresh_out(self) -> None:
        src = self.var_input.get().strip()
        if not src:
            self.var_out.set("（自动）与原文件同目录，扩展名改为目标格式")
            return
        target = TARGET_BY_CHOICE.get(self.var_target.get(), "tcx")
        try:
            self.var_out.set(unique_out_path(src, target))
        except Exception:
            self.var_out.set("（自动）与原文件同目录")

    def on_pick(self) -> None:
        if self.busy:
            return
        path = filedialog.askopenfilename(
            title="选择一个轨迹文件",
            filetypes=[("轨迹文件", "*.gpx *.tcx *.fit"),
                       ("GPX 轨迹", "*.gpx"), ("TCX 轨迹", "*.tcx"),
                       ("FIT 轨迹", "*.fit"), ("全部文件", "*.*")],
        )
        if not path:
            return
        self.var_input.set(path)
        fmt = guess_format(path)
        if fmt:
            for choice in TARGET_CHOICES:
                if TARGET_BY_CHOICE[choice] != fmt:
                    self.var_target.set(choice)
                    break
        self.refresh_out()
        self.log("已选择文件：%s" % path)
        self.var_status.set("已选择文件，点击「开始转换」")

    def on_submit(self) -> None:
        if self.busy:
            return
        src = self.var_input.get().strip()
        if not src:
            messagebox.showwarning(APP_NAME, "请先点击「选择文件」选一个轨迹文件。")
            return
        if not os.path.isfile(src):
            messagebox.showerror(APP_NAME, "文件不存在：\n%s" % src)
            return
        target = TARGET_BY_CHOICE.get(self.var_target.get(), "tcx")
        src_fmt = guess_format(src)
        if src_fmt == target:
            messagebox.showwarning(APP_NAME, "目标格式与源格式相同（都是 %s）。\n请选择其它目标格式。"
                                   % FORMAT_LABEL[target].upper())
            return
        mode = MODE_BY_LABEL.get(self.var_mode.get(), MODE_DECLARED)

        self.busy = True
        self.btn_submit.configure(state="disabled")
        self.btn_pick.configure(state="disabled")
        self.var_status.set("正在处理…")
        self.log("")
        self.log("=" * 72)
        self.log(" 开始转换  %s → %s   %s"
                 % (FORMAT_LABEL.get(src_fmt, "?").upper(), FORMAT_LABEL[target].upper(),
                    dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
        self.log("=" * 72)
        threading.Thread(target=self._worker, args=(src, target, mode), daemon=True).start()

    def _worker(self, src: str, target: str, mode: str) -> None:
        try:
            res = convert_file(src, target, mode, self.log)
            self.log_q.put(("done", ("ok", res, None)))
        except TrackError as exc:
            self.log("转换中止：%s" % exc)
            self.log_q.put(("done", ("err", None, str(exc))))
        except Exception as exc:
            self.log("意外错误：")
            self.log(traceback.format_exc())
            self.log_q.put(("done", ("err", None, "%s: %s" % (type(exc).__name__, exc))))

    def _on_done(self, status: str, res: Optional[Dict[str, Any]], err: Optional[str]) -> None:
        self.busy = False
        self.btn_submit.configure(state="normal")
        self.btn_pick.configure(state="normal")
        if status == "ok" and res:
            self.var_status.set("完成：%s（%s）" % (os.path.basename(res["out_path"]),
                                                 res["out_size"] and fmt_size(res["out_size"])))
            self.refresh_out()
            st = res["stats"]
            summary = ["转换完成 ✓", "",
                       "输出：%s" % res["out_path"],
                       "点数：%d" % res.get("written", 0)]
            if st.get("distance") is not None:
                summary.append("距离：%.2f km" % (st["distance"] / 1000.0))
            if st.get("elapsed"):
                summary.append("时长：%s" % fmt_dur(st["elapsed"]))
            if st.get("t_first"):
                summary.append("时间：%s" % fmt_local(st["t_first"]))
            messagebox.showinfo(APP_NAME, "\n".join(summary))
        else:
            self.var_status.set("失败：%s" % (err or "未知错误"))
            messagebox.showerror(APP_NAME, "转换失败：\n%s" % (err or "未知错误"))

    def on_exit(self) -> None:
        if self.busy and not messagebox.askyesno(APP_NAME, "正在处理中，确定要退出吗？"):
            return
        self.root.destroy()


# ============================================================================
#  入口
# ============================================================================
def setup_console() -> None:
    """Windows 控制台切到 UTF-8，避免中文输出乱码/报错。"""
    if os.name != "nt":
        return
    try:
        import ctypes
        ctypes.windll.kernel32.SetConsoleOutputCP(65001)
    except Exception:
        pass
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")   # type: ignore[attr-defined]
        except Exception:
            pass


USAGE = """用法:
  python3 track_converter.py                      # 打开图形界面
  python3 track_converter.py <文件> <目标格式>     # 命令行直接转换
     目标格式: gpx | tcx | fit
     附加开关: --fake-z   按「伪 Z 修正」口径解释时间（墙钟按 UTC+8）
示例:
  python3 track_converter.py ride.gpx fit
  python3 track_converter.py ride.fit tcx --fake-z
"""


def run_cli(argv: Sequence[str]) -> int:
    args = [a for a in argv if not a.startswith("--")]
    mode = MODE_FAKE_Z if "--fake-z" in argv else MODE_DECLARED
    if len(args) < 2:
        print(USAGE)
        return 2
    src, target = args[0], args[1].lower().lstrip(".")
    if target not in FORMAT_LABEL:
        print("目标格式只能是 gpx / tcx / fit")
        print(USAGE)
        return 2
    if not os.path.isfile(src):
        print("文件不存在：%s" % src)
        return 1
    print("=" * 72)
    print(" %s v%s  命令行模式" % (APP_NAME, APP_VER))
    print("=" * 72)
    try:
        convert_file(src, target, mode, lambda m: print(m, flush=True))
    except TrackError as exc:
        print("转换中止：%s" % exc)
        return 1
    except Exception:
        print(traceback.format_exc())
        return 1
    return 0


def main() -> int:
    setup_console()
    argv = sys.argv[1:]
    if len(argv) >= 2:
        return run_cli(argv)
    if not TK_AVAILABLE:
        print("当前 Python 没有可用的 tkinter（%s），无法打开界面。" % TK_ERROR)
        print("可以改用命令行模式：")
        print(USAGE)
        return 1
    try:
        root = tk.Tk()
    except tk.TclError as exc:
        print("无法启动图形界面（%s），可改用命令行：" % exc)
        print(USAGE)
        return 1
    TrackConverterApp(root)
    root.mainloop()
    return 0


if __name__ == "__main__":
    sys.exit(main())