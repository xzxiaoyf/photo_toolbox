#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
GPX / TCX 轨迹插值补全工具 (v2)
================================================================
用途
----
小米健康等 App 导出的轨迹，在信号差、隧道、暂停等情况下会缺采样点，
相邻两点的时间间隔随之变大。本工具在「间隔超过阈值」的两点之间按
等时间线性插入补全点，让轨迹成为逐秒连续的序列。

**主要用途：按时间匹配照片，给照片写入 GPS 坐标。**

设计要点（相对原版）
--------------------
[P0-1] TCX 通路修复。原版 `ET.register_namespace('ns3', ...)` 必抛
       ValueError: Prefix format reserved for internal use
       → 任何 .tcx 文件点「提交」都只会弹错误框，功能是死的。
[P0-2] 改为「原位插入」。原版把 trkseg 的子元素全部删掉再按解析结果重建，
       任何解析失败的点都会连同 <ele>、扩展信息一起被静默删除，
       返回值还会把删除算成「共插入 -5 个点」。
[P0-3] 解析失败的点不再被跨过去插值。原版把点过滤后只剩可解析的点，
       于是会跨过被删掉的点伪造一条直线。
[P0-4] 海拔。小米 TCX 把 <AltitudeMeters> 嵌在 <Position> 内部
       （不符合 TCX schema），原版只找 <Trackpoint> 直接子元素
       → 海拔恒为 None → 打印明细时 TypeError 崩溃，且 (ele or 0)
       会凭空造出海拔 0 米与假下坡。现在两种写法都读，缺失就如实处理。
[P1-5] 时间真换算。原版 `strptime(..., '%z').replace(tzinfo=utc)` 把已解析
       出的真实偏移覆盖掉，08:00+08:00 被当成 08:00Z，会产生 8.5 小时的
       伪缺口（实测插入 28829 个点）。现在统一 astimezone(utc)。
[P1-6] 时间写法兼容。空格分隔、缺秒位、>6 位小数秒等合法写法原版全部
       解析失败。现在统一用一个正则覆盖。
[P1-7] 输出时间格式镜像源文件（毫秒位数、T/空格分隔），整份文件时间写法统一。
[P2-8] 最长插值间隔保护：超过阈值（默认 300 秒）的区间跳过并明确告警。
[P2-9] 保留 DOCTYPE / standalone / XML 注释 / 命名空间前缀 / 原有排版。
[P2-10] 输出重名自动加序号 xxx_C.gpx -> xxx_C2.gpx，不再静默覆盖。
[P2-11] 临时文件 + os.replace 原子写出。
[P2-12] 后台线程 + 进度 + 可取消 + 日志区；处理前预览确认；跨平台字体。

依赖
----
纯标准库，无需 pip 安装任何东西（原版需 lxml 的版本已去掉该依赖）。

用于照片匹配的注意事项
----------------------
1. **时间口径必须和照片那一端一致。** 本工具不改动任何已有时间戳，新点的时区
   写法会镜像源文件（源写 Z 就写 Z，源写 +08:00 就写 +08:00，源不带时区就
   不带）。所以：先用「小米轨迹时间修正工具」把 GPX 修成真正的 UTC，
   再插值；或者两张图都用同一个口径，别混。
2. **插值阈值决定匹配精度。** 照片只会匹配到最近的轨迹点，误差最大约为
   阈值的一半。阈值 20 秒 ≈ ±10 秒 ≈ 步行 ±14 米；要更准就调小（如 5 秒）。
3. **插值点是直线外推的估计值。** 只在「真实数据安静地缺了几十秒」时可信；
   超过「最长插值间隔」（默认 300 秒）的缺口会被跳过并告警，不伪造直线。

运行
----
    python3 gpx_track_interpolator_v2.py                 # 图形界面
    python3 gpx_track_interpolator_v2.py --preview F.gpx # 只分析，不写文件
    python3 gpx_track_interpolator_v2.py F.gpx           # 命令行处理
"""

import argparse
import os
import re
import sys
import tempfile
import threading
import queue
import traceback
import xml.etree.ElementTree as etree
from collections import Counter, OrderedDict
from datetime import datetime, timedelta, timezone

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from tkinter.scrolledtext import ScrolledText


# ══════════════════════════════════════════════════════════════
# 常量
# ══════════════════════════════════════════════════════════════

APP_TITLE = "GPX/TCX 轨迹插值补全工具"
APP_VERSION = "v2.2"

#: 界面统一背景色（灰色）。macOS 深色模式下 Tk 根窗口默认背景会发黑，
#: 而 ttk 组件是主题自带的浅灰，两者交界处就会露出黑色条带。
#: 把根窗口和所有 ttk 组件统一刷成同一个灰色即可消除色差。
UI_BG = "#d9d9d9"

GPX_NS_11 = "http://www.topografix.com/GPX/1/1"
GPX_NS_10 = "http://www.topografix.com/GPX/1/0"
TCX_NS = "http://www.garmin.com/xmlschemas/TrainingCenterDatabase/v2"

TZ_CN = timezone(timedelta(hours=8))          # 中国区 UTC+8

#: 每种格式的「轨迹点」标签名 / 「轨迹段」标签名
FMT_TAGS = {
    "gpx": {"point": "trkpt", "container": "trkseg"},
    "tcx": {"point": "Trackpoint", "container": "Track"},
}

#: 无时区时间的三种处理口径
NAIVE_RULES = OrderedDict([
    ("utc8", "按中国区 UTC+8 换算（小米口径）"),
    ("utc", "视为 UTC（只补 Z，不做换算）"),
    ("local", "按本机本地时区换算"),
])

DEFAULTS = {
    "gap_threshold": 20.0,   # 秒：间隔超过它才插值
    "interval": 1.0,         # 秒：插值后的时间步长
    "max_gap": 300.0,        # 秒：超过它就不插值，只告警（默认 5 分钟）
}

DEFAULT_OUT_SUFFIX = "_C"

TIME_RE = re.compile(
    r"^\s*"
    r"(?P<y>\d{4})-(?P<mo>\d{2})-(?P<d>\d{2})"
    r"[Tt ]+"
    r"(?P<h>\d{2}):(?P<mi>\d{2})"
    r"(?::(?P<s>\d{2})(?:[.,](?P<frac>\d+))?)?"
    r"\s*"
    r"(?P<tz>[Zz]|[+-]\d{2}(?::?\d{2})?)?"
    r"\s*$"
)

DECL_RE = re.compile(rb"<\?xml\s+([^?]*)\?>")
ATTR_RE = r"%s\s*=\s*['\"]([^'\"]*)['\"]"

#: 全文件扫描 xmlns 声明用（只认 ASCII 字节，不受文件编码影响）
NS_DECL_RE = re.compile(rb"xmlns(?::([A-Za-z_][\w.\-]*))?\s*=\s*[\"']([^\"']*)[\"']")
DOCTYPE_START_RE = re.compile(rb"<!DOCTYPE\b")


# ══════════════════════════════════════════════════════════════
# 命名空间 / DOCTYPE 保真
# ══════════════════════════════════════════════════════════════

def register_source_namespaces(path):
    """
    扫描整个文件的 xmlns 声明并注册到 ElementTree。

    标准库 ElementTree 不保留原文前缀，若目标命名空间未注册，输出会把
    所有元素改写成 ns0: 前缀。原版只读文件头 4096 字节，靠后的声明仍会
    退化成 ns0:；这里改成全文件扫描。
    """
    try:
        with open(path, "rb") as f:
            data = f.read()
    except OSError:
        return {}
    found = OrderedDict()
    for m in NS_DECL_RE.finditer(data):
        prefix = m.group(1).decode("ascii", "replace") if m.group(1) else ""
        uri = m.group(2).decode("utf-8", "replace")
        if not uri:
            continue
        found.setdefault(prefix, uri)
    for prefix, uri in found.items():
        if re.match(r"^ns\d+$", prefix):      # 该形式前缀被标准库保留，注册会抛错
            continue
        try:
            etree.register_namespace(prefix, uri)
        except (ValueError, TypeError):
            pass
    return found


def extract_doctype(path, limit=8192):
    """取出源文件的 DOCTYPE 声明（含内部子集），没有则返回 None。"""
    try:
        with open(path, "rb") as f:
            head = f.read(limit)
    except OSError:
        return None
    m = DOCTYPE_START_RE.search(head)
    if m is None:
        return None
    i, depth = m.end(), 0
    while i < len(head):
        ch = head[i:i + 1]
        if ch == b"[":
            depth += 1
        elif ch == b"]":
            depth -= 1
        elif ch == b">" and depth <= 0:
            return head[m.start():i + 1]
        i += 1
    return None


# ══════════════════════════════════════════════════════════════
# 时间层
# ══════════════════════════════════════════════════════════════

def parse_time_text(text, naive_rule="utc8"):
    """
    解析一个 GPX/TCX 时间文本。

    返回 (utc_datetime | None, 小数秒位数 | None, 分隔符)
    支持的写法：Z / z / +08:00 / +0800 / +08 / 无时区 / 无秒位 /
               空格或 T 分隔 / 任意位小数秒 / 逗号作小数点。
    """
    if not text:
        return None, None, "T"
    m = TIME_RE.match(text)
    if m is None:
        return None, None, "T"

    frac = m.group("frac")
    try:
        dt = datetime(
            int(m.group("y")), int(m.group("mo")), int(m.group("d")),
            int(m.group("h")), int(m.group("mi")),
            int(m.group("s") or 0),
            int(((frac or "") + "000000")[:6]),
        )
    except ValueError:
        return None, None, "T"

    tz = m.group("tz")
    if tz is None:
        # 没有任何时区标记 —— 按选定口径解释，绝不猜测
        if naive_rule == "utc":
            dt = dt.replace(tzinfo=timezone.utc)
        elif naive_rule == "utc8":
            dt = dt.replace(tzinfo=TZ_CN)
        else:                      # 'local'：naive.astimezone 视本机本地时间
            dt = dt.astimezone(timezone.utc)
    else:
        if tz in ("Z", "z"):
            dt = dt.replace(tzinfo=timezone.utc)
        else:
            sign = 1 if tz[0] == "+" else -1
            body = tz[1:].replace(":", "")
            off = timedelta(hours=int(body[:2]),
                            minutes=int(body[2:4]) if len(body) > 2 else 0)
            dt = dt.replace(tzinfo=timezone(sign * off))
        dt = dt.astimezone(timezone.utc)     # ★ 真换算，不是 replace

    sep = "T" if ("T" in text or "t" in text) else " "
    return dt, (len(frac) if frac else None), sep


ZONE_TOKEN_RE = re.compile(r"(?P<z>[Zz]|[+-]\d{2}(?::?\d{2})?)\s*$")


def parse_zone_token(text):
    """取出时间文本尾部的时区写法：'Z' / '+08:00' / '+0800' / '+08' / ''（无时区）。"""
    if not text:
        return ""
    m = ZONE_TOKEN_RE.search(text.strip())
    return m.group("z") if m else ""


def _fmt_base(dt, frac_digits, sep="T"):
    base = dt.strftime("%Y-%m-%d") + sep + dt.strftime("%H:%M:%S")
    if frac_digits:
        us = "%06d" % dt.microsecond
        if frac_digits <= 6:
            base += "." + us[:frac_digits]
        else:
            base += "." + us + "0" * (frac_digits - 6)
    return base


def format_utc(dt, frac_digits, sep="T"):
    """按源文件的写法输出，固定以 Z 结尾。"""
    return _fmt_base(dt, frac_digits, sep) + "Z"


def format_like_source(dt_utc, ana):
    """
    把 UTC 时间按源文件的「时区写法」输出，保证新点与邻居文本风格一致。

    这对「按时间做文本匹配」的下游工具很重要：如果邻居写的是 +08:00 而新点写
    Z，字面排序和正则匹配都会错位（虽然两者表示的是同一时刻）。
    """
    token = ana.zone_style
    if token in ("Z", "z"):
        return format_utc(dt_utc, ana.frac_digits, ana.sep)
    if token:
        sign = 1 if token[0] == "+" else -1
        body = token[1:].replace(":", "")
        off = timedelta(hours=int(body[:2]),
                        minutes=int(body[2:4]) if len(body) > 2 else 0)
        local = dt_utc.astimezone(timezone(sign * off))
        return _fmt_base(local, ana.frac_digits, ana.sep) + token
    # 源文件没有时区标记：按同一口径还原成墙钟时间写法
    rule = ana.opts_naive_rule
    if rule == "utc8":
        wall = dt_utc.astimezone(TZ_CN)
    elif rule == "utc":
        wall = dt_utc
    else:
        wall = dt_utc.astimezone()
    return _fmt_base(wall, ana.frac_digits, ana.sep)


def to_beijing(dt):
    return dt.astimezone(TZ_CN)


# ══════════════════════════════════════════════════════════════
# XML 辅助（一律按 local-name 匹配，天然兼容前缀命名空间与 1.0/1.1）
# ══════════════════════════════════════════════════════════════

def local_name(tag):
    if not isinstance(tag, str):
        return ""
    return tag.rsplit("}", 1)[-1]


def ns_prefix_of(tag):
    """从 '{uri}name' 取出 '{uri}' 部分；无命名空间时返回 ''。"""
    if isinstance(tag, str) and tag.startswith("{"):
        return tag[: tag.index("}") + 1]
    return ""


def first_child_named(elem, name):
    for c in elem:
        if isinstance(c.tag, str) and local_name(c.tag) == name:
            return c
    return None


def text_of(elem):
    if elem is None:
        return None
    t = elem.text
    return t.strip() if t and t.strip() else None


def _detect_decimals(texts, default, lo, hi):
    """按源文件里数值的小数位「众数」决定输出精度，让整份文件风格统一。"""
    cnt = Counter()
    for t in texts:
        t = (t or "").strip()
        if "." in t and re.match(r"^-?\d+\.\d+$", t):
            cnt[len(t.split(".")[1])] += 1
    if not cnt:
        return default
    best = max(cnt.items(), key=lambda kv: (kv[1], kv[0]))[0]
    return max(lo, min(hi, best))


# ══════════════════════════════════════════════════════════════
# 选项
# ══════════════════════════════════════════════════════════════

class Options(object):
    def __init__(self, gap_threshold=None, interval=None, max_gap=None,
                 naive_rule="utc8", format_output=True, indent="  ",
                 print_detail=True, write_report=False):
        self.gap_threshold = float(DEFAULTS["gap_threshold"] if gap_threshold is None else gap_threshold)
        self.interval = float(DEFAULTS["interval"] if interval is None else interval)
        self.max_gap = float(DEFAULTS["max_gap"] if max_gap is None else max_gap)
        self.naive_rule = naive_rule
        self.format_output = bool(format_output)
        self.indent = indent or "  "
        self.print_detail = bool(print_detail)
        self.write_report = bool(write_report)

    def validate(self):
        if self.interval <= 0:
            raise ValueError("插入间隔必须大于 0 秒。")
        if self.gap_threshold < 0:
            raise ValueError("插值阈值不能为负数。")
        if self.max_gap <= 0:
            raise ValueError("最长插值间隔必须大于 0 秒。")
        if self.max_gap < self.interval:
            raise ValueError("最长插值间隔不能小于插入间隔。")

    def describe(self):
        return ("阈值 %.4gs / 步长 %.4gs / 最长 %.4gs / 无时区=%s / 格式化=%s"
                % (self.gap_threshold, self.interval, self.max_gap,
                   self.naive_rule, "开" if self.format_output else "关"))


# ══════════════════════════════════════════════════════════════
# 点解析
# ══════════════════════════════════════════════════════════════

class Point(object):
    __slots__ = ("elem", "time", "lat", "lon", "ele", "ele_layout")

    def __init__(self, elem, time, lat, lon, ele, ele_layout=None):
        self.elem = elem
        self.time = time
        self.lat = lat
        self.lon = lon
        self.ele = ele
        self.ele_layout = ele_layout    # TCX: 'direct' / 'in_position' / None


def parse_gpx_point(elem, naive_rule):
    """解析 <trkpt>；任何必需字段缺失/非法都返回 (None, 原因)。"""
    lat_s, lon_s = elem.get("lat"), elem.get("lon")
    if lat_s is None or lon_s is None:
        return None, "缺少 lat/lon 属性"
    try:
        lat, lon = float(lat_s), float(lon_s)
    except (TypeError, ValueError):
        return None, "lat/lon 不是数字"
    t_el = first_child_named(elem, "time")
    raw = text_of(t_el)
    if raw is None:
        return None, "缺少 <time>"
    dt, _frac, _sep = parse_time_text(raw, naive_rule)
    if dt is None:
        return None, "时间写法无法解析：%s" % raw

    ele = None
    ele_el = first_child_named(elem, "ele")
    if ele_el is not None:
        try:
            ele = float(text_of(ele_el))
        except (TypeError, ValueError):
            ele = None
    return Point(elem, dt, lat, lon, ele), None


def parse_tcx_point(elem, naive_rule):
    """解析 <Trackpoint>；兼容小米把 AltitudeMeters 放进 <Position> 的写法。"""
    t_el = first_child_named(elem, "Time")
    raw = text_of(t_el)
    if raw is None:
        return None, "缺少 <Time>"
    dt, _frac, _sep = parse_time_text(raw, naive_rule)
    if dt is None:
        return None, "时间写法无法解析：%s" % raw

    pos = first_child_named(elem, "Position")
    if pos is None:
        return None, "缺少 <Position>"
    lat_el = first_child_named(pos, "LatitudeDegrees")
    lon_el = first_child_named(pos, "LongitudeDegrees")
    if lat_el is None or lon_el is None:
        return None, "缺少经纬度"
    try:
        lat = float(text_of(lat_el))
        lon = float(text_of(lon_el))
    except (TypeError, ValueError):
        return None, "经纬度不是数字"

    ele, layout = None, None
    direct = first_child_named(elem, "AltitudeMeters")       # 标准 TCX 写法
    if direct is not None:
        layout = "direct"
        try:
            ele = float(text_of(direct))
        except (TypeError, ValueError):
            ele = None
    else:
        inner = first_child_named(pos, "AltitudeMeters")     # 小米写法
        if inner is not None:
            layout = "in_position"
            try:
                ele = float(text_of(inner))
            except (TypeError, ValueError):
                ele = None
    return Point(elem, dt, lat, lon, ele, layout), None


# ══════════════════════════════════════════════════════════════
# 分析（阶段一：只算不做，供预览与统计）
# ══════════════════════════════════════════════════════════════

class GapInsertion(object):
    """一段待插值的区间。"""
    __slots__ = ("container", "anchor_idx", "anchor", "tail_point",
                 "gap", "rows", "flat_ele", "seq")

    def __init__(self, container, anchor_idx, anchor, tail_point, gap, seq):
        self.container = container      # 所在 trkseg / Track 元素
        self.anchor_idx = anchor_idx    # 前点在容器子元素中的下标
        self.anchor = anchor            # 前点 Point
        self.tail_point = tail_point    # 后点 Point
        self.gap = gap                  # 秒
        self.rows = []                  # [(dt, lat, lon, ele, ele_src)]
        self.flat_ele = 0
        self.seq = seq                  # 全局区间序号


class Analysis(object):
    def __init__(self):
        self.path = ""
        self.fmt = "gpx"
        self.tree = None
        self.root = None
        self.decl = {}
        self.doctype = None             # 源文件的 DOCTYPE 声明（原样保留）
        self.ns_decls = {}              # 源文件里的 xmlns 声明
        self.ends_with_newline = True
        self.segments = []              # 容器元素列表
        self.points_total = 0
        self.gaps = []                  # 原始相邻间隔（秒）
        self.post_gaps = []             # 处理后会出现的间隔（秒）
        self.plan = []                  # [GapInsertion]
        self.skipped = []               # [(段号, 下标, 原因)]
        self.long_gaps = []             # [(段号, 前点时间, 后点时间, 间隔)]
        self.naive_count = 0            # 无时区时间的数量
        self.times = []                 # 全部可解析时间(UTC)
        self.frac_digits = None
        self.sep = "T"
        self.zone_style = "Z"           # 新点时间的时区写法（镜像源文件）
        self.zone_mixed = False         # 源文件里时区写法是否混杂
        self.lat_dec = 7
        self.lon_dec = 7
        self.ele_dec = 1
        self.ele_missing = 0
        self.dup_times = 0              # 相邻时间完全相同（0 秒间隔）
        self.back_times = 0             # 相邻时间为负（源数据时间倒流）
        self.opts_naive_rule = "utc8"

    # -- 统计 --------------------------------------------------
    @property
    def inserted(self):
        return sum(len(g.rows) for g in self.plan)

    @property
    def new_total(self):
        return self.points_total + self.inserted

    @property
    def flat_ele_total(self):
        return sum(g.flat_ele for g in self.plan)

    def gap_stats(self):
        g = self.gaps
        if not g:
            return (0.0, 0.0, 0.0)
        return (min(g), max(g), sum(g) / len(g))

    def max_gap_after(self):
        return max(self.post_gaps) if self.post_gaps else 0.0

    @property
    def time_range(self):
        if not self.times:
            return None
        return (min(self.times), max(self.times))


def _load_declaration(path):
    """读取源 XML 声明的引号风格 / version / encoding / standalone，
    以及声明后面是否原本就跟了换行（决定是否补换行）。"""
    info = {"quote": '"', "version": "1.0", "encoding": "UTF-8",
            "standalone": None, "decl_newline": True}
    try:
        with open(path, "rb") as f:
            head = f.read(4096)
    except OSError:
        return info
    m = DECL_RE.search(head)
    if m is None:
        return info
    rest = head[m.end():m.end() + 2]
    info["decl_newline"] = rest.startswith(b"\n") or rest.startswith(b"\r")
    body = m.group(1).decode("ascii", "replace")
    if "'" in body and '"' not in body:
        info["quote"] = "'"
    for key in ("version", "encoding", "standalone"):
        mm = re.search(ATTR_RE % key, body)
        if mm:
            info[key] = mm.group(1)
    return info


def detect_format(path, root):
    name = local_name(root.tag).lower()
    if name == "gpx":
        return "gpx"
    if name == "trainingcenterdatabase":
        return "tcx"
    ext = os.path.splitext(path)[1].lower()
    if ext == ".tcx":
        return "tcx"
    if ext == ".gpx":
        return "gpx"
    raise ValueError("无法识别文件格式（根元素 <%s>），请确认是 GPX 或 TCX。"
                     % local_name(root.tag))


def analyze_file(path, opts, log=None):
    """解析文件并算出完整的插值计划（不修改任何内容）。"""
    log = log or (lambda m: None)
    ana = Analysis()
    ana.path = path
    ana.decl = _load_declaration(path)

    with open(path, "rb") as f:
        tail = f.read()[-2:]
    ana.ends_with_newline = tail.endswith(b"\n")

    # 先把源文件里所有命名空间前缀注册好，避免输出退化成 ns0:
    ana.ns_decls = register_source_namespaces(path)
    ana.doctype = extract_doctype(path)

    # 注释必须显式保留：标准库 ElementTree 默认会把注释丢掉
    # （Python 3.8+ 的 TreeBuilder 支持 insert_comments / insert_pis）
    try:
        parser = etree.XMLParser(
            target=etree.TreeBuilder(insert_comments=True, insert_pis=True))
    except TypeError:                    # 极老版本的标准库兜底
        parser = None
    ana.tree = etree.parse(path, parser) if parser is not None else etree.parse(path)
    ana.root = ana.tree.getroot()
    if ana.root is None:
        raise ValueError("文件内容为空，没有 XML 根元素。")

    ana.fmt = detect_format(path, ana.root)
    tags = FMT_TAGS[ana.fmt]

    containers = [e for e in ana.root.iter()
                  if isinstance(e.tag, str) and local_name(e.tag) == tags["container"]]
    if not containers:
        raise ValueError("文件中未找到轨迹段 <%s>，没有可处理的数据。"
                         % tags["container"])
    ana.segments = containers

    log("格式：%s，轨迹段 %d 个" % (ana.fmt.upper(), len(containers)))
    ana.opts_naive_rule = opts.naive_rule

    parse_point = parse_gpx_point if ana.fmt == "gpx" else parse_tcx_point
    lat_texts, lon_texts, ele_texts = [], [], []
    seq = 0

    for si, container in enumerate(containers, 1):
        children = list(container)
        anchor, anchor_idx = None, None

        for idx, child in enumerate(children):
            if not (isinstance(child.tag, str)
                    and local_name(child.tag) == tags["point"]):
                continue                      # 非轨迹点元素：原样保留，不影响链路
            pt, reason = parse_point(child, opts.naive_rule)
            if pt is None:
                ana.skipped.append((si, idx, reason))
                log("  段 %d 第 %d 个子元素无法解析（%s）→ 原样保留，"
                    "且不在它两侧跨点插值" % (si, idx, reason))
                anchor, anchor_idx = None, None      # ★ 阻断跨点插值
                continue

            ana.points_total += 1
            ana.times.append(pt.time)
            if ana.fmt == "gpx":
                lat_texts.append(child.get("lat"))
                lon_texts.append(child.get("lon"))
            else:                       # TCX 的经纬度是子元素，不是属性
                pos = first_child_named(child, "Position")
                lat_texts.append(text_of(first_child_named(pos, "LatitudeDegrees"))
                                 if pos is not None else None)
                lon_texts.append(text_of(first_child_named(pos, "LongitudeDegrees"))
                                 if pos is not None else None)

            raw_time = text_of(first_child_named(
                child, "Time" if ana.fmt == "tcx" else "time"))
            if raw_time and not re.search(r"[Zz]$|[+-]\d{2}", raw_time):
                ana.naive_count += 1

            ele_el = first_child_named(
                child, "AltitudeMeters" if ana.fmt == "tcx" else "ele")
            if ana.fmt == "tcx" and ele_el is None:
                pos = first_child_named(child, "Position")
                ele_el = first_child_named(pos, "AltitudeMeters") if pos is not None else None
            if ele_el is not None:
                ele_texts.append(text_of(ele_el))
            if pt.ele is None:
                ana.ele_missing += 1

            if anchor is not None:
                gap = (pt.time - anchor.time).total_seconds()
                ana.gaps.append(gap)
                if gap == 0:
                    ana.dup_times += 1
                elif gap < 0:
                    ana.back_times += 1

                if gap > opts.gap_threshold:
                    if gap > opts.max_gap:
                        ana.long_gaps.append((si, anchor.time, pt.time, gap))
                        ana.post_gaps.append(gap)
                        log("  ⚠ 段 %d 出现 %.1f 秒间隔，超过最长插值间隔 %.0f 秒 → "
                            "跳过不插值（%s → %s）"
                            % (si, gap, opts.max_gap,
                               anchor.time.strftime("%Y-%m-%dT%H:%M:%SZ"),
                               pt.time.strftime("%Y-%m-%dT%H:%M:%SZ")))
                    else:
                        seq += 1
                        ins = GapInsertion(container, anchor_idx, anchor, pt, gap, seq)
                        n = int(gap / opts.interval + 1e-9) - 1
                        ea, eb = anchor.ele, pt.ele
                        for k in range(1, n + 1):
                            r = k / (n + 1.0)
                            if ea is None and eb is None:
                                ele, src = None, "none"
                            elif ea is None:
                                ele, src = eb, "flat"
                            elif eb is None:
                                ele, src = ea, "flat"
                            else:
                                ele, src = ea + (eb - ea) * r, "linear"
                            if src == "flat":
                                ins.flat_ele += 1
                            ins.rows.append((
                                anchor.time + timedelta(seconds=gap * r),
                                anchor.lat + (pt.lat - anchor.lat) * r,
                                anchor.lon + (pt.lon - anchor.lon) * r,
                                ele, src))
                        ana.plan.append(ins)
                        ana.post_gaps.append(gap / (n + 1.0))
                else:
                    ana.post_gaps.append(gap)
            anchor, anchor_idx = pt, idx

    # ---- 输出风格：时间小数位 / 分隔符 / 时区写法 / 数值精度 ----
    fracs = Counter()
    seps = Counter()
    zones = Counter()
    for container in containers:
        for child in container:
            if not (isinstance(child.tag, str)
                    and local_name(child.tag) == tags["point"]):
                continue
            raw = text_of(first_child_named(
                child, "Time" if ana.fmt == "tcx" else "time"))
            dt, frac, sep = parse_time_text(raw, opts.naive_rule)
            if dt is not None:
                fracs[frac] += 1
                seps[sep] += 1
                zones[parse_zone_token(raw)] += 1
    if fracs:
        # 取小数位数的众数；None（无小数秒）视作 -1，避免与 int 比较
        ana.frac_digits = max(
            fracs.items(),
            key=lambda kv: (kv[1], -1 if kv[0] is None else kv[0]))[0]
    if seps:
        ana.sep = max(seps.items(), key=lambda kv: kv[1])[0]
    if zones:
        ana.zone_style = max(zones.items(), key=lambda kv: kv[1])[0]
        ana.zone_mixed = len(zones) > 1
    ana.lat_dec = _detect_decimals(lat_texts, 7, 6, 15)
    ana.lon_dec = _detect_decimals(lon_texts, 7, 6, 15)
    ana.ele_dec = _detect_decimals(ele_texts, 1, 0, 3)

    log("原始点 %d 个，相邻间隔 最大 %.1fs / 平均 %.2fs"
        % ((ana.points_total,) + ana.gap_stats()[1:]))
    return ana


# ══════════════════════════════════════════════════════════════
# 新点构造
# ══════════════════════════════════════════════════════════════

def _child_order(anchor_elem, need_ele, point_tags):
    """镜像前点的子元素顺序，保证新点结构与文件自身风格一致。"""
    order = [local_name(c.tag) for c in anchor_elem
             if isinstance(c.tag, str) and local_name(c.tag) in point_tags]
    if "time" not in order:
        order.append("time")
    if need_ele and "ele" not in order:
        order.insert(0, "ele")
    return [n for n in order if n != "ele" or need_ele]


def build_gpx_point(anchor_elem, dt, lat, lon, ele, ana):
    ns = ns_prefix_of(anchor_elem.tag)
    pt = etree.Element(ns + "trkpt")
    pt.set("lat", ("%%.%df" % ana.lat_dec) % lat)
    pt.set("lon", ("%%.%df" % ana.lon_dec) % lon)
    for name in _child_order(anchor_elem, ele is not None, ("ele", "time")):
        if name == "ele":
            c = etree.SubElement(pt, ns + "ele")
            c.text = ("%%.%df" % ana.ele_dec) % ele
        else:
            c = etree.SubElement(pt, ns + "time")
            c.text = format_like_source(dt, ana)
    return pt


def build_tcx_point(anchor_elem, dt, lat, lon, ele, ana, layout):
    ns = ns_prefix_of(anchor_elem.tag)
    pt = etree.Element(ns + "Trackpoint")
    t = etree.SubElement(pt, ns + "Time")
    t.text = format_like_source(dt, ana)
    pos = etree.SubElement(pt, ns + "Position")
    la = etree.SubElement(pos, ns + "LatitudeDegrees")
    la.text = ("%%.%df" % ana.lat_dec) % lat
    lo = etree.SubElement(pos, ns + "LongitudeDegrees")
    lo.text = ("%%.%df" % ana.lon_dec) % lon
    if ele is not None:
        if layout == "in_position":
            e = etree.SubElement(pos, ns + "AltitudeMeters")
        else:
            e = etree.SubElement(pt, ns + "AltitudeMeters")
        e.text = ("%%.%df" % ana.ele_dec) % ele
    return pt


# ══════════════════════════════════════════════════════════════
# 排版 / 写出
# ══════════════════════════════════════════════════════════════

def _layout_only(elem):
    """元素内部是否只有排版空白（没有混合内容）。"""
    if elem.text is not None and elem.text.strip():
        return False
    for c in elem:
        if c.tail is not None and c.tail.strip():
            return False
    return True


def reindent(elem, level=0, unit="  "):
    """按层级重排缩进；混合内容（文本+子元素混排）整段跳过，不动内容。"""
    kids = list(elem)
    if not kids:
        return
    if not _layout_only(elem):
        for c in kids:
            if isinstance(c.tag, str):
                reindent(c, level + 1, unit)
        return
    elem.text = "\n" + unit * (level + 1)
    for i, c in enumerate(kids):
        if isinstance(c.tag, str):
            reindent(c, level + 1, unit)
        c.tail = "\n" + unit * (level + 1) if i < len(kids) - 1 else "\n" + unit * level


def declaration_text(info):
    q = info.get("quote", '"')
    parts = ["version=%s%s%s" % (q, info.get("version", "1.0"), q)]
    enc = info.get("encoding") or "UTF-8"
    parts.append("encoding=%s%s%s" % (q, enc, q))
    if info.get("standalone") is not None:
        parts.append("standalone=%s%s%s" % (q, info["standalone"], q))
    return ("<?xml %s?>" % " ".join(parts)).encode("ascii", "replace")


def unique_path(path):
    """重名时自动加序号，绝不静默覆盖。"""
    if not os.path.exists(path):
        return path
    base, ext = os.path.splitext(path)
    n = 2
    while True:
        cand = "%s%d%s" % (base, n, ext)
        if not os.path.exists(cand):
            return cand
        n += 1


def apply_and_write(ana, opts, log=None, detail=None, should_cancel=None,
                    progress=None):
    """按计划原位插入新点并原子写出，返回输出路径。

    progress: 可选回调 progress(done, total)，每插一个点报一次，
              供 GUI 驱动确定性进度条；CLI 传 None 即可。
    """
    log = log or (lambda m: None)
    detail = detail or (lambda m: None)
    should_cancel = should_cancel or (lambda: False)
    progress = progress or (lambda done, total: None)

    tags = FMT_TAGS[ana.fmt]

    # ---- 按容器分组，原位插入 ----
    groups = OrderedDict()
    for ins in ana.plan:
        groups.setdefault(id(ins.container), [ins.container, []])[1].append(ins)

    built = 0
    for _key, (container, ins_list) in groups.items():
        by_idx = {}
        for ins in ins_list:
            by_idx.setdefault(ins.anchor_idx, []).append(ins)

        children = list(container)
        new_children = []
        for idx, child in enumerate(children):
            new_children.append(child)             # 原有元素一个不丢
            for ins in by_idx.get(idx, ()):
                if should_cancel():
                    raise KeyboardInterrupt
                layout = None
                if ana.fmt == "tcx":
                    layout = ins.anchor.ele_layout or ins.tail_point.ele_layout or "direct"
                for dt, lat, lon, ele, _src in ins.rows:
                    if ana.fmt == "gpx":
                        el = build_gpx_point(child, dt, lat, lon, ele, ana)
                    else:
                        el = build_tcx_point(child, dt, lat, lon, ele, ana, layout)
                    el.tail = child.tail       # 沿用原有排版空白
                    new_children.append(el)
                    built += 1
                    progress(built, ana.inserted)

        for c in children:
            container.remove(c)
        for c in new_children:
            container.append(c)

    if built != ana.inserted:
        raise AssertionError("内部计数不一致：%d != %d" % (built, ana.inserted))

    # ---- 可选格式化 ----
    if opts.format_output:
        reindent(ana.root, 0, opts.indent)

    # ---- 序列化（自己拼声明，保住 standalone / 引号风格 / DOCTYPE）----
    enc = (ana.decl.get("encoding") or "UTF-8").upper()
    body = etree.tostring(ana.root, encoding="unicode")
    try:
        body_bytes = body.encode(enc)
    except (UnicodeEncodeError, LookupError):
        enc = "UTF-8"
        body_bytes = body.encode("utf-8")
        log("源文件声明的编码无法写出，已改用 UTF-8。")

    decl_info = dict(ana.decl)
    decl_info["encoding"] = enc
    head_parts = [declaration_text(decl_info)]
    if ana.doctype:
        head_parts.append(ana.doctype)
    sep = b"\n" if decl_info.get("decl_newline", True) else b""
    data = b"\n".join(head_parts) + sep + body_bytes
    if ana.ends_with_newline and not data.endswith(b"\n"):
        data += b"\n"

    # ---- 输出路径 + 原子替换 ----
    base, ext = os.path.splitext(ana.path)
    out_path = unique_path("%s%s%s" % (base, DEFAULT_OUT_SUFFIX, ext))
    dir_name = os.path.dirname(out_path) or "."
    fd, tmp_path = tempfile.mkstemp(dir=dir_name, prefix=".interp_", suffix=".tmp")
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(data)
        try:                                    # 权限对齐源文件
            os.chmod(tmp_path, os.stat(ana.path).st_mode & 0o777)
        except OSError:
            pass
        os.replace(tmp_path, out_path)
    except BaseException:
        try:
            os.unlink(tmp_path)
        except OSError:
            pass
        raise

    log("已写出：%s（%.1f KB → %.1f KB）"
        % (out_path, os.path.getsize(ana.path) / 1024.0,
           os.path.getsize(out_path) / 1024.0))
    return out_path


# ══════════════════════════════════════════════════════════════
# 回读校验
# ══════════════════════════════════════════════════════════════

def verify_output(out_path, ana):
    """回读输出：点数对不对、原始点是否都在、插值后最大间隔是多少。"""
    tree = etree.parse(out_path)
    root = tree.getroot()
    tags = FMT_TAGS[ana.fmt]
    containers = [e for e in root.iter()
                  if isinstance(e.tag, str) and local_name(e.tag) == tags["container"]]
    pts = [c for cont in containers for c in cont
           if isinstance(c.tag, str) and local_name(c.tag) == tags["point"]]

    def sig(el):
        lat = el.get("lat")
        lon = el.get("lon")
        if ana.fmt == "tcx":
            pos = first_child_named(el, "Position")
            lat = text_of(first_child_named(pos, "LatitudeDegrees")) if pos is not None else None
            lon = text_of(first_child_named(pos, "LongitudeDegrees")) if pos is not None else None
        t = text_of(first_child_named(el, "Time" if ana.fmt == "tcx" else "time"))
        return (lat, lon, t)

    out_sigs = set(sig(p) for p in pts)
    orig_sigs = set()
    for cont in ana.segments:
        for c in cont:
            if isinstance(c.tag, str) and local_name(c.tag) == tags["point"]:
                orig_sigs.add(sig(c))

    # 原始点是被改动过的（时间可能重写），所以只校验数量与经纬度覆盖
    missing = 0
    out_latlon = set((s[0], s[1]) for s in out_sigs)
    for s in orig_sigs:
        if (s[0], s[1]) not in out_latlon:
            missing += 1

    times, gaps = [], []
    naive_rule = ana.opts_naive_rule
    for p in pts:
        raw = text_of(first_child_named(p, "Time" if ana.fmt == "tcx" else "time"))
        dt, _f, _s = parse_time_text(raw, naive_rule)
        if dt is not None:
            times.append(dt)
    times.sort()
    gaps = [(times[i] - times[i - 1]).total_seconds() for i in range(1, len(times))]

    return {
        "points": len(pts),
        "expected": ana.new_total,
        "missing": missing,
        "max_gap": max(gaps) if gaps else 0.0,
        "time_min": times[0] if times else None,
        "time_max": times[-1] if times else None,
        "unparsable": len(pts) - len(times),
    }


# ══════════════════════════════════════════════════════════════
# 报告文本
# ══════════════════════════════════════════════════════════════

def _fmt_range(ana):
    tr = ana.time_range
    if tr is None:
        return "（无有效时间）"
    a, b = tr
    return ("%s → %s\n        北京时间  %s → %s"
            % (a.strftime("%Y-%m-%dT%H:%M:%SZ"), b.strftime("%Y-%m-%dT%H:%M:%SZ"),
               to_beijing(a).strftime("%Y-%m-%d %H:%M:%S"),
               to_beijing(b).strftime("%Y-%m-%d %H:%M:%S")))


def build_summary(ana, opts):
    gmin, gmax, gavg = ana.gap_stats()
    after = ana.max_gap_after()

    lines = []
    lines.append("文件      : %s" % os.path.basename(ana.path))
    lines.append("格式      : %s，轨迹段 %d 个"
                 % (ana.fmt.upper(), len(ana.segments)))
    lines.append("时间范围  : %s" % _fmt_range(ana))
    lines.append("时间写法  : %s%s（新点镜像此写法）"
                 % ("无小数秒" if ana.frac_digits is None
                    else "%d 位小数秒" % ana.frac_digits,
                    "，时区 " + (ana.zone_style or "无时区标记")))
    if ana.zone_mixed:
        lines.append("⚠时区混杂: 源文件里存在多种时区写法（新点按多数派「%s」写）"
                     % (ana.zone_style or "无时区标记"))
    lines.append("原始点    : %d 个，相邻间隔 最大 %.1fs / 平均 %.2fs"
                 % (ana.points_total, gmax, gavg))
    lines.append("待插值    : %d 个区间，共插入 %d 点"
                 % (len(ana.plan), ana.inserted))
    lines.append("处理结果  : %d 点 → %d 点" % (ana.points_total, ana.new_total))
    if ana.inserted:
        lines.append("插值后    : 最大间隔约 %.1fs" % after)
        if after > 5.0:
            lines.append("匹配精度  : 照片最多可能匹配到 %.1fs 外的点 ≈ ±%.0f 米；"
                         "要更准可把插值阈值调小（如 5 秒）"
                         % (after / 2.0, after / 2.0 * 1.4))
    if ana.naive_count:
        lines.append("无时区时间: %d 处，按「%s」解释"
                     % (ana.naive_count, NAIVE_RULES.get(opts.naive_rule, opts.naive_rule)))
    if ana.ele_missing:
        lines.append("缺海拔    : %d 个原始点无海拔数据" % ana.ele_missing)
    if ana.flat_ele_total:
        lines.append("海拔说明  : %d 个新点因仅一端有海拔而平推取值" % ana.flat_ele_total)
    if ana.skipped:
        lines.append("无法解析  : %d 个点（已原样保留、不参与插值）" % len(ana.skipped))
    if ana.dup_times:
        lines.append("重复时间  : %d 处相邻点时间完全相同（源数据如此，未改动；"
                     "按时间匹配时可能落在同一点上）" % ana.dup_times)
    if ana.back_times:
        lines.append("⚠时间倒流: %d 处相邻点时间比前一点更早（源数据异常，未改动）"
                     % ana.back_times)
    if ana.long_gaps:
        lines.append("跳过区间  : %d 处间隔超过 %.0f 秒，未插值"
                     % (len(ana.long_gaps), opts.max_gap))
    return "\n".join(lines)


def build_preview(ana, opts, head=3):
    lines = [build_summary(ana, opts), ""]
    if ana.plan:
        lines.append("前 %d 个插值区间：" % min(head, len(ana.plan)))
        for gi in ana.plan[:head]:
            lines.append("  %s → %s  (%.1fs，插 %d 点)"
                         % (gi.anchor.time.strftime("%m-%d %H:%M:%S"),
                            gi.tail_point.time.strftime("%H:%M:%S"),
                            gi.gap, len(gi.rows)))
    if ana.long_gaps:
        lines.append("")
        lines.append("被跳过的长间隔：")
        for si, ta, tb, g in ana.long_gaps[:5]:
            lines.append("  段 %d  %s → %s  (%.1fs)"
                         % (si, ta.strftime("%m-%d %H:%M:%S"),
                            tb.strftime("%H:%M:%S"), g))
    return "\n".join(lines)


def build_detail_report(ana, opts, out_path=None):
    """生成逐区间的插值明细（控制台打印 / 可另存 txt）。"""
    buf = []
    w = buf.append
    w("=" * 78)
    w("GPX/TCX 轨迹插值明细")
    w("=" * 78)
    w(build_summary(ana, opts))
    if out_path:
        w("输出文件  : %s" % out_path)
    w("")

    for gi in ana.plan:
        w("=" * 78)
        w("  插值 #%d   段内插入 %d 点" % (gi.seq, len(gi.rows)))
        w("  时间区间 : %s → %s  (间隔 %.1fs)"
          % (gi.anchor.time.strftime("%Y-%m-%dT%H:%M:%SZ"),
             gi.tail_point.time.strftime("%Y-%m-%dT%H:%M:%SZ"), gi.gap))
        w("  前点坐标 : %.6f, %.6f  海拔 %s"
          % (gi.anchor.lat, gi.anchor.lon,
             "—" if gi.anchor.ele is None else "%.1fm" % gi.anchor.ele))
        w("  后点坐标 : %.6f, %.6f  海拔 %s"
          % (gi.tail_point.lat, gi.tail_point.lon,
             "—" if gi.tail_point.ele is None else "%.1fm" % gi.tail_point.ele))
        w("  " + "-" * 72)
        w("  %4s  %-22s  %*s  %*s  %8s  %s"
          % ("序号", "UTC 时间", ana.lat_dec + 4, "纬度",
             ana.lon_dec + 4, "经度", "海拔(m)", "来源"))
        w("  " + "-" * 72)
        for j, (dt, lat, lon, ele, src) in enumerate(gi.rows, 1):
            w("  %4d  %-22s  %*.*f  %*.*f  %8s  %s"
              % (j, dt.strftime("%Y-%m-%dT%H:%M:%S.%f")[:-3] + "Z",
                 ana.lat_dec + 4, ana.lat_dec, lat,
                 ana.lon_dec + 4, ana.lon_dec, lon,
                 "—" if ele is None else "%.1f" % ele,
                 {"linear": "线性插值", "flat": "单端平推",
                  "none": "无海拔"}.get(src, src)))
        w("=" * 78)
        w("")
    return "\n".join(buf)


# ══════════════════════════════════════════════════════════════
# 命令行
# ══════════════════════════════════════════════════════════════

def cli_main(args):
    opts = Options(gap_threshold=args.threshold, interval=args.interval,
                   max_gap=args.max_gap, naive_rule=args.naive,
                   format_output=not args.no_format,
                   print_detail=not args.quiet,
                   write_report=args.report)
    opts.validate()

    print("分析：%s" % args.file)
    ana = analyze_file(args.file, opts, log=lambda m: print("  " + m))
    print()
    print(build_preview(ana, opts, head=5))

    if not ana.plan:
        print("\n没有需要插值的区间，未生成文件。")
        return 0
    if args.preview:
        print("\n（--preview 模式：未写出文件）")
        return 0

    out = apply_and_write(ana, opts, log=lambda m: print("  " + m))
    if not args.quiet:
        text = build_detail_report(ana, opts, out)
        print()
        print(text)
    if opts.write_report:
        rep = os.path.splitext(out)[0] + "_插值明细.txt"
        with open(rep, "w", encoding="utf-8") as f:
            f.write(build_detail_report(ana, opts, out))
        print("明细报告：%s" % rep)

    ana.opts_naive_rule = opts.naive_rule
    v = verify_output(out, ana)
    print("回读校验：%d 点（应为 %d），原始点缺失 %d，插值后最大间隔 %.1fs，"
          "时间无法解析 %d" % (v["points"], v["expected"], v["missing"],
                              v["max_gap"], v["unparsable"]))
    return 0


# ══════════════════════════════════════════════════════════════
# GUI
# ══════════════════════════════════════════════════════════════

def pick_font(root):
    """跨平台挑一个能显示中文的字体。"""
    try:
        from tkinter import font as tkfont
        fams = set(tkfont.families(root))
    except Exception:
        return "TkDefaultFont"
    for name in ("PingFang SC", "Microsoft YaHei", "Hiragino Sans GB",
                 "Noto Sans CJK SC", "Source Han Sans SC", "WenQuanYi Micro Hei",
                 "Heiti SC", "STHeiti", "SimHei", "Arial Unicode MS"):
        if name in fams:
            return name
    return "TkDefaultFont"


class App(object):
    def __init__(self, root):
        self.root = root
        self.root.title("%s %s" % (APP_TITLE, APP_VERSION))
        self.font = pick_font(root)
        self._busy = False
        self._cancel = False
        self._q = queue.Queue()
        self.ana = None
        self.opts = None

        self.style = ttk.Style()
        try:
            self.style.theme_use("clam")
        except tk.TclError:
            pass
        self._setup_style()

        self.filepath = tk.StringVar(value="")
        self.status_text = tk.StringVar(value="就绪：请选择 GPX 或 TCX 文件")
        self.v_threshold = tk.StringVar(value="20")
        self.v_interval = tk.StringVar(value="1")
        self.v_maxgap = tk.StringVar(value="300")
        self.v_naive = tk.StringVar(value=NAIVE_RULES["utc8"])
        self.v_format = tk.BooleanVar(value=True)
        self.v_indent = tk.StringVar(value="2 个空格")
        self.v_detail = tk.BooleanVar(value=True)
        self.v_report = tk.BooleanVar(value=False)
        self.v_preview = tk.BooleanVar(value=True)

        self._build_ui()
        self.root.after(80, self._poll)

    # ---------- 样式 ----------
    def _setup_style(self):
        f = self.font
        s = self.style
        # 统一背景色：根窗口、Frame、LabelFrame、按钮、复选框等全部
        # 刷成同一个灰色，避免 macOS 深色模式下出现黑色条带。
        s.configure(".", background=UI_BG, font=(f, 11))
        s.configure("TFrame", background=UI_BG)
        s.configure("TLabel", background=UI_BG)
        s.configure("Title.TLabel", font=(f, 16, "bold"), background=UI_BG)
        s.configure("Sub.TLabel", font=(f, 10), foreground="#555555",
                    background=UI_BG)
        s.configure("Warn.TLabel", font=(f, 10), foreground="#a04000",
                    background=UI_BG)
        s.configure("Status.TLabel", font=(f, 11), foreground="#333333",
                    background=UI_BG)
        s.configure("TButton", font=(f, 11), padding=6, background="#e4e4e4")
        s.map("TButton",
              background=[("pressed", "#cfcfcf"), ("active", "#eeeeee")])
        s.configure("Action.TButton", font=(f, 12, "bold"), padding=8,
                    background="#e4e4e4")
        s.map("Action.TButton",
              background=[("pressed", "#cfcfcf"), ("active", "#eeeeee")])
        s.configure("TLabelframe", background=UI_BG)
        s.configure("TLabelframe.Label", font=(f, 11, "bold"), background=UI_BG)
        s.configure("TCheckbutton", font=(f, 11), background=UI_BG)
        s.map("TCheckbutton", background=[("active", UI_BG)])
        s.configure("TCombobox", font=(f, 11), fieldbackground="#ffffff")
        s.configure("TEntry", fieldbackground="#ffffff")
        s.configure("Horizontal.TProgressbar", background="#5a9c5a",
                    troughcolor="#c3c3c3")

    # ---------- 界面 ----------
    def _build_ui(self):
        root = self.root
        root.geometry("880x720")
        root.minsize(820, 640)
        root.configure(background=UI_BG)

        head = ttk.Frame(root, padding=(18, 14, 18, 6))
        head.pack(fill=tk.X)
        ttk.Label(head, text="GPX / TCX 轨迹插值补全工具", style="Title.TLabel").pack(anchor=tk.W)
        ttk.Label(head, text="在超过阈值的采样间隔之间按等时间线性插入补全点，"
                             "用于按时间匹配照片、给照片写入 GPS 坐标。"
                             "新增点时间一律为真正的 UTC + Z。",
                  style="Sub.TLabel", wraplength=820, justify=tk.LEFT).pack(anchor=tk.W, pady=(2, 0))

        # 文件
        ff = ttk.LabelFrame(root, text=" 文件 ", padding=10)
        ff.pack(fill=tk.X, padx=18, pady=6)
        self.lbl_path = ttk.Label(ff, text="未选择文件", anchor=tk.W, wraplength=640,
                                  foreground="#666666")
        self.lbl_path.pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Button(ff, text="选择文件...", command=self.select_file).pack(side=tk.RIGHT)

        # 参数
        pf = ttk.LabelFrame(root, text=" 插值参数 ", padding=10)
        pf.pack(fill=tk.X, padx=18, pady=6)
        pf.columnconfigure(1, weight=1)

        r = 0
        ttk.Label(pf, text="插值阈值（秒）").grid(row=r, column=0, sticky=tk.W, pady=2)
        e1 = ttk.Entry(pf, textvariable=self.v_threshold, width=10)
        e1.grid(row=r, column=1, sticky=tk.W, padx=(8, 20))
        ttk.Label(pf, text="相邻两点间隔超过它才插值。照片定位误差 ≤ 阈值的一半，"
                           "要更准可调小（如 5）", style="Sub.TLabel").grid(row=r, column=2, sticky=tk.W)
        r += 1
        ttk.Label(pf, text="插入间隔（秒）").grid(row=r, column=0, sticky=tk.W, pady=2)
        e2 = ttk.Entry(pf, textvariable=self.v_interval, width=10)
        e2.grid(row=r, column=1, sticky=tk.W, padx=(8, 20))
        ttk.Label(pf, text="补点的步长，默认 1 秒", style="Sub.TLabel").grid(row=r, column=2, sticky=tk.W)
        r += 1
        ttk.Label(pf, text="最长插值间隔（秒）").grid(row=r, column=0, sticky=tk.W, pady=2)
        e3 = ttk.Entry(pf, textvariable=self.v_maxgap, width=10)
        e3.grid(row=r, column=1, sticky=tk.W, padx=(8, 20))
        ttk.Label(pf, text="超过它的区间不插值、只告警（默认 300 秒 = 5 分钟），"
                           "防止异常数据被伪造成直线", style="Sub.TLabel").grid(row=r, column=2, sticky=tk.W)
        r += 1
        ttk.Label(pf, text="无时区时间").grid(row=r, column=0, sticky=tk.W, pady=2)
        ttk.Combobox(pf, textvariable=self.v_naive, state="readonly",
                     values=list(NAIVE_RULES.values()), width=28).grid(
            row=r, column=1, sticky=tk.W, padx=(8, 20))
        ttk.Label(pf, text="文件里没有时区标记的时间按此解释", style="Sub.TLabel").grid(
            row=r, column=2, sticky=tk.W)
        r += 1
        ttk.Label(pf, text="输出格式化").grid(row=r, column=0, sticky=tk.W, pady=2)
        box = ttk.Frame(pf)
        box.grid(row=r, column=1, columnspan=2, sticky=tk.W, padx=(8, 0))
        ttk.Checkbutton(box, text="按层级缩进排版", variable=self.v_format,
                        command=self._toggle_indent).pack(side=tk.LEFT)
        self.cmb_indent = ttk.Combobox(box, textvariable=self.v_indent, state="readonly",
                                       width=12,
                                       values=["2 个空格", "4 个空格", "Tab"])
        self.cmb_indent.pack(side=tk.LEFT, padx=(12, 0))
        r += 1
        ttk.Label(pf, text="输出选项").grid(row=r, column=0, sticky=tk.W, pady=2)
        box2 = ttk.Frame(pf)
        box2.grid(row=r, column=1, columnspan=2, sticky=tk.W, padx=(8, 0))
        ttk.Checkbutton(box2, text="处理前预览确认", variable=self.v_preview).pack(side=tk.LEFT)
        ttk.Checkbutton(box2, text="控制台打印插值明细", variable=self.v_detail).pack(side=tk.LEFT, padx=(10, 0))
        ttk.Checkbutton(box2, text="另存明细报告", variable=self.v_report).pack(side=tk.LEFT, padx=(10, 0))

        self._entry_widgets = [e1, e2, e3]

        # 按钮
        bf = ttk.Frame(root)
        bf.pack(pady=(8, 4))
        self.btn_run = ttk.Button(bf, text="开始处理", style="Action.TButton",
                                  command=self.start)
        self.btn_run.pack(side=tk.LEFT, padx=10)
        self.btn_cancel = ttk.Button(bf, text="取消", style="Action.TButton",
                                     command=self.cancel, state=tk.DISABLED)
        self.btn_cancel.pack(side=tk.LEFT, padx=10)
        ttk.Button(bf, text="退出程序", style="Action.TButton",
                   command=self.do_exit).pack(side=tk.LEFT, padx=10)

        # 进度
        self.pb = ttk.Progressbar(root, mode="indeterminate")
        self.pb.pack(fill=tk.X, padx=18, pady=(6, 2))

        ttk.Label(root, textvariable=self.status_text, style="Status.TLabel").pack(
            anchor=tk.W, padx=20)

        # 日志
        lf = ttk.LabelFrame(root, text=" 处理日志 ", padding=6)
        lf.pack(fill=tk.BOTH, expand=True, padx=18, pady=(4, 12))
        self.log_box = ScrolledText(lf, height=14, wrap=tk.NONE,
                                    font=("Menlo" if sys.platform == "darwin" else "Consolas", 10),
                                    bg="#ffffff", fg="#1a1a1a",
                                    relief="flat", bd=0)
        self.log_box.pack(fill=tk.BOTH, expand=True)
        self.log_box.configure(state=tk.DISABLED)

    def _toggle_indent(self):
        self.cmb_indent.configure(state="readonly" if self.v_format.get() else tk.DISABLED)

    # ---------- 日志 ----------
    def log(self, msg):
        self.log_box.configure(state=tk.NORMAL)
        self.log_box.insert(tk.END, msg + "\n")
        self.log_box.see(tk.END)
        self.log_box.configure(state=tk.DISABLED)

    def _reset_pb(self):
        """进度条复位为来回扫动的等待动画（分析阶段用）。"""
        try:
            self.pb.stop()
        except tk.TclError:
            pass
        self.pb.config(mode="indeterminate", maximum=100, value=0)

    def set_busy(self, busy):
        self._busy = busy
        state = tk.DISABLED if busy else tk.NORMAL
        for w in [self.btn_run] + list(self._entry_widgets):
            try:
                w.config(state=state)
            except tk.TclError:
                pass
        try:
            self.btn_cancel.config(state=tk.NORMAL if busy else tk.DISABLED)
        except tk.TclError:
            pass
        if busy:
            self._reset_pb()
            self.pb.start(60)
        else:
            self.pb.stop()

    # ---------- 文件 ----------
    def select_file(self):
        path = filedialog.askopenfilename(
            title="选择 GPX 或 TCX 文件",
            filetypes=[("轨迹文件", "*.gpx *.tcx"), ("GPX 文件", "*.gpx"),
                       ("TCX 文件", "*.tcx"), ("所有文件", "*.*")])
        if path:
            self.filepath.set(path)
            self.lbl_path.config(text=path, foreground="#1a73e8")
            self.status_text.set("已选择：%s" % os.path.basename(path))

    # ---------- 主流程 ----------
    def _collect_opts(self):
        opts = Options(
            gap_threshold=float(self.v_threshold.get()),
            interval=float(self.v_interval.get()),
            max_gap=float(self.v_maxgap.get()),
            naive_rule={v: k for k, v in NAIVE_RULES.items()}[self.v_naive.get()],
            format_output=self.v_format.get(),
            indent={"2 个空格": "  ", "4 个空格": "    ", "Tab": "\t"}[self.v_indent.get()],
            print_detail=self.v_detail.get(),
            write_report=self.v_report.get())
        opts.validate()
        return opts

    def start(self):
        path = self.filepath.get()
        if not path:
            messagebox.showwarning("提示", "请先选择一个 GPX 或 TCX 文件！")
            return
        if not os.path.isfile(path):
            messagebox.showerror("错误", "所选文件不存在！")
            return
        try:
            self.opts = self._collect_opts()
        except ValueError as e:
            messagebox.showerror("参数有误", str(e))
            return

        self._cancel = False
        self.set_busy(True)
        self.status_text.set("正在分析...")
        self.log_box.configure(state=tk.NORMAL)
        self.log_box.delete("1.0", tk.END)
        self.log_box.configure(state=tk.DISABLED)
        self.log("=== 开始：%s ===" % os.path.basename(path))
        self.log("参数：%s" % self.opts.describe())
        t = threading.Thread(target=self._worker_analyze, daemon=True)
        t.start()

    def _worker_analyze(self):
        try:
            ana = analyze_file(self.filepath.get(), self.opts,
                               log=lambda m: self._q.put(("log", m)))
            self._q.put(("analysis", ana))
        except Exception as e:
            self._q.put(("error", (str(e), traceback.format_exc())))

    def _worker_write(self, ana):
        try:
            self._q.put(("log", build_summary(ana, self.opts)))
            out = apply_and_write(ana, self.opts,
                                  log=lambda m: self._q.put(("log", m)),
                                  should_cancel=lambda: self._cancel,
                                  progress=lambda done, total:
                                      self._q.put(("progress", done)))
            if self.opts.write_report:
                rep = os.path.splitext(out)[0] + "_插值明细.txt"
                with open(rep, "w", encoding="utf-8") as f:
                    f.write(build_detail_report(ana, self.opts, out))
                self._q.put(("log", "明细报告：%s" % rep))
            if self.opts.print_detail:
                sys.stdout.write("\n" + build_detail_report(ana, self.opts, out) + "\n")
                sys.stdout.flush()
            ana.opts_naive_rule = self.opts.naive_rule
            v = verify_output(out, ana)
            self._q.put(("done", (out, v)))
        except KeyboardInterrupt:
            self._q.put(("cancelled", None))
        except Exception as e:
            self._q.put(("error", (str(e), traceback.format_exc())))

    def cancel(self):
        self._cancel = True
        self.status_text.set("正在取消...")

    # ---------- 队列轮询 ----------
    def _poll(self):
        try:
            while True:
                kind, payload = self._q.get_nowait()
                if kind == "log":
                    self.log(payload)
                elif kind == "progress":
                    try:
                        self.pb.config(value=payload)
                    except tk.TclError:
                        pass
                elif kind == "analysis":
                    self._on_analysis(payload)
                elif kind == "done":
                    self._on_done(*payload)
                elif kind == "cancelled":
                    self._reset_pb()
                    self.set_busy(False)
                    self.status_text.set("已取消")
                    self.log("已取消，未写出文件。")
                elif kind == "error":
                    msg, tb = payload
                    self._reset_pb()
                    self.set_busy(False)
                    self.status_text.set("失败：%s" % msg)
                    self.log("!! 出错：%s" % msg)
                    self.log(tb)
                    messagebox.showerror("处理出错", msg)
        except queue.Empty:
            pass
        self.root.after(80, self._poll)

    def _on_analysis(self, ana):
        self.ana = ana
        if ana.points_total == 0:
            self._reset_pb()
            self.set_busy(False)
            self.status_text.set("失败：文件里没有有效的轨迹点")
            self.log("文件中没有有效的轨迹点，未生成文件。")
            messagebox.showerror("无数据", "文件中没有有效的轨迹点。")
            return

        if not ana.plan:
            self._reset_pb()
            self.set_busy(False)
            self.log(build_summary(ana, self.opts))
            self.status_text.set("完成：没有需要插值的区间")
            messagebox.showinfo(
                "无需插值",
                "%s\n\n所有相邻点间隔都不超过 %.0f 秒，没有需要补全的区间。\n未生成文件。"
                % (build_summary(ana, self.opts), self.opts.gap_threshold))
            return

        if self.v_preview.get():
            self.log("--- 预览 ---")
            self.log(build_preview(ana, self.opts))
            ok = messagebox.askyesno(
                "处理前确认",
                build_preview(ana, self.opts) + "\n\n是否继续写出文件？")
            if not ok:
                self._reset_pb()
                self.set_busy(False)
                self.status_text.set("已取消（预览未确认）")
                self.log("预览未确认，未写出文件。")
                return

        # 写出阶段切换为确定性进度条：按实际插入点数从 0 走到 100%
        self.pb.stop()
        self.pb.config(mode="determinate",
                       maximum=max(ana.inserted, 1), value=0)
        self.status_text.set("正在插入补全点...")
        threading.Thread(target=self._worker_write, args=(ana,), daemon=True).start()

    def _on_done(self, out, v):
        self.set_busy(False)
        # 让进度条走满再停，视觉上「走完了」而不是中途消失
        try:
            self.pb.config(value=self.pb["maximum"])
        except tk.TclError:
            pass
        self.status_text.set("完成 → %s" % os.path.basename(out))
        self.log("- - - - - - - - - - - - - - - - - - - - - - - - - - - - - -")
        self.log("回读校验：%d 点（应为 %d），原始点缺失 %d，"
                 "插值后最大间隔 %.1fs" % (v["points"], v["expected"],
                                        v["missing"], v["max_gap"]))
        if v["time_min"]:
            self.log("时间范围：%s → %s"
                     % (v["time_min"].strftime("%Y-%m-%dT%H:%M:%SZ"),
                        v["time_max"].strftime("%Y-%m-%dT%H:%M:%SZ")))
            self.log("北京时间：%s → %s"
                     % (to_beijing(v["time_min"]).strftime("%Y-%m-%d %H:%M:%S"),
                        to_beijing(v["time_max"]).strftime("%Y-%m-%d %H:%M:%S")))
        messagebox.showinfo(
            "处理完成",
            "插入 %d 个补全点，共 %d 点。\n\n输出文件：\n%s\n\n"
            "原始文件未做任何改动。" % (self.ana.inserted, v["points"], out))

    def do_exit(self):
        if self._busy:
            if not messagebox.askyesno("确认", "正在处理中，确定要退出吗？"):
                return
        if messagebox.askyesno("确认", "确定要退出程序吗？"):
            self.root.destroy()


# ══════════════════════════════════════════════════════════════
# 入口
# ══════════════════════════════════════════════════════════════

def main():
    if len(sys.argv) > 1:
        p = argparse.ArgumentParser(
            description="GPX/TCX 轨迹插值补全工具 %s。不带参数运行则打开图形界面。"
                        % APP_VERSION)
        p.add_argument("file", help="GPX 或 TCX 文件路径")
        p.add_argument("--preview", action="store_true",
                       help="只分析并打印统计，不写出文件")
        p.add_argument("--threshold", type=float, default=DEFAULTS["gap_threshold"],
                       help="插值阈值（秒），默认 %g" % DEFAULTS["gap_threshold"])
        p.add_argument("--interval", type=float, default=DEFAULTS["interval"],
                       help="插入间隔（秒），默认 %g" % DEFAULTS["interval"])
        p.add_argument("--max-gap", type=float, default=DEFAULTS["max_gap"], dest="max_gap",
                       help="最长插值间隔（秒），默认 %g" % DEFAULTS["max_gap"])
        p.add_argument("--naive", choices=list(NAIVE_RULES), default="utc8",
                       help="无时区时间的解释口径")
        p.add_argument("--no-format", action="store_true", help="不做缩进排版")
        p.add_argument("--quiet", action="store_true", help="不打印逐点明细")
        p.add_argument("--report", action="store_true", help="另存插值明细报告")
        ns = p.parse_args()
        return cli_main(ns)

    root = tk.Tk()
    App(root)
    root.mainloop()
    return 0


if __name__ == "__main__":
    sys.exit(main())
