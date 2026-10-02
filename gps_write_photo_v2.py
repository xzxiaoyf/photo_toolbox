#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
GPS轨迹写入照片/视频工具 (修复版 v2)
================================================================
用途
----
用轨迹文件（GPX / TCX / FIT）按拍摄时间给照片、视频匹配并写入 GPS。
轨迹请使用前序工具处理过的文件（时间修正 / 插值补全后的真 UTC 文件）。
**没有匹配上就不写入**，宁可留空也不写错位置。

相对原版的关键修复（每一条都实机复现过）
----------------------------------------
[P0-1] 纯标准库，去掉了 gpxpy / fitparse 依赖。
       原版在你机器上启动即弹「缺少gpxpy」退出（6 个 Python 全没装、也无 pip3）。
       现在 GPX/TCX 自己解析；FIT 无 fitparse 时给出明确提示。
[P0-2] 轨迹时间一律按「真 UTC」解释（前序插值/修正工具的输出就是真 UTC+Z）。
       文件里带数字偏移（+08:00 等）时仍按偏移真换算，不受影响。
       （小米原始导出的伪 Z 文件请先用前序工具修正，本工具不再提供口径切换，
       避免不懂的人选错。）
[P0-3] 时间偏移真换算。原版正则把 +08:00 整段剥掉只用墙钟（实测误差 8 小时），
       现在带偏移的时间按偏移换算成真 UTC。
[P1-4] 小米 TCX 海拔修复。<AltitudeMeters> 嵌在 <Position> 内部（实测 2478 点
       原版读到 0 个海拔），现在两种布局都读。
[P1-5] 负海拔修复。实测 exiftool 13.25：数字 -GPSAltitudeRef=1 静默无效、
       负值会被写成正数；且 Ref 会残留。改用字符串 "Above/Below Sea Level"
       并总是显式写 Ref，实测正负海拔落盘都正确。
[P1-6] 视频（mp4/mov 等）支持 + 全部诊断进 GUI 日志区。
       pyinstaller -F 打包后没有控制台，原版所有 print 都看不见。
       实测：视频时间读 -api QuickTimeUTC（返回带 +08:00 偏移的本地时间）；
       视频写 GPS 用 Keys:GPSCoordinates="lat lon"（该格式不含海拔，实测如此）。
[P1-7] 每个文件的处理结果都输出到日志区；结束统计写入/未写入数量。
[P2-8] 可选备份：写入前把原文件复制到同目录 exif_backup/（Finder 可见）。
[P2-9] 解析在后台线程，界面不冻；进度条按真实文件数走满；可取消。
[P2-10] 统一灰色界面配色 + 跨平台中文字体。

依赖
----
- 纯 Python 标准库（无需 pip 安装任何东西）
- 外部命令 exiftool（https://exiftool.org/）

运行
----
    python3 gps_write_photo_v2.py                    # 图形界面
    python3 gps_write_photo_v2.py 轨迹.gpx 照片目录   # 命令行处理
#  pyinstaller -F gps_write_photo_v2.py
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from tkinter.scrolledtext import ScrolledText
import subprocess
import json
import os
import sys
import re
import shutil
import argparse
import queue as queue_mod
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
import threading

# ===================== 配置区 =====================
PHOTO_EXTENSIONS = {
    '.jpg', '.jpeg', '.png', '.tiff', '.tif',
    '.heic', '.heif','.hif', '.raw', '.cr2', '.cr3',
    '.nef', '.arw', '.dng', '.orf', '.rw2', '.sr2'
}

VIDEO_EXTENSIONS = {
    '.mp4', '.mov', '.m4v', '.avi', '.3gp', '.mkv', '.mts', '.m2ts'
}

#: 照片缺省时区补偿（小时）：相机本地时间(北京 UTC+8) → UTC
DEFAULT_TZ_HOURS = 8

#: 匹配容差（秒）：照片与最近轨迹点超过它就不写入
DEFAULT_TOLERANCE = 30.0

#: 轨迹时间口径：一律按真 UTC 解释（前序工具负责把轨迹修正成真 UTC+Z）

#: 备份目录名（放在媒体文件所在目录下，Finder 可见、无点前缀）
BACKUP_DIRNAME = "exif_backup"

APP_TITLE = "GPS轨迹写入照片/视频工具"
APP_VERSION = "v2.1"

#: 统一界面背景色（macOS 深色模式下 Tk 根窗口默认发黑，必须统一刷灰）
UI_BG = "#d9d9d9"


# ============================================================
# 通用小工具
# ============================================================
def local_name(tag):
    return tag.split('}')[-1] if isinstance(tag, str) else ''


def first_child_named(el, name):
    for c in el:
        if isinstance(c.tag, str) and local_name(c.tag) == name:
            return c
    return None


def text_of(el):
    return el.text.strip() if el is not None and el.text else None


def pick_font(root):
    """跨平台挑一个可用的中文字体。"""
    try:
        fonts = set(root.tk.call('font', 'families'))
    except tk.TclError:
        fonts = set()
    for name in ["PingFang SC", "Hiragino Sans GB", "Microsoft YaHei UI",
                 "Microsoft YaHei", "Noto Sans CJK SC", "SimHei", "WenQuanYi Zen Hei"]:
        if name in fonts:
            return name
    return "TkDefaultFont"


def unique_path(path):
    """重名时自动加序号，绝不覆盖已有文件。"""
    if not os.path.exists(path):
        return path
    base, ext = os.path.splitext(path)
    n = 2
    while True:
        cand = "%s_%d%s" % (base, n, ext)
        if not os.path.exists(cand):
            return cand
        n += 1


# ============================================================
# 时间解析（轨迹）
# ============================================================
#: 兼容：T/空格分隔、缺秒位、任意位小数秒、Z/z、±HH[:MM|MM]
TIME_RE = re.compile(
    r"^\s*(?P<y>\d{4})-(?P<mo>\d{2})-(?P<d>\d{2})[Tt ]+"
    r"(?P<h>\d{2}):(?P<mi>\d{2})"
    r"(?::(?P<s>\d{2})(?:[.,](?P<frac>\d+))?)?\s*"
    r"(?P<tz>[Zz]|[+-]\d{2}(?::?\d{2})?)?\s*$")


def _tz_from_token(token):
    """'Z' → utc；'+08:00'/'-0500'/'-05' → 对应 timezone；None/'' → None。"""
    if not token:
        return None
    if token in ("Z", "z"):
        return timezone.utc
    sign = 1 if token[0] == '+' else -1
    body = token[1:].replace(":", "")
    hours = int(body[:2])
    minutes = int(body[2:4]) if len(body) >= 4 else 0
    return timezone(sign * timedelta(hours=hours, minutes=minutes))


def parse_iso_time(text, naive_rule="utc8"):
    """解析 ISO 8601 时间 → **naive UTC** datetime。

    带偏移的时间（+08:00 等）按偏移**真换算**成 UTC（原版是直接丢掉偏移）；
    不带时区的时间按 naive_rule 解释：
      utc8 = 北京墙钟（小米口径）  utc = 已是 UTC  local = 本机时区
    解析失败返回 None。
    """
    if not text:
        return None
    m = TIME_RE.match(text)
    if not m:
        return None
    try:
        dt = datetime(int(m.group('y')), int(m.group('mo')), int(m.group('d')),
                      int(m.group('h')), int(m.group('mi')),
                      int(m.group('s') or 0),
                      microsecond=int((m.group('frac') or '0')[:6].ljust(6, '0')))
    except ValueError:
        return None
    tz = _tz_from_token(m.group('tz'))
    if tz is not None:
        return dt.replace(tzinfo=tz).astimezone(timezone.utc).replace(tzinfo=None)
    if naive_rule == "utc":
        return dt
    if naive_rule == "utc8":
        return dt - timedelta(hours=DEFAULT_TZ_HOURS)
    return dt - (datetime.now() - datetime.utcnow())


def parse_wall_time(text):
    """把轨迹文件里的时间文本换成真 UTC naive datetime。

    Z / 无后缀 → 当作真 UTC（前序工具修正版就是真 UTC+Z）；
    数字偏移（+08:00 / -0500）→ 相信文件，按偏移真换算。
    """
    if not text:
        return None
    m = TIME_RE.match(text)
    if not m:
        return None
    try:
        dt = datetime(int(m.group('y')), int(m.group('mo')), int(m.group('d')),
                      int(m.group('h')), int(m.group('mi')),
                      int(m.group('s') or 0),
                      microsecond=int((m.group('frac') or '0')[:6].ljust(6, '0')))
    except ValueError:
        return None
    token = m.group('tz')
    if token is not None and token not in ("Z", "z"):
        # 数字偏移（+08:00 / -0500）：相信文件，真换算
        return (dt.replace(tzinfo=_tz_from_token(token))
                  .astimezone(timezone.utc).replace(tzinfo=None))
    return dt                                # 真 UTC（或无后缀当 UTC）


# ============================================================
# 轨迹解析（纯标准库）
# ============================================================
class GpsPoint(object):
    __slots__ = ("lat", "lon", "ele", "time")

    def __init__(self, lat, lon, ele=None, time=None):
        self.lat = lat
        self.lon = lon
        self.ele = ele
        self.time = time          # naive UTC

    def __repr__(self):
        return ("GPS(%.6f,%.6f,ele=%s,time=%s)"
                % (self.lat, self.lon, self.ele, self.time))


class FitNotSupported(Exception):
    pass


def parse_gpx_points(path):
    """纯标准库解析 GPX：trkpt / rtept / wpt。"""
    root = ET.parse(path).getroot()
    points = []
    for el in root.iter():
        if local_name(el.tag) not in ("trkpt", "rtept", "wpt"):
            continue
        try:
            lat = float(el.get("lat"))
            lon = float(el.get("lon"))
        except (TypeError, ValueError):
            continue
        ele = t = None
        for c in el:
            n = local_name(c.tag)
            if n == "ele" and c.text:
                try:
                    ele = float(c.text.strip())
                except ValueError:
                    pass
            elif n == "time" and c.text:
                t = parse_wall_time(c.text)
        points.append(GpsPoint(lat, lon, ele, t))
    return points


def parse_tcx_points(path):
    """纯标准库解析 TCX。小米把 <AltitudeMeters> 嵌在 <Position> 内，
    两种布局都读。"""
    root = ET.parse(path).getroot()
    points = []
    for tp in root.iter():
        if local_name(tp.tag) != "Trackpoint":
            continue
        lat = lon = ele = t = None
        pos = first_child_named(tp, "Position")
        if pos is not None:
            a = text_of(first_child_named(pos, "LatitudeDegrees"))
            b = text_of(first_child_named(pos, "LongitudeDegrees"))
            try:
                lat = float(a) if a else None
                lon = float(b) if b else None
            except ValueError:
                lat = lon = None
            # 布局一：海拔嵌在 Position 里（小米）
            a = text_of(first_child_named(pos, "AltitudeMeters"))
            if a:
                try:
                    ele = float(a)
                except ValueError:
                    pass
        # 布局二：海拔是 Trackpoint 直接子元素（标准 TCX）
        a = text_of(first_child_named(tp, "AltitudeMeters"))
        if a:
            try:
                ele = float(a)
            except ValueError:
                pass
        a = text_of(first_child_named(tp, "Time"))
        if a:
            t = parse_wall_time(a)
        if lat is not None and lon is not None:
            points.append(GpsPoint(lat, lon, ele, t))
    return points


def parse_fit_points(path):
    """FIT：有 fitparse 就用；没有则明确报错（请转 GPX/TCX）。"""
    try:
        from fitparse import FitFile
    except ImportError:
        raise FitNotSupported(
            "本机没有 fitparse，无法解析 FIT 文件。\n"
            "请改用 GPX / TCX 轨迹（小米健康导出 GPX/TCX 即可）。")
    points = []
    fitfile = FitFile(path)
    for record in fitfile.get_messages('record'):
        data = record.get_values()
        lat = data.get('position_lat')
        lon = data.get('position_long')
        if lat is None or lon is None:
            continue
        lat_deg = lat * (180.0 / 2 ** 31)
        lon_deg = lon * (180.0 / 2 ** 31)
        ele = data.get('altitude')
        t = data.get('timestamp')
        if hasattr(t, 'utcoffset') and t.utcoffset() is not None:
            t = t.astimezone(timezone.utc).replace(tzinfo=None)
        elif isinstance(t, str):
            t = parse_iso_time(t)
        points.append(GpsPoint(lat_deg, lon_deg, ele, t))
    return points


def sniff_format(path):
    """按扩展名 + 文件头判断轨迹格式。"""
    ext = os.path.splitext(path)[1].lower()
    if ext == '.gpx':
        return 'gpx'
    if ext == '.tcx':
        return 'tcx'
    if ext == '.fit':
        return 'fit'
    try:
        with open(path, 'rb') as f:
            head = f.read(2048).decode('utf-8', 'replace').lower()
    except OSError:
        head = ''
    if 'trainingcenterdatabase' in head or '<activity' in head:
        return 'tcx'
    if '<gpx' in head:
        return 'gpx'
    if head.startswith('.fit') or ext == '.fit':
        return 'fit'
    return None


def load_track(path, log=None):
    """加载轨迹 → (points, info)。points 的 time 全部为 naive UTC。"""
    log = log or (lambda m: None)
    fmt = sniff_format(path)
    log("轨迹格式：%s" % (fmt or "无法识别"))
    if fmt == 'gpx':
        points = parse_gpx_points(path)
    elif fmt == 'tcx':
        points = parse_tcx_points(path)
    elif fmt == 'fit':
        points = parse_fit_points(path)
    else:
        raise ValueError("无法识别的轨迹文件：%s" % os.path.basename(path))

    info = {"fmt": fmt, "total": len(points)}
    times = [p.time for p in points if p.time is not None]
    info["with_time"] = len(times)
    info["no_time"] = len(points) - len(times)
    info["t_min"] = min(times) if times else None
    info["t_max"] = max(times) if times else None
    info["dup_times"] = len(times) - len(set(times))
    info["with_ele"] = sum(1 for p in points if p.ele is not None)
    return points, info


def find_nearest(photo_utc, points):
    """返回 (最近点, 差秒数)。不做容差判断，由调用方决定。"""
    best, best_diff = None, None
    for pt in points:
        if pt.time is None:
            continue
        diff = abs((photo_utc - pt.time).total_seconds())
        if best_diff is None or diff < best_diff:
            best, best_diff = pt, diff
    return best, best_diff


# ============================================================
# exiftool 层
# ============================================================
def find_exiftool():
    """编译版/Finder 双击启动时 PATH 常缺 /opt/homebrew/bin 等目录，
    PATH 找不到就按常见安装位置兜底，最后问登录 shell。"""
    exe = shutil.which("exiftool")
    if exe:
        return exe
    cands = [
        "/opt/homebrew/bin/exiftool",        # Apple Silicon Homebrew
        "/usr/local/bin/exiftool",           # Intel Homebrew / 官方 pkg
        "/opt/local/bin/exiftool",           # MacPorts
        "/usr/bin/exiftool",
        "/Applications/exiftool/exiftool",   # 官方 dmg 放进应用程序
        os.path.expanduser("~/bin/exiftool"),
        r"C:\Program Files\exiftool\exiftool.exe",
        r"C:\exiftool\exiftool.exe",
    ]
    for p in cands:
        if os.path.isfile(p) and os.access(p, os.X_OK):
            return p
    if sys.platform == "darwin":
        try:
            out = subprocess.run(["/bin/zsh", "-lc", "command -v exiftool"],
                                 capture_output=True, text=True, timeout=5)
            p = out.stdout.strip()
            if p and os.path.isfile(p) and os.access(p, os.X_OK):
                return p
        except Exception:
            pass
    return None


EXIFTOOL = find_exiftool() or "exiftool"   # 找不到保持原名，行为同旧版


def exiftool_ok():
    try:
        proc = subprocess.run([EXIFTOOL, "-ver"], capture_output=True, timeout=5)
        return proc.returncode == 0, proc.stdout.decode().strip()
    except (FileNotFoundError, subprocess.TimeoutExpired, OSError):
        return False, None


def _run_exiftool(args, timeout=30):
    return subprocess.run([EXIFTOOL] + args, capture_output=True,
                          text=True, encoding="utf-8", timeout=timeout)


def _parse_media_dt(s):
    """解析 exiftool 返回的时间字符串 → naive 本地时间。

    照片：'2026:09:26 09:36:02'（无时区，本地）
    视频（QuickTimeUTC）：'2026:09:26 09:36:02+08:00'（带偏移）
    返回 (naive_local, tzinfo_or_None)。
    """
    s = str(s).strip()
    m = re.match(r"^(\d{4}[:-]\d{2}[:-]\d{2})[ T]"
                 r"(\d{2}:\d{2}:\d{2})(?:[.,]\d+)?"
                 r"\s*(?P<tz>[+-]\d{2}:?\d{2}|Z)?$", s)
    if m:
        base = m.group(1).replace('-', ':') + " " + m.group(2)
        try:
            dt = datetime.strptime(base, "%Y:%m:%d %H:%M:%S")
        except ValueError:
            return None, None
        tz = _tz_from_token(m.group('tz'))
        return dt, tz
    for fmt in ("%Y:%m:%d %H:%M:%S", "%Y-%m-%d %H:%M:%S"):
        try:
            return datetime.strptime(s, fmt), None
        except ValueError:
            continue
    return None, None


def read_media_info(path, is_video):
    """读取媒体拍摄时间与已有 GPS。

    返回 dict: local_time(naive本地), has_gps, lat, lon, ele, error
    """
    args = ["-json", "-n",
            "-DateTimeOriginal", "-CreateDate",
            "-GPSLatitude", "-GPSLongitude", "-GPSAltitude"]
    if is_video:
        args = ["-api", "QuickTimeUTC"] + args
    args.append(path)
    try:
        proc = _run_exiftool(args, timeout=15)
    except subprocess.TimeoutExpired:
        return {"error": "exiftool 读取超时"}
    except OSError as e:
        return {"error": "exiftool 调用失败：%s" % e}
    if proc.returncode != 0:
        return {"error": "exiftool 返回码 %d" % proc.returncode}
    try:
        data = json.loads(proc.stdout)
    except ValueError:
        return {"error": "exiftool 输出无法解析"}
    if not data:
        return {"error": "exiftool 无输出"}
    info = data[0]
    if info.get("Error"):
        return {"error": str(info["Error"])}

    res = {"local_time": None, "has_gps": False,
           "lat": None, "lon": None, "ele": None, "error": None,
           "time_raw": None, "time_is_utc": False}

    ds = info.get("DateTimeOriginal") or info.get("CreateDate")
    if ds:
        res["time_raw"] = str(ds)
        local, tz = _parse_media_dt(ds)
        if local is not None and tz is not None:
            # 视频返回带偏移的时间：换算成本地墙钟展示、时间本身按 UTC 用
            res["local_time"] = local
            res["utc_time"] = local.replace(tzinfo=tz).astimezone(
                timezone.utc).replace(tzinfo=None)
            res["time_is_utc"] = True
        else:
            res["local_time"] = local

    glat, glon = info.get("GPSLatitude"), info.get("GPSLongitude")
    if glat is not None and glon is not None:
        try:
            la, lo = float(glat), float(glon)
            if la != 0 or lo != 0:
                res["has_gps"] = True
                res["lat"], res["lon"] = la, lo
        except (TypeError, ValueError):
            pass
    ga = info.get("GPSAltitude")
    if ga is not None:
        try:
            res["ele"] = float(ga)
        except (TypeError, ValueError):
            pass
    return res


def make_backup(path, log):
    """写入前备份到媒体目录下可见的 exif_backup/（不覆盖已有备份）。"""
    folder = os.path.join(os.path.dirname(path) or ".", BACKUP_DIRNAME)
    try:
        os.makedirs(folder, exist_ok=True)
        target = unique_path(os.path.join(folder, os.path.basename(path)))
        shutil.copy2(path, target)
        return True, target
    except OSError as e:
        log("⚠ 备份失败（继续写入）：%s" % e)
        return False, None


def write_gps(path, gps_pt, is_video, backup, log):
    """写入 GPS。返回 (ok, message)。

    实测要点（exiftool 13.25）：
    - 照片：GPSAltitudeRef 必须写字符串 "Above/Below Sea Level"，
      数字 1 会静默无效、负海拔会被写成正数；Ref 会残留，必须总是显式写。
    - 视频：Keys:GPSCoordinates 只接受 "lat lon" 两段（不带海拔）。
    """
    lat, lon = gps_pt.lat, gps_pt.lon
    try:
        if is_video:
            coord = "%.6f %.6f" % (lat, lon)
            cmd = ["-overwrite_original", "-Keys:GPSCoordinates=%s" % coord]
        else:
            cmd = ["-overwrite_original",
                   "-GPSLatitude=%.6f" % abs(lat),
                   "-GPSLatitudeRef=%s" % ("N" if lat >= 0 else "S"),
                   "-GPSLongitude=%.6f" % abs(lon),
                   "-GPSLongitudeRef=%s" % ("E" if lon >= 0 else "W")]
            if gps_pt.ele is not None:
                cmd += ["-GPSAltitude=%.1f" % abs(gps_pt.ele),
                        "-GPSAltitudeRef=%s"
                        % ("Above Sea Level" if gps_pt.ele >= 0 else "Below Sea Level")]

        if backup:
            ok, target = make_backup(path, log)
            if ok:
                log("      （已备份 → %s）"
                    % os.path.relpath(target, os.path.dirname(path)))
        cmd.append(path)
        proc = _run_exiftool(cmd, timeout=60)
        if proc.returncode == 0 and "error" not in proc.stdout.lower():
            if "1 image files updated" in proc.stdout:
                return True, "已写入"
            if "nothing to do" in proc.stdout.lower():
                return False, "exiftool 无改动（%s）" % proc.stdout.strip()
            return True, proc.stdout.strip() or "已写入"
        msg = proc.stderr.strip() or proc.stdout.strip() or ("返回码 %d" % proc.returncode)
        return False, msg
    except subprocess.TimeoutExpired:
        return False, "exiftool 写入超时"
    except OSError as e:
        return False, "exiftool 调用失败：%s" % e


# ============================================================
# 处理核心（GUI 与 CLI 共用）
# ============================================================
class Stats(object):
    def __init__(self):
        self.total = 0
        self.written = 0
        self.not_written = 0
        self.no_match = 0
        self.no_time = 0
        self.skipped_existing = 0
        self.errors = 0


def process_media(path, is_video, points, tolerance, tz_hours,
                  overwrite, backup, stats, log, should_cancel=None):
    """处理单个媒体文件。返回状态字符串。"""
    name = os.path.basename(path)
    info = read_media_info(path, is_video)
    if info.get("error"):
        stats.not_written += 1
        stats.errors += 1
        log("    ✗ 读取失败：%s" % info["error"])
        return "error"

    kind = "视频" if is_video else "照片"
    if info["local_time"] is None:
        stats.not_written += 1
        stats.no_time += 1
        log("    ✗ 未写入（%s无拍摄时间）" % kind)
        return "no_time"

    lt = info["local_time"]
    log("    拍摄时间（本地）：%s" % lt.strftime("%Y-%m-%d %H:%M:%S"))

    # 本地时间 → UTC。视频 QuickTimeUTC 已给出带偏移的时间，直接用换算结果。
    if info.get("time_is_utc") and info.get("utc_time") is not None:
        photo_utc = info["utc_time"]
    else:
        photo_utc = lt - timedelta(hours=tz_hours)

    gps_pt, diff = find_nearest(photo_utc, points)
    if gps_pt is None or diff > tolerance:
        near = ("最近轨迹点相差 %.1fs，超过容差 %.0fs" % (diff, tolerance)
                if gps_pt is not None else "轨迹点全部没有时间戳")
        stats.not_written += 1
        stats.no_match += 1
        log("    ✗ 未写入（无匹配：%s）" % near)
        return "no_match"

    ele_s = "%.1fm" % gps_pt.ele if gps_pt.ele is not None else "无海拔"
    match_s = "%.6f, %.6f" % (gps_pt.lat, gps_pt.lon)
    if info["has_gps"] and not overwrite:
        stats.not_written += 1
        stats.skipped_existing += 1
        log("    ⊘ 未写入（已有 GPS，不覆盖模式）")
        log("      原GPS: %.6f, %.6f" % (info["lat"], info["lon"]))
        log("      轨迹(Δ%.1fs): %s  海拔:%s" % (diff, match_s, ele_s))
        return "skip_existing"

    ok, msg = write_gps(path, gps_pt, is_video, backup, log)
    if ok:
        stats.written += 1
        log("    ✓ 已写入 GPS  Δ%.1fs  %s  海拔:%s" % (diff, match_s, ele_s))
        if info["has_gps"]:
            log("      （覆盖原 GPS: %.6f, %.6f）" % (info["lat"], info["lon"]))
        return "written"
    stats.not_written += 1
    stats.errors += 1
    log("    ✗ 写入失败：%s" % msg)
    return "error"


# ============================================================
# GUI
# ============================================================
class GpsWriterApp(object):
    def __init__(self, root):
        self.root = root
        self.root.title("%s %s" % (APP_TITLE, APP_VERSION))
        self.font = pick_font(root)
        self._busy = False
        self._cancel = False
        self._q = queue_mod.Queue()

        self.gps_file_path = ""
        self.photo_dir = ""
        self.gps_points = []
        self.track_info = None

        self._setup_style()
        self._build_ui()
        self.root.after(80, self._poll)

    # ---------- 样式 ----------
    def _setup_style(self):
        self.style = ttk.Style()
        try:
            self.style.theme_use("clam")
        except tk.TclError:
            pass
        f = self.font
        s = self.style
        s.configure(".", background=UI_BG, font=(f, 11))
        s.configure("TFrame", background=UI_BG)
        s.configure("TLabel", background=UI_BG)
        s.configure("Sub.TLabel", font=(f, 10), foreground="#555555",
                    background=UI_BG)
        s.configure("TButton", font=(f, 11), padding=6, background="#e4e4e4")
        s.map("TButton",
              background=[("pressed", "#cfcfcf"), ("active", "#eeeeee")])
        s.configure("TLabelframe", background=UI_BG)
        s.configure("TLabelframe.Label", font=(f, 11, "bold"), background=UI_BG)
        s.configure("TRadiobutton", font=(f, 11), background=UI_BG)
        s.map("TRadiobutton", background=[("active", UI_BG)])
        s.configure("TCheckbutton", font=(f, 11), background=UI_BG)
        s.map("TCheckbutton", background=[("active", UI_BG)])
        s.configure("TEntry", fieldbackground="#ffffff")
        s.configure("TCombobox", font=(f, 11), fieldbackground="#ffffff")
        s.configure("Horizontal.TProgressbar", background="#5a9c5a",
                    troughcolor="#c3c3c3")

    # ---------- 界面 ----------
    def _build_ui(self):
        root = self.root
        root.geometry("860x760")
        root.minsize(820, 660)
        root.configure(background=UI_BG)

        head = ttk.Frame(root, padding=(16, 12, 16, 4))
        head.pack(fill=tk.X)
        ttk.Label(head, text="GPS 轨迹写入照片/视频", style="Title.TLabel").pack(anchor=tk.W)
        ttk.Label(head, text="按拍摄时间匹配轨迹点并写入 GPS。轨迹请用前序工具"
                             "处理过的文件；没有匹配上的文件一律不写入。",
                  style="Sub.TLabel", wraplength=800, justify=tk.LEFT).pack(anchor=tk.W)

        # ① 轨迹
        r1 = ttk.LabelFrame(root, text=" ① GPS轨迹文件 ", padding=8)
        r1.pack(fill=tk.X, padx=16, pady=5)
        ttk.Button(r1, text="选择轨迹文件...", command=self._select_gps_file).pack(side=tk.LEFT)
        self.gps_file_var = tk.StringVar(value="未选择")
        ttk.Label(r1, textvariable=self.gps_file_var, foreground="#555555",
                  wraplength=600, background=UI_BG).pack(
            side=tk.LEFT, padx=(10, 0), fill=tk.X, expand=True)

        # ② 媒体目录
        r2 = ttk.LabelFrame(root, text=" ② 照片/视频目录 ", padding=8)
        r2.pack(fill=tk.X, padx=16, pady=5)
        ttk.Button(r2, text="选择媒体目录...", command=self._select_media_dir).pack(side=tk.LEFT)
        self.media_dir_var = tk.StringVar(value="未选择")
        ttk.Label(r2, textvariable=self.media_dir_var, foreground="#555555",
                  wraplength=600, background=UI_BG).pack(
            side=tk.LEFT, padx=(10, 0), fill=tk.X, expand=True)

        # ③ 选项
        r3 = ttk.LabelFrame(root, text=" ③ 匹配与写入选项 ", padding=8)
        r3.pack(fill=tk.X, padx=16, pady=5)
        grid = ttk.Frame(r3)
        grid.pack(fill=tk.X)
        grid.columnconfigure(1, weight=1)

        ttk.Label(grid, text="匹配容差（秒）").grid(row=0, column=0, sticky=tk.W, pady=2)
        self.v_tolerance = tk.StringVar(value="%g" % DEFAULT_TOLERANCE)
        e1 = ttk.Entry(grid, textvariable=self.v_tolerance, width=10)
        e1.grid(row=0, column=1, sticky=tk.W, padx=(8, 20))
        ttk.Label(grid, text="照片与最近轨迹点相差超过它就不写入", style="Sub.TLabel").grid(
            row=0, column=2, sticky=tk.W)

        ttk.Label(grid, text="照片时区（小时）").grid(row=1, column=0, sticky=tk.W, pady=2)
        self.v_tz = tk.StringVar(value="%g" % DEFAULT_TZ_HOURS)
        e2 = ttk.Entry(grid, textvariable=self.v_tz, width=10)
        e2.grid(row=1, column=1, sticky=tk.W, padx=(8, 20))
        ttk.Label(grid, text="相机本地时间 = UTC+8 就填 8", style="Sub.TLabel").grid(
            row=1, column=2, sticky=tk.W)

        self.v_overwrite = tk.BooleanVar(value=False)
        ttk.Checkbutton(grid, text="覆盖已有 GPS 信息（默认跳过已有 GPS 的文件）",
                        variable=self.v_overwrite).grid(
            row=2, column=0, columnspan=3, sticky=tk.W, pady=(4, 0))
        self.v_backup = tk.BooleanVar(value=False)
        ttk.Checkbutton(grid, text="写入前备份原文件到同目录 exif_backup/",
                        variable=self.v_backup).grid(
            row=3, column=0, columnspan=3, sticky=tk.W)

        # ④ 按钮
        r4 = ttk.Frame(root)
        r4.pack(fill=tk.X, padx=16, pady=(8, 2))
        self.btn_run = ttk.Button(r4, text="开始处理", command=self._start)
        self.btn_run.pack(side=tk.LEFT, padx=(0, 12))
        self.btn_cancel = ttk.Button(r4, text="取消", command=self._cancel_run,
                                     state=tk.DISABLED)
        self.btn_cancel.pack(side=tk.LEFT, padx=(0, 12))
        ttk.Button(r4, text="退出程序", command=self._exit).pack(side=tk.LEFT)

        # ⑤ 进度 + 状态
        self.pb = ttk.Progressbar(root, mode="indeterminate")
        self.pb.pack(fill=tk.X, padx=16, pady=(6, 2))
        self.status_var = tk.StringVar(value="就绪：请选择轨迹文件和媒体目录")
        ttk.Label(root, textvariable=self.status_var, style="Sub.TLabel").pack(
            anchor=tk.W, padx=18)

        # 日志
        lf = ttk.LabelFrame(root, text=" 处理日志（每个文件一行结果） ", padding=6)
        lf.pack(fill=tk.BOTH, expand=True, padx=16, pady=(4, 12))
        self.log_box = ScrolledText(lf, height=12, wrap=tk.WORD,
                                    font=("Menlo" if sys.platform == "darwin"
                                          else "Consolas", 10),
                                    bg="#ffffff", fg="#1a1a1a",
                                    relief="flat", bd=0)
        self.log_box.pack(fill=tk.BOTH, expand=True)
        self.log_box.configure(state=tk.DISABLED)

        self._entry_widgets = [e1, e2]

    def log(self, msg):
        self.log_box.configure(state=tk.NORMAL)
        self.log_box.insert(tk.END, msg + "\n")
        self.log_box.see(tk.END)
        self.log_box.configure(state=tk.DISABLED)

    # ---------- 文件选择 ----------
    def _select_gps_file(self):
        path = filedialog.askopenfilename(
            title="选择GPS轨迹文件",
            filetypes=[("GPS轨迹文件", "*.gpx *.fit *.tcx *.txt"),
                       ("GPX文件", "*.gpx"), ("FIT文件", "*.fit"),
                       ("TCX文件", "*.tcx"), ("文本文件", "*.txt"),
                       ("所有文件", "*.*")])
        if not path:
            return
        self.gps_file_path = path
        self.gps_file_var.set("%s  （%s）" % (
            os.path.basename(path), os.path.dirname(path)))
        self.status_var.set("正在解析轨迹文件…")
        self._set_busy(True)
        threading.Thread(target=self._worker_load, args=(path,), daemon=True).start()

    def _worker_load(self, path):
        try:
            pts, info = load_track(path, log=lambda m: self._q.put(("log", m)))
            self._q.put(("loaded", (pts, info, path)))
        except Exception as e:
            self._q.put(("load_error", (str(e), traceback_text())))

    def _select_media_dir(self):
        path = filedialog.askdirectory(title="选择照片/视频目录")
        if not path:
            return
        self.photo_dir = path
        n_photo, n_video = count_media(path)
        self.media_dir_var.set(path)
        self.status_var.set("媒体目录已选择：照片 %d 个，视频 %d 个" % (n_photo, n_video))

    # ---------- 忙碌控制 ----------
    def _set_busy(self, busy):
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
            self.pb.config(mode="indeterminate", maximum=100, value=0)
            self.pb.start(60)
        else:
            self.pb.stop()

    def _cancel_run(self):
        self._cancel = True
        self.status_var.set("正在取消…")

    # ---------- 主流程 ----------
    def _start(self):
        if not self.gps_file_path or not self.gps_points:
            messagebox.showwarning("提示", "请先选择并成功解析轨迹文件")
            return
        if not self.photo_dir:
            messagebox.showwarning("提示", "请先选择照片/视频目录")
            return
        try:
            tolerance = float(self.v_tolerance.get())
            if tolerance < 0:
                raise ValueError
        except ValueError:
            messagebox.showerror("参数有误", "匹配容差必须是非负数字")
            return
        try:
            tz_hours = float(self.v_tz.get())
        except ValueError:
            messagebox.showerror("参数有误", "照片时区必须是数字")
            return
        if not any(p.time is not None for p in self.gps_points):
            messagebox.showwarning("提示", "轨迹点全部没有时间戳，无法匹配！")
            return
        if self._busy:
            messagebox.showwarning("提示", "正在处理中")
            return

        self._cancel = False
        self.log_box.configure(state=tk.NORMAL)
        self.log_box.delete("1.0", tk.END)
        self.log_box.configure(state=tk.DISABLED)
        self._set_busy(True)
        self.status_var.set("正在处理…")
        threading.Thread(target=self._worker_process, daemon=True).start()

    def _worker_process(self):
        try:
            tolerance = float(self.v_tolerance.get())
            tz_hours = float(self.v_tz.get())
            overwrite = self.v_overwrite.get()
            backup = self.v_backup.get()
            self._q.put(("log", "=== 开始处理 ==="))
            self._q.put(("log", "轨迹：%s（时间按真 UTC 解释）"
                         % os.path.basename(self.gps_file_path)))
            self._q.put(("log", "媒体目录：%s" % self.photo_dir))

            files = collect_media(self.photo_dir)
            if not files:
                self._q.put(("log", "目录里没有照片/视频文件。"))
                self._q.put(("done", None))
                return
            self._q.put(("log", "共 %d 个文件（照片 %d / 视频 %d）"
                         % (len(files),
                            sum(1 for f, v in files if not v),
                            sum(1 for f, v in files if v))))
            self._q.put(("progress_max", len(files)))

            stats = Stats()
            stats.total = len(files)
            points = self.gps_points
            for idx, (path, is_video) in enumerate(files, 1):
                if self._cancel:
                    self._q.put(("log", "—— 已取消 ——"))
                    break
                kind = "视频" if is_video else "照片"
                self._q.put(("log", "[%d/%d] %s（%s）"
                             % (idx, len(files), os.path.basename(path), kind)))
                self._q.put(("progress", idx))
                self._q.put(("status", "(%d/%d) %s" % (idx, len(files),
                                                       os.path.basename(path))))
                process_media(path, is_video, points, tolerance, tz_hours,
                              overwrite, backup, stats,
                              log=lambda m: self._q.put(("log", m)),
                              should_cancel=lambda: self._cancel)

            self._q.put(("stats", stats))
            self._q.put(("done", None))
        except Exception:
            self._q.put(("fatal", traceback_text()))

    # ---------- 队列轮询 ----------
    def _poll(self):
        try:
            while True:
                kind, payload = self._q.get_nowait()
                if kind == "log":
                    self.log(payload)
                elif kind == "status":
                    self.status_var.set(payload)
                elif kind == "progress_max":
                    self.pb.stop()
                    self.pb.config(mode="determinate", maximum=max(payload, 1),
                                   value=0)
                elif kind == "progress":
                    try:
                        self.pb.config(value=payload)
                    except tk.TclError:
                        pass
                elif kind == "loaded":
                    self._on_loaded(*payload)
                elif kind == "load_error":
                    self._set_busy(False)
                    self.status_var.set("轨迹解析失败")
                    self.log("!! 轨迹解析失败：%s" % payload[0])
                    self.log(payload[1])
                    messagebox.showerror("轨迹解析失败", payload[0])
                elif kind == "stats":
                    self._on_stats(payload)
                elif kind == "fatal":
                    self._set_busy(False)
                    self.status_var.set("处理出错")
                    self.log("!! 致命错误：")
                    self.log(payload)
                    messagebox.showerror("处理出错", payload.splitlines()[-1])
                elif kind == "done":
                    self._set_busy(False)
        except queue_mod.Empty:
            pass
        self.root.after(80, self._poll)

    def _on_loaded(self, pts, info, path):
        self.gps_points = pts
        self.track_info = info
        self._set_busy(False)
        if info["total"] == 0:
            self.status_var.set("⚠ 未解析到有效 GPS 点")
            messagebox.showerror("无数据", "文件里没有解析到有效 GPS 点。")
            return
        if info["with_time"] == 0:
            self.status_var.set("⚠ %d 个点均无时间戳，无法匹配！" % info["total"])
            messagebox.showerror("无时间", "轨迹点全部没有时间戳，无法按时间匹配。")
            return
        tmin, tmax = info["t_min"], info["t_max"]
        self.log("轨迹已加载：%s（%d 点，含时间 %d，含海拔 %d）"
                 % (os.path.basename(path), info["total"],
                    info["with_time"], info["with_ele"]))
        if info["dup_times"]:
            self.log("⚠ 轨迹里有 %d 处重复时间戳（不影响匹配，取同位置点）"
                     % info["dup_times"])
        if tmin is not None:
            self.log("轨迹时间范围（UTC）：%s ~ %s"
                     % (tmin.strftime("%Y-%m-%d %H:%M:%S"),
                        tmax.strftime("%Y-%m-%d %H:%M:%S")))
            self.log("            对应北京时间：%s ~ %s"
                     % ((tmin + timedelta(hours=DEFAULT_TZ_HOURS)).strftime(
                         "%Y-%m-%d %H:%M:%S"),
                        (tmax + timedelta(hours=DEFAULT_TZ_HOURS)).strftime(
                         "%Y-%m-%d %H:%M:%S")))
            self.log("↑↑ 请核对：照片大概在这个北京时间范围内才会匹配上。")
        self.status_var.set("轨迹已加载：%d 点（%d 含时间）"
                            % (info["total"], info["with_time"]))

    def _on_stats(self, st):
        summary = ("总计 %d | 写入 %d | 未写入 %d"
                   "（无匹配 %d、无拍摄时间 %d、保留原GPS %d、失败 %d）"
                   % (st.total, st.written, st.not_written, st.no_match,
                      st.no_time, st.skipped_existing, st.errors))
        self.log("-" * 60)
        self.log("处理完成：" + summary)
        self.status_var.set(summary)
        messagebox.showinfo(
            "处理完成",
            "总文件数：%d\n写入 GPS：%d\n未写入：%d\n"
            "  · 无匹配（超出容差）：%d\n"
            "  · 无拍摄时间：%d\n"
            "  · 已有 GPS 保留未覆盖：%d\n"
            "  · 读取/写入失败：%d"
            % (st.total, st.written, st.not_written, st.no_match,
               st.no_time, st.skipped_existing, st.errors))

    def _exit(self):
        if self._busy:
            if not messagebox.askyesno("确认", "正在处理中，确定退出？"):
                return
        self.root.destroy()


# ============================================================
# 媒体收集
# ============================================================
def collect_media(folder):
    """返回 [(完整路径, is_video)]，按文件名排序。"""
    out = []
    try:
        names = sorted(os.listdir(folder))
    except OSError:
        return out
    for name in names:
        full = os.path.join(folder, name)
        if not os.path.isfile(full):
            continue
        ext = os.path.splitext(name)[1].lower()
        if ext in PHOTO_EXTENSIONS:
            out.append((full, False))
        elif ext in VIDEO_EXTENSIONS:
            out.append((full, True))
    return out


def count_media(folder):
    files = collect_media(folder)
    return (sum(1 for _, v in files if not v),
            sum(1 for _, v in files if v))


def traceback_text():
    import traceback
    return traceback.format_exc()


# ============================================================
# 命令行入口
# ============================================================
def cli_main(args):
    ok, ver = exiftool_ok()
    if not ok:
        print("[错误] 找不到 exiftool，请安装：https://exiftool.org/")
        return 1
    print("[exiftool] %s" % ver)
    try:
        points, info = load_track(args.track, log=print)
    except FitNotSupported as e:
        print("[错误] %s" % e)
        return 1
    except Exception as e:
        print("[错误] 轨迹解析失败：%s" % e)
        return 1
    if info["total"] == 0 or info["with_time"] == 0:
        print("[错误] 轨迹无有效点或全部无时间戳。")
        return 1
    print("[轨迹] %d 点（含时间 %d，含海拔 %d），范围 %s ~ %s (UTC)"
          % (info["total"], info["with_time"], info["with_ele"],
             info["t_min"], info["t_max"]))
    files = collect_media(args.media_dir)
    if not files:
        print("[错误] 目录里没有照片/视频文件。")
        return 1
    print("[媒体] %d 个文件" % len(files))
    stats = Stats()
    stats.total = len(files)
    for idx, (path, is_video) in enumerate(files, 1):
        print("[%d/%d] %s" % (idx, len(files), os.path.basename(path)))
        process_media(path, is_video, points, args.tolerance, args.tz_hours,
                      args.overwrite, args.backup, stats, log=print)
    print("=" * 60)
    print("总计 %d | 写入 %d | 未写入 %d（无匹配 %d、无时间 %d、"
          "保留原GPS %d、失败 %d）"
          % (stats.total, stats.written, stats.not_written, stats.no_match,
             stats.no_time, stats.skipped_existing, stats.errors))
    return 0


def main():
    argv = sys.argv[1:]
    if argv:
        p = argparse.ArgumentParser(
            description="%s %s（命令行模式）" % (APP_TITLE, APP_VERSION))
        p.add_argument("track", help="GPX/TCX/FIT 轨迹文件")
        p.add_argument("media_dir", help="照片/视频目录")
        p.add_argument("--tolerance", type=float, default=DEFAULT_TOLERANCE,
                       help="匹配容差秒数，默认 %g" % DEFAULT_TOLERANCE)
        p.add_argument("--tz-hours", type=float, default=DEFAULT_TZ_HOURS,
                       dest="tz_hours",
                       help="照片本地时区（相对 UTC 的小时数），默认 8")
        p.add_argument("--overwrite", action="store_true",
                       help="覆盖已有 GPS 信息")
        p.add_argument("--backup", action="store_true",
                       help="写入前备份原文件到 exif_backup/")
        return cli_main(p.parse_args(argv))

    ok, _ver = exiftool_ok()
    if not ok:
        root = tk.Tk()
        root.withdraw()
        messagebox.showerror("缺少exiftool",
                             "请安装 exiftool 并加入 PATH\nhttps://exiftool.org/")
        root.destroy()
        return 1

    root = tk.Tk()
    GpsWriterApp(root)
    root.mainloop()
    return 0


if __name__ == "__main__":
    sys.exit(main())
