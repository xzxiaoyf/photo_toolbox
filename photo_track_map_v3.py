#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
照片轨迹地图 v3（ttk / clam 风格）—— 轨迹 + 照片一起标在高德地图上

在「轨迹地图查看器 v2」基础上新增照片功能（轨迹部分完全保留）：
- 「选择照片目录」按钮 → 显示带路径的目录名
- 左侧列出该目录下的所有照片（可含子目录）：文件名 / 拍摄时间 / 有无 GPS
- 点击照片：若带 GPS，右侧信息区显示
    · 原始 GPS（EXIF 里的 WGS-84 经纬度、海拔、方向）
    · 转换后的高德坐标（GCJ-02 火星坐标）
    · 逆地理编码得到的中文地址名称（需要高德 Key）
    · 该照片的缩图
- 内嵌高德地图上同时显示照片标记（所有带 GPS 的照片 + 当前选中照片高亮）
  点击地图上的照片标记 → 弹出该照片的缩图与坐标/地址
- 「浏览器打开」的网页版同样显示照片标记，点击标记弹出缩图
- 照片的 EXIF 与缩图一律交给外部 exiftool 处理
  （缩图链：ThumbnailImage → JpgFromRaw → PreviewImage；都取不到时才用 macOS
   sips 兜底生成小图，用于 HEIC / 无嵌入缩图的文件）

原有轨迹功能：
- 选择 GPX / TCX / FIT 轨迹文件，显示带路径的文件名
- 显示轨迹开始/结束时间的 UTC(+Z) 值；输入/选择时区后同时显示本地时间
  （并提供「时间口径」切换：小米等设备导出的 Z 常为本地墙钟挂 Z）
- 显示轨迹走过的公里数（WGS-84 球面距离，FIT 有设备记录值时一并列出）
- 内嵌高德地图（Canvas 瓦片渲染）：滚轮缩放、拖拽平移、标准图/卫星图切换、
  轨迹起点（绿）/终点（红）标注、「适配轨迹」按钮

依赖：仅 Python 标准库（无 PIL / requests / tkinterweb / gpxpy / fitparse）
     卫星 JPEG 瓦片与照片缩图用内置纯 Python 基线 JPEG 解码器
     （已与 macOS sips 逐像素比对验证）
     外部命令 exiftool（照片 EXIF 与缩图提取）
"""

import base64
import hashlib
import json
import math
import os
import queue as queue_mod
import re
import shutil
import ssl
import struct
import subprocess
import sys
import tempfile
import threading
import time as time_mod
import traceback
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone

import tkinter as tk
from tkinter import ttk, filedialog, messagebox

APP_TITLE = "照片轨迹地图 v3（高德）"

TILE_SIZE = 256
ZOOM_MIN, ZOOM_MAX = 3, 17

#: 瓦片图层：每层是若干叠加源（按顺序绘制）。实测可用的官方瓦片端点。
TILE_SOURCES = {
    "std": "https://webrd0{s}.is.autonavi.com/appmaptile?lang=zh_cn&size=1"
           "&scale=1&style=8&x={x}&y={y}&z={z}",
    "sat": "https://webst0{s}.is.autonavi.com/appmaptile?style=6"
           "&x={x}&y={y}&z={z}",
}
MAP_LAYERS = (("标准图", ("std",)), ("卫星图", ("sat",)))

USER_AGENT = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
              "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124 Safari/537.36")


# ============================================================
# HTTPS 证书自动降级
#   python.org 安装的 Python 不自带 CA 证书（需手动运行
#   /Applications/Python 3.x/Install Certificates.command），
#   未安装时所有 HTTPS 请求都会抛 CERTIFICATE_VERIFY_FAILED——
#   表现就是「轨迹能画出来，但地图瓦片一张都下不到」。
#   这里按 certifi → 系统 CA 文件 → 系统默认 → 关闭校验 依次降级。
# ============================================================
_SYS_CA_FILES = (
    "/etc/ssl/cert.pem",                        # macOS / 部分 Linux
    "/etc/pki/tls/certs/ca-bundle.crt",         # RHEL / CentOS
    "/etc/ssl/certs/ca-certificates.crt",       # Debian / Ubuntu
)

_SSL_CANDIDATES = None
_SSL_PREFERRED = 0
_SSL_NOTE = ""          # 实际生效的降级说明；空串 = 正常校验


def _ssl_candidates():
    """构造候选 (标题, ssl context, 降级说明)，按安全性从高到低。"""
    global _SSL_CANDIDATES
    if _SSL_CANDIDATES is not None:
        return _SSL_CANDIDATES
    paths = []
    try:
        import certifi
        paths.append(certifi.where())
    except Exception:
        pass
    paths.extend(p for p in _SYS_CA_FILES if os.path.exists(p))
    cands = []
    for p in paths:
        try:
            cands.append(("CA 文件 %s" % p,
                          ssl.create_default_context(cafile=p), ""))
        except Exception:
            continue
    try:
        cands.append(("系统默认证书库", ssl.create_default_context(), ""))
    except Exception:
        pass
    cands.append(("跳过证书校验", ssl._create_unverified_context(),
                  "系统缺少 CA 证书，已临时跳过 HTTPS 证书校验"))
    _SSL_CANDIDATES = cands
    return cands


def ssl_note():
    """实际生效的证书降级说明（空串表示正常校验）。"""
    return _SSL_NOTE


def http_get(url, timeout=15, referer=None):
    """带证书自动降级的 HTTPS GET，返回响应字节。

    先试上次成功的候选，再依次尝试其它候选；只有证书类错误才降级，
    真正的网络错误（DNS/超时）原样抛出，便于给出准确的失败原因。
    """
    global _SSL_PREFERRED, _SSL_NOTE
    cands = _ssl_candidates()
    order = [_SSL_PREFERRED] + [i for i in range(len(cands))
                                if i != _SSL_PREFERRED]
    headers = {"User-Agent": USER_AGENT}
    if referer:
        headers["Referer"] = referer
    cert_err = None
    for idx in order:
        _, ctx, note = cands[idx]
        try:
            req = urllib.request.Request(url, headers=headers)
            with urllib.request.urlopen(req, timeout=timeout,
                                        context=ctx) as resp:
                data = resp.read()
            _SSL_PREFERRED = idx
            _SSL_NOTE = note
            return data
        except urllib.error.URLError as e:
            reason = getattr(e, "reason", None)
            if isinstance(reason, ssl.SSLError) or isinstance(e, ssl.SSLError):
                cert_err = e           # 证书问题 → 换下一个候选
                continue
            raise
        except ssl.SSLError as e:
            cert_err = e
            continue
    raise cert_err if cert_err is not None else RuntimeError(
        "HTTPS 请求失败：%s" % url)


# ============================================================
# 字体：跨平台挑选第一个可用的中文字体
# ============================================================
def pick_font():
    try:
        from tkinter import font as tkfont
        root = tk._get_default_root()
        available = set(tkfont.families(root))
        for name in ("PingFang SC", "Microsoft YaHei UI", "Microsoft YaHei",
                     "Noto Sans CJK SC", "Source Han Sans SC", "Heiti SC",
                     "WenQuanYi Micro Hei"):
            if name in available:
                return name
    except Exception:
        pass
    return "TkDefaultFont"


# ============================================================
# 子进程静默化：Windows 上别弹「命令窗口」
#   本进程若没有控制台（用 pythonw.exe 启动、或打包成 --noconsole 的
#   exe），Windows 会给每个被调用的控制台程序单独新建一个控制台窗口，
#   程序一退出立即关掉——看起来就是「点一下、黑框闪一下」。
#   点一张照片要跑 exiftool 抽缩图（必要时再跑一次 PowerShell 压小），
#   于是每张照片都闪；扫描整个目录时按批闪。
#   解法：CREATE_NO_WINDOW 让子进程压根不建控制台，再叠一层
#   STARTUPINFO(SW_HIDE) 兜底（个别 shell / 中间包装程序会忽略前者）。
#   非 Windows 返回 {}，所以调用处统一写 `**hidden_kw()` 即可。
# ============================================================
def hidden_kw(osname=None, startupinfo_cls=None):
    """返回用于隐藏子进程窗口的 kwargs（非 Windows 平台返回空字典）。"""
    name = osname or os.name
    if name != "nt":
        return {}
    kw = {"creationflags": getattr(subprocess, "CREATE_NO_WINDOW",
                                   0x08000000)}          # CREATE_NO_WINDOW
    cls = startupinfo_cls if startupinfo_cls is not None else getattr(
        subprocess, "STARTUPINFO", None)
    if cls is not None:
        try:
            si = cls()
            si.dwFlags |= getattr(subprocess, "STARTF_USESHOWWINDOW", 1)
            si.wShowWindow = 0                            # SW_HIDE
            kw["startupinfo"] = si
        except Exception:
            pass
    return kw


# ============================================================
# 外部 exiftool 定位
#   照片的 EXIF 与缩图一律交给外部 exiftool 处理（与 sony_exif_shutter /
#   photo_exif_viewer 一致）。Finder 双击启动的进程 PATH 常缺
#   /opt/homebrew/bin 等目录，所以找不到就按常见安装位置兜底，
#   再不行问一次登录 shell（能读到用户 .zprofile 里的 PATH）。
# ============================================================
def find_exiftool():
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
        try:   # 最后兜底：问登录 shell（读取用户 .zprofile 里的 PATH）
            out = subprocess.run(["/bin/zsh", "-lc", "command -v exiftool"],
                                 capture_output=True, text=True, timeout=5,
                                 **hidden_kw())
            p = out.stdout.strip()
            if p and os.path.isfile(p) and os.access(p, os.X_OK):
                return p
        except Exception:
            pass
    return None


EXIFTOOL = find_exiftool() or "exiftool"


# ============================================================
# 配置文件：与 photo_toolbox / sony_exif_shutter 等共用
# 运行 py 用脚本目录；编译后用 exe/.app 所在目录
# ============================================================
def _config_path():
    if getattr(sys, "frozen", False):           # PyInstaller
        base = os.path.dirname(os.path.abspath(sys.executable))
        parent = os.path.dirname(os.path.dirname(base))
        if sys.platform == "darwin" and parent.endswith(".app"):
            base = os.path.dirname(parent)
    else:
        base = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base, "exif_viewer_config.json")


CONFIG_PATH = _config_path()
_LEGACY_CANDIDATES = [os.path.join(os.getcwd(), "exif_viewer_config.json")]

#: 形似真实高德 key 的 32 位十六进制
_KEY_RE = re.compile(r"^[0-9a-fA-F]{32}$")


def load_config():
    """读配置；amap_key 为空时兼容从旧字段 js_key / rest_key 取（须形似真 key）。"""
    cfg = {}
    for path in [CONFIG_PATH] + _LEGACY_CANDIDATES:
        if not os.path.exists(path):
            continue
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict) and data:
                cfg = dict(data)
                break
        except Exception:
            continue
    key = str(cfg.get("amap_key") or "").strip()
    if not _KEY_RE.match(key):
        for alt in ("js_key", "rest_key"):
            cand = str(cfg.get(alt) or "").strip()
            if _KEY_RE.match(cand):
                key = cand
                break
    cfg["amap_key"] = key
    return cfg


def save_config_fields(fields):
    """读全量 → 合并若干字段 → 原子写回（保留其它工具写入的字段）。

    与 save_amap_key 同一套写法：先写临时文件再 os.replace，
    避免其它工具（或本程序崩溃）读到半截 JSON。
    """
    cfg = {}
    if os.path.exists(CONFIG_PATH):
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict):
                cfg = data
        except Exception:
            cfg = {}
    cfg.update(fields)
    d = os.path.dirname(CONFIG_PATH) or "."
    try:
        fd, tmp = tempfile.mkstemp(dir=d, prefix=".cfg_", suffix=".tmp")
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                json.dump(cfg, f, indent=2, ensure_ascii=False)
            os.replace(tmp, CONFIG_PATH)
        except BaseException:
            try:
                os.unlink(tmp)
            except OSError:
                pass
            raise
        return True
    except Exception:
        return False


def save_amap_key(key):
    """读全量 → 只改 amap_key → 原子写回（保留其它工具的字段）。"""
    if save_config_fields({"amap_key": str(key).strip()}):
        return True
    messagebox.showerror("保存失败", "无法写入配置文件：\n%s" % CONFIG_PATH)
    return False


# ============================================================
# 时间解析：兼容 Z / ±HH:MM / ±HHMM / 无时区 / 任意位小数秒
# ============================================================
_TS_RE = re.compile(
    r"^(\d{4})-(\d{2})-(\d{2})[Tt ](\d{2}):(\d{2}):(\d{2})"
    r"(?:\.(\d+))?\s*(Z|z|[+-]\d{2}:?\d{2})?$")


def parse_iso_time(text):
    """返回 (dt, was_utc, had_offset)。dt 为 aware(UTC 或带偏移) 或 naive。"""
    if not text:
        return None, False, False
    m = _TS_RE.match(text.strip())
    if not m:
        return None, False, False
    y, mo, d, h, mi, s = (int(m.group(i)) for i in range(1, 7))
    frac = (m.group(7) or "")[:6].ljust(6, "0")
    us = int(frac) if frac else 0
    if not (1970 <= y <= 2100):
        return None, False, False
    tz = m.group(8)
    try:
        dt = datetime(y, mo, d, h, mi, s, us)
    except ValueError:
        return None, False, False
    if tz in ("Z", "z"):
        return dt.replace(tzinfo=timezone.utc), True, False
    if tz:
        sign = 1 if tz[0] == "+" else -1
        hh = int(tz[1:3])
        mm = int(tz.replace(":", "")[3:5])
        if hh > 14 or mm > 59:
            return dt, False, False
        off = timezone(sign * timedelta(hours=hh, minutes=mm))
        return dt.replace(tzinfo=off), False, True
    return dt, False, False


def fmt_utc_z(dt):
    if dt is None:
        return "—"
    u = dt.astimezone(timezone.utc)
    return u.strftime("%Y-%m-%d %H:%M:%SZ")


def fmt_local(dt, offset_hours, assume_wall=False):
    """assume_wall=True：dt 本身就是墙钟时间（伪 Z 口径）。"""
    if dt is None:
        return "—"
    if assume_wall:
        wall = dt if dt.tzinfo is None else dt.astimezone(
            timezone.utc).replace(tzinfo=None)
        return wall.strftime("%Y-%m-%d %H:%M:%S")
    u = dt.astimezone(timezone.utc) + timedelta(hours=offset_hours)
    return u.strftime("%Y-%m-%d %H:%M:%S")


def utc_of(dt, offset_hours, assume_wall=False):
    if dt is None:
        return None
    if assume_wall:
        wall = dt if dt.tzinfo is None else dt.astimezone(
            timezone.utc).replace(tzinfo=None)
        return wall.replace(tzinfo=timezone.utc) - timedelta(hours=offset_hours)
    return dt.astimezone(timezone.utc)


# ============================================================
# GCJ-02 火星坐标转换（WGS-84 ↔ GCJ-02，标准算法）
# ============================================================
_PI = math.pi
_A = 6378245.0                     # 长半轴
_EE = 0.00669342162296594323       # 偏心率平方


def _out_of_china(lat, lon):
    return not (72.004 <= lon <= 137.8347 and 0.8293 <= lat <= 55.8271)


def _transform_lat(x, y):
    ret = (-100.0 + 2.0 * x + 3.0 * y + 0.2 * y * y + 0.1 * x * y
           + 0.2 * math.sqrt(abs(x)))
    ret += (20.0 * math.sin(6.0 * x * _PI) + 20.0 *
            math.sin(2.0 * x * _PI)) * 2.0 / 3.0
    ret += (20.0 * math.sin(y * _PI) + 40.0 *
            math.sin(y / 3.0 * _PI)) * 2.0 / 3.0
    ret += (160.0 * math.sin(y / 12.0 * _PI) + 320.0 *
            math.sin(y * _PI / 30.0)) * 2.0 / 3.0
    return ret


def _transform_lon(x, y):
    ret = (300.0 + x + 2.0 * y + 0.1 * x * x + 0.1 * x * y
           + 0.1 * math.sqrt(abs(x)))
    ret += (20.0 * math.sin(6.0 * x * _PI) + 20.0 *
            math.sin(2.0 * x * _PI)) * 2.0 / 3.0
    ret += (20.0 * math.sin(x * _PI) + 40.0 *
            math.sin(x / 3.0 * _PI)) * 2.0 / 3.0
    ret += (150.0 * math.sin(x / 12.0 * _PI) + 300.0 *
            math.sin(x / 30.0 * _PI)) * 2.0 / 3.0
    return ret


def wgs84_to_gcj02(lat, lon):
    if _out_of_china(lat, lon):
        return lat, lon
    dlat = _transform_lat(lon - 105.0, lat - 35.0)
    dlon = _transform_lon(lon - 105.0, lat - 35.0)
    radlat = lat / 180.0 * _PI
    magic = math.sin(radlat)
    magic = 1 - _EE * magic * magic
    sqrtmagic = math.sqrt(magic)
    dlat = (dlat * 180.0) / ((_A * (1 - _EE)) / (magic * sqrtmagic) * _PI)
    dlon = (dlon * 180.0) / (_A / sqrtmagic * math.cos(radlat) * _PI)
    return lat + dlat, lon + dlon


def gcj02_to_wgs84(lat, lon):
    """迭代逼近的逆变换（精度约 1e-9 度）。"""
    wlat, wlon = lat, lon
    for _ in range(3):
        glat, glon = wgs84_to_gcj02(wlat, wlon)
        wlat += lat - glat
        wlon += lon - glon
    return wlat, wlon


def haversine_m(lat1, lon1, lat2, lon2):
    rlat1, rlat2 = math.radians(lat1), math.radians(lat2)
    dlat = rlat2 - rlat1
    dlon = math.radians(lon2 - lon1)
    a = (math.sin(dlat / 2) ** 2
         + math.cos(rlat1) * math.cos(rlat2) * math.sin(dlon / 2) ** 2)
    return 2 * 6371008.8 * math.asin(math.sqrt(a))


# ============================================================
# 纯 Python 基线 JPEG 解码器（卫星瓦片用）
# 仅支持基线顺序 DCT；渐进式等抛 JpegError 由调用方兜底。
# ============================================================
class JpegError(Exception):
    pass


def _build_lut(counts, symbols):
    if sum(counts) != len(symbols):
        raise JpegError("DHT 长度不一致")
    maxlen = 0
    for l, c in enumerate(counts, 1):
        if c:
            maxlen = l
    if maxlen == 0:
        raise JpegError("空霍夫曼表")
    size = 1 << maxlen
    lut_code = [0] * size
    lut_len = [0] * size
    code = 0
    k = 0
    for l in range(1, maxlen + 1):
        for _ in range(counts[l - 1]):
            sym = symbols[k]
            k += 1
            if code >= (1 << l):
                raise JpegError("霍夫曼码溢出")
            prefix = code << (maxlen - l)
            for i in range(prefix, prefix + (1 << (maxlen - l))):
                lut_code[i] = sym
                lut_len[i] = l
            code += 1
        code <<= 1
    return maxlen, lut_code, lut_len


class _BitReader(object):
    __slots__ = ("data", "pos", "bitbuf", "bitcnt", "at_marker", "marker")

    def __init__(self, data, pos):
        self.data = data
        self.pos = pos
        self.bitbuf = 0
        self.bitcnt = 0
        self.at_marker = False
        self.marker = 0

    def _fill(self):
        data = self.data
        n = len(data)
        while self.bitcnt <= 24 and not self.at_marker:
            p = self.pos
            if p >= n:
                self.at_marker = True
                self.marker = 0xD9
                return
            b = data[p]
            if b != 0xFF:
                self.pos = p + 1
                self.bitbuf = (self.bitbuf << 8) | b
                self.bitcnt += 8
                continue
            nb = data[p + 1] if p + 1 < n else 0xD9
            if nb == 0x00:                      # 填充字节
                self.pos = p + 2
                self.bitbuf = (self.bitbuf << 8) | 0xFF
                self.bitcnt += 8
            elif 0xD0 <= nb <= 0xD7:            # 重启标记：留给 consume
                self.at_marker = True
                self.marker = nb
                return
            else:
                self.at_marker = True
                self.marker = nb
                self.pos = p + 1
                return

    def decode_huff(self, maxlen, lut_code, lut_len):
        if self.bitcnt < maxlen:
            if self.at_marker:
                while self.bitcnt < maxlen:
                    self.bitbuf = (self.bitbuf << 1) | 1
                    self.bitcnt += 1
            else:
                self._fill()
                while self.bitcnt < maxlen and self.at_marker:
                    self.bitbuf = (self.bitbuf << 1) | 1
                    self.bitcnt += 1
        idx = (self.bitbuf >> (self.bitcnt - maxlen)) & ((1 << maxlen) - 1)
        ln = lut_len[idx]
        if ln == 0:
            raise JpegError("霍夫曼解码失败")
        self.bitcnt -= ln
        return lut_code[idx]

    def receive_extend(self, s):
        if s == 0:
            return 0
        if self.bitcnt < s:
            if self.at_marker:
                while self.bitcnt < s:
                    self.bitbuf = (self.bitbuf << 1) | 1
                    self.bitcnt += 1
            else:
                self._fill()
                while self.bitcnt < s and self.at_marker:
                    self.bitbuf = (self.bitbuf << 1) | 1
                    self.bitcnt += 1
        self.bitcnt -= s
        v = (self.bitbuf >> self.bitcnt) & ((1 << s) - 1)
        if v < (1 << (s - 1)):
            v -= (1 << s) - 1
        return v

    def consume_restart(self):
        if self.at_marker and 0xD0 <= self.marker <= 0xD7:
            self.pos += 2
            self.at_marker = False
            self.marker = 0
            self.bitbuf = 0
            self.bitcnt = 0
            return True
        return False


_ZIGZAG = [
    0, 1, 8, 16, 9, 2, 3, 10,
    17, 24, 32, 25, 18, 11, 4, 5,
    12, 19, 26, 33, 40, 48, 41, 34,
    27, 20, 13, 6, 7, 14, 21, 28,
    35, 42, 49, 56, 57, 50, 43, 36,
    29, 22, 15, 23, 30, 37, 44, 51,
    58, 59, 52, 45, 38, 31, 39, 46,
    53, 60, 61, 54, 47, 55, 62, 63]

_T = [[0.5 * (0.7071067811865476 if u == 0 else 1.0) *
       math.cos((2 * x + 1) * u * math.pi / 16.0) for u in range(8)]
      for x in range(8)]


def _decode_block(br, dct, act, qtab, pred, ci):
    blk = [0.0] * 64
    s = br.decode_huff(dct[0], dct[1], dct[2])
    if s:
        diff = br.receive_extend(s)
        pred[ci] += diff
    blk[0] = pred[ci] * qtab[0]
    k = 1
    while k < 64:
        rs = br.decode_huff(act[0], act[1], act[2])
        r = rs >> 4
        s = rs & 15
        if s == 0:
            if r == 15:
                k += 16
                continue
            break
        k += r
        if k > 63:
            break
        blk[_ZIGZAG[k]] = br.receive_extend(s) * qtab[_ZIGZAG[k]]
        k += 1
    return blk


def _idct_flat(dc):
    v = int(dc * 0.125 + 128.5)
    if v < 0:
        v = 0
    elif v > 255:
        v = 255
    return [v] * 64


def _idct_block(blk):
    flat = True
    for i in range(1, 64):
        if blk[i]:
            flat = False
            break
    if flat:
        return _idct_flat(blk[0])
    tmp = [0.0] * 64
    T = _T
    for y in range(8):
        off = y * 8
        row = blk[off:off + 8]
        for x in range(8):
            s = 0.0
            for u in range(8):
                c = row[u]
                if c:
                    s += c * T[x][u]
            tmp[off + x] = s
    out = [0] * 64
    for x in range(8):
        for y in range(8):
            s = 0.0
            for v in range(8):
                c = tmp[(v << 3) + x]
                if c:
                    s += c * T[y][v]
            val = int(s + 128.5)
            if val < 0:
                val = 0
            elif val > 255:
                val = 255
            out[(y << 3) + x] = val
    return out


def decode_jpeg_rgb(data):
    """返回 (w, h, bytearray RGB)。"""
    if len(data) < 4 or data[0] != 0xFF or data[1] != 0xD8:
        raise JpegError("不是 JPEG")
    pos = 2
    n = len(data)
    qt = {}
    huff_dc = {}
    huff_ac = {}
    frame = None
    dri = 0
    scan = None
    while pos + 4 <= n:
        if data[pos] != 0xFF:
            pos += 1
            continue
        marker = data[pos + 1]
        if marker == 0xFF:
            pos += 1
            continue
        if marker in (0x01, 0xD8) or 0xD0 <= marker <= 0xD7:
            pos += 2
            continue
        if marker == 0xD9:
            break
        seglen = int.from_bytes(data[pos + 2:pos + 4], "big")
        if seglen < 2 or pos + 2 + seglen > n:
            raise JpegError("段长度越界")
        body = data[pos + 4: pos + 2 + seglen]
        if marker == 0xDB:
            i = 0
            while i < len(body):
                pq = body[i] >> 4
                tq = body[i] & 15
                i += 1
                tbl = [0] * 64
                for j in range(64):
                    if pq:
                        tbl[_ZIGZAG[j]] = int.from_bytes(body[i:i + 2], "big")
                        i += 2
                    else:
                        tbl[_ZIGZAG[j]] = body[i]
                        i += 1
                qt[tq] = tbl
        elif marker in (0xC0, 0xC1):
            if body[0] != 8:
                raise JpegError("精度 %d 不支持" % body[0])
            h = int.from_bytes(body[1:3], "big")
            w = int.from_bytes(body[3:5], "big")
            nc = body[5]
            if nc not in (1, 3):
                raise JpegError("分量数 %d 不支持" % nc)
            comps = []
            i = 6
            for _ in range(nc):
                comps.append({"id": body[i], "h": body[i + 1] >> 4,
                              "v": body[i + 1] & 15, "tq": body[i + 2]})
                i += 3
            frame = {"w": w, "h": h, "comps": comps}
        elif marker == 0xC2:
            raise JpegError("渐进式 JPEG 不支持")
        elif marker == 0xC4:
            i = 0
            while i + 17 <= len(body):
                tc = body[i] >> 4
                th = body[i] & 15
                counts = list(body[i + 1:i + 17])
                cnt = sum(counts)
                syms = list(body[i + 17:i + 17 + cnt])
                i += 17 + cnt
                tbl = _build_lut(counts, syms)
                if tc == 0:
                    huff_dc[th] = tbl
                else:
                    huff_ac[th] = tbl
        elif marker == 0xDD:
            dri = int.from_bytes(body[:2], "big")
        elif marker == 0xDA:
            ns = body[0]
            scomps = []
            i = 1
            for _ in range(ns):
                scomps.append((body[i], body[i + 1] >> 4, body[i + 1] & 15))
                i += 2
            scan = {"scomps": scomps, "ss": body[i], "se": body[i + 1],
                    "data_pos": pos + 2 + seglen}
            break
        pos += 2 + seglen
    if frame is None or scan is None:
        raise JpegError("缺少 SOF/SOS")
    if (scan["ss"], scan["se"]) not in ((0, 63), (1, 63)):
        raise JpegError("非常规频谱选择")
    return _decode_scan(data, frame, qt, huff_dc, huff_ac, scan, dri)


def _decode_scan(data, frame, qt, huff_dc, huff_ac, scan, dri):
    w, h = frame["w"], frame["h"]
    comps = frame["comps"]
    scomps = dict((cs, (td, ta)) for (cs, td, ta) in scan["scomps"])
    hmax = max(c["h"] for c in comps)
    vmax = max(c["v"] for c in comps)
    mcux = (w + 8 * hmax - 1) // (8 * hmax)
    mcuy = (h + 8 * vmax - 1) // (8 * vmax)

    planes = []
    for c in comps:
        pw = mcux * 8 * c["h"]
        ph = mcuy * 8 * c["v"]
        planes.append(bytearray(pw * ph))
        c["stride"] = pw

    br = _BitReader(data, scan["data_pos"])
    pred = [0] * len(comps)
    restart_left = dri
    done = 0
    for my in range(mcuy):
        for mx in range(mcux):
            if dri and restart_left == 0 and done > 0:
                if not br.consume_restart():
                    break
                pred = [0] * len(comps)
                restart_left = dri
            for ci, c in enumerate(comps):
                td, ta = scomps.get(c["id"], (None, None))
                dct = huff_dc.get(td)
                act = huff_ac.get(ta)
                if dct is None or act is None:
                    raise JpegError("缺霍夫曼表")
                qtab = qt.get(c["tq"])
                if qtab is None:
                    raise JpegError("缺量化表")
                stride = c["stride"]
                plane = planes[ci]
                top = (my * c["v"]) * 8 * stride + (mx * c["h"]) * 8
                for by in range(c["v"]):
                    for bx in range(c["h"]):
                        blk = _decode_block(br, dct, act, qtab, pred, ci)
                        px = _idct_block(blk)
                        base = top + by * 8 * stride + bx * 8
                        for r in range(8):
                            off = base + r * stride
                            bo = r << 3
                            plane[off] = px[bo]
                            plane[off + 1] = px[bo + 1]
                            plane[off + 2] = px[bo + 2]
                            plane[off + 3] = px[bo + 3]
                            plane[off + 4] = px[bo + 4]
                            plane[off + 5] = px[bo + 5]
                            plane[off + 6] = px[bo + 6]
                            plane[off + 7] = px[bo + 7]
            done += 1
            if dri:
                restart_left -= 1
        if done < (my + 1) * mcux:
            break
    return _compose(frame, planes, mcux, mcuy, hmax, vmax)


def _compose(frame, planes, mcux, mcuy, hmax, vmax):
    w, h, comps = frame["w"], frame["h"], frame["comps"]
    out = bytearray(w * h * 3)
    yp = planes[0]
    ystride = comps[0]["stride"]

    if len(comps) == 1:
        for y in range(h):
            base = y * w * 3
            yoff = y * ystride
            for x in range(w):
                g = yp[yoff + x]
                i3 = base + 3 * x
                out[i3] = g
                out[i3 + 1] = g
                out[i3 + 2] = g
        return w, h, out

    geo = []
    for c in comps[1:]:
        geo.append({"stride": c["stride"], "cw": mcux * 8 * c["h"],
                    "ch": mcuy * 8 * c["v"],
                    "sx": c["h"] / float(hmax), "sy": c["v"] / float(vmax)})

    def _itab(out_n, src_n):
        tab = []
        for o in range(out_n):
            p = (o + 0.5) * src_n / float(out_n) - 0.5
            if p < 0:
                p = 0.0
            i0 = int(p)
            if i0 > src_n - 1:
                i0 = src_n - 1
            frac = p - i0
            i1 = i0 + 1 if i0 + 1 < src_n else src_n - 1
            tab.append((i0, i1, frac))
        return tab

    cplane0 = planes[1]
    cplane1 = planes[2] if len(planes) > 2 else None
    g0, g1 = geo[0], geo[1]
    xt0 = _itab(w, g0["cw"])
    xt1 = _itab(w, g1["cw"])

    tab_vr = [int(round(1.402 * (v - 128))) for v in range(256)]
    tab_vg = [int(round(-0.344136 * (v - 128))) for v in range(256)]
    tab_ub = [int(round(1.772 * (u - 128))) for u in range(256)]
    tab_ug = [int(round(-0.714136 * (u - 128))) for u in range(256)]

    for oy in range(h):
        def _crow(cplane, g, xt):
            p = (oy + 0.5) * g["sy"] - 0.5
            if p < 0:
                p = 0.0
            i0 = int(p)
            if i0 > g["ch"] - 1:
                i0 = g["ch"] - 1
            frac = p - i0
            i1 = i0 + 1 if i0 + 1 < g["ch"] else g["ch"] - 1
            b0 = i0 * g["stride"]
            b1 = i1 * g["stride"]
            cw = g["cw"]
            r0 = cplane[b0:b0 + cw]
            r1 = cplane[b1:b1 + cw]
            row = [0] * w
            for x in range(w):
                a0, a1, wx = xt[x]
                v0 = r0[a0] + (r0[a1] - r0[a0]) * wx
                v1 = r1[a0] + (r1[a1] - r1[a0]) * wx
                row[x] = int(v0 + (v1 - v0) * frac + 0.5)
            return row

        cbrow = _crow(cplane0, g0, xt0)
        crrow = _crow(cplane1, g1, xt1) if cplane1 is not None else cbrow
        ybase = oy * ystride
        obase = oy * w * 3
        for x in range(w):
            yy = yp[ybase + x]
            cb = cbrow[x]
            cr = crrow[x]
            r = yy + tab_vr[cr]
            g = yy + tab_ug[cb] + tab_vg[cr]
            b = yy + tab_ub[cb]
            i3 = obase + 3 * x
            out[i3] = 0 if r < 0 else (255 if r > 255 else r)
            out[i3 + 1] = 0 if g < 0 else (255 if g > 255 else g)
            out[i3 + 2] = 0 if b < 0 else (255 if b > 255 else b)
    return w, h, out


# ============================================================
# 轨迹解析：GPX / TCX / FIT（纯标准库）
# 点结构: (datetime|None, lat, lon, ele|None, 原始时间文本|None)
# ============================================================
def _local(tag):
    """去掉 XML 命名空间。"""
    return tag.split("}")[-1] if isinstance(tag, str) else ""


def parse_gpx(path):
    parser = ET.XMLParser(target=ET.TreeBuilder(insert_comments=True,
                                                insert_pis=True))
    tree = ET.parse(path, parser=parser)
    root = tree.getroot()
    fmt = "GPX %s" % (root.get("version") or "1.x")
    segments = []
    name = None
    for el in root.iter():
        if _local(el.tag) == "name" and name is None and el.text:
            name = el.text.strip()
    trksegs = []
    for trk in root.iter():
        if _local(trk.tag) != "trk":
            continue
        for seg in trk.iter():
            if _local(seg.tag) == "trkseg":
                trksegs.append(seg)
    if not trksegs:
        for rte in root.iter():
            if _local(rte.tag) == "rte":
                trksegs.append(rte)
    for seg in trksegs:
        pts = []
        for p in seg.iter():
            if _local(p.tag) not in ("trkpt", "rtept"):
                continue
            try:
                lat = float(p.get("lat"))
                lon = float(p.get("lon"))
            except (TypeError, ValueError):
                continue
            if not (-90 <= lat <= 90 and -180 <= lon <= 180):
                continue
            ele = None
            t = None
            raw = None
            for c in p:
                ln = _local(c.tag)
                if ln == "ele":
                    try:
                        ele = float(c.text)
                    except (TypeError, ValueError):
                        ele = None
                elif ln == "time":
                    raw = (c.text or "").strip()
                    t, _, _ = parse_iso_time(raw)
            pts.append((t, lat, lon, ele, raw))
        if pts:
            segments.append(pts)
    return {"fmt": fmt, "segments": segments, "device_distance_m": None,
            "name": name, "warnings": []}


def parse_tcx(path):
    tree = ET.parse(path)
    root = tree.getroot()
    fmt = "TCX"
    segments = []
    device_distance_m = None
    name = None
    for act in root.iter():
        if _local(act.tag) != "Activity":
            continue
        if name is None:
            sid = act.get("Sport")
            for c in act:
                if _local(c.tag) == "Id" and c.text:
                    name = (sid or "Activity") + " " + c.text.strip()[:19]
                    break
        for lap in act.iter():
            if _local(lap.tag) != "Lap":
                continue
            for track in lap.iter():
                if _local(track.tag) != "Track":
                    continue
                pts = []
                for p in track.iter():
                    if _local(p.tag) != "Trackpoint":
                        continue
                    t = None
                    raw = None
                    lat = lon = None
                    ele = None
                    for c in p.iter():
                        ln = _local(c.tag)
                        if ln == "Time" and t is None:
                            raw = (c.text or "").strip()
                            t, _, _ = parse_iso_time(raw)
                        elif ln == "LatitudeDegrees":
                            try:
                                lat = float(c.text)
                            except (TypeError, ValueError):
                                lat = None
                        elif ln == "LongitudeDegrees":
                            try:
                                lon = float(c.text)
                            except (TypeError, ValueError):
                                lon = None
                        elif ln == "AltitudeMeters":
                            try:
                                ele = float(c.text)
                            except (TypeError, ValueError):
                                ele = None
                    if lat is None or lon is None:
                        continue
                    if not (-90 <= lat <= 90 and -180 <= lon <= 180):
                        continue
                    pts.append((t, lat, lon, ele, raw))
                if pts:
                    segments.append(pts)
            for c in lap:
                if _local(c.tag) == "DistanceMeters":
                    try:
                        device_distance_m = float(c.text)
                    except (TypeError, ValueError):
                        pass
    return {"fmt": fmt, "segments": segments,
            "device_distance_m": device_distance_m, "name": name,
            "warnings": []}


# ---------------- FIT ----------------
FIT_EPOCH = 631065600          # 1989-12-31 00:00:00 UTC

_FIT_BASE_TYPES = {
    0x00: (1, "B", 0xFF), 0x01: (1, "b", -0x80), 0x02: (1, "B", 0xFF),
    0x07: (1, "B", 0x00), 0x0A: (1, "B", 0xFF), 0x0D: (1, "B", 0xFF),
    0x83: (2, "h", -0x8000), 0x84: (2, "H", 0xFFFF),
    0x85: (4, "i", -0x80000000), 0x86: (4, "I", 0xFFFFFFFF),
    0x88: (4, "f", None), 0x89: (8, "d", None),
    0x8B: (2, "H", 0xFFFF), 0x8C: (4, "I", 0xFFFFFFFF),
    0x8D: (8, "q", None), 0x8E: (8, "Q", None),
}

_CRC_TABLE = (
    0x0000, 0xCC01, 0xD801, 0x1400, 0xF001, 0x3C00, 0x2800, 0xE401,
    0xA001, 0x6C00, 0x7800, 0xB401, 0x5000, 0x9C01, 0x8801, 0x4400)


def _fit_crc16(data, crc=0):
    T = _CRC_TABLE
    for byte in data:
        tmp = T[crc & 0xF]
        crc = (crc >> 4) & 0x0FFF
        crc ^= tmp ^ T[byte & 0xF]
        tmp = T[crc & 0xF]
        crc = (crc >> 4) & 0x0FFF
        crc ^= tmp ^ T[(byte >> 4) & 0xF]
    return crc & 0xFFFF


class FitError(Exception):
    pass


def _fit_read_fields(body, i, flds, arch, dev_sizes):
    vals = {}
    p = i
    n = len(body)
    for (num, size, bt) in flds:
        fstart = p
        meta = _FIT_BASE_TYPES.get(bt)
        if meta is None:
            meta = _FIT_BASE_TYPES.get(bt | 0x80)
        if meta is None:
            p = fstart + size
            continue
        width, fmt, invalid = meta
        cnt = size // width if width else 0
        arr = []
        for _ in range(max(cnt, 1)):
            if p + width > n or p - fstart + width > size:
                break
            v = struct.unpack_from(("<" if arch == 0 else ">") + fmt,
                                   body, p)[0]
            arr.append(v)
            p += width
        p = fstart + size            # 按声明尺寸前进（防病态文件错位）
        if not arr:
            continue
        v0 = arr[0]
        if invalid is not None and v0 == invalid:
            continue
        if bt == 0x07:
            v0 = bytes(arr).split(b"\x00")[0].decode("utf-8", "replace")
        vals[num] = v0
    p += sum(dev_sizes)
    return vals, p - i


def parse_fit(path):
    with open(path, "rb") as f:
        data = f.read()
    if len(data) < 14:
        raise FitError("文件过小，不是有效的 FIT 文件")
    if data[8:12] != b".FIT":
        raise FitError("不是 FIT 文件（缺 .FIT 魔数）")
    header_size = data[0]
    if header_size not in (12, 14):
        raise FitError("不支持的文件头长度 %d" % header_size)
    data_size = int.from_bytes(data[4:8], "little")
    body_end = min(header_size + data_size, len(data))
    body = data[header_size:body_end]

    warnings = []
    if len(data) >= body_end + 2:
        crc_val = int.from_bytes(data[body_end:body_end + 2], "little")
        crc_start = 0 if header_size < 14 else header_size
        if _fit_crc16(data[crc_start:body_end]) != crc_val:
            warnings.append("FIT 数据区 CRC 校验不符（文件可能被改动/截断），已按可读内容解析")

    defs = {}
    points = []
    last_ts = 0
    sessions = []
    laps = []
    sport = ""
    device_distance_m = None
    fit_start = None
    fit_end = None
    i = 0
    n = len(body)
    while i < n:
        h = body[i]
        if h & 0x80:                                   # 压缩时间戳头
            local = (h >> 5) & 0x03
            t_off = h & 0x1F
            i += 1
            d = defs.get(local)
            if d is None:
                warnings.append("FIT 数据区在 offset %d 处无法继续解析（已解析部分正常显示）" % i)
                break
            gmsg, arch, flds, dev_sizes = d
            vals, size = _fit_read_fields(body, i, flds, arch, dev_sizes)
            i += size
            if gmsg == 20:
                ts = (last_ts & ~0x1F) | t_off
                if ts < last_ts:
                    ts += 32
                last_ts = ts
                _fit_collect(vals, last_ts, points)
            continue
        local = h & 0x0F
        i += 1
        if h & 0x40:                                   # 定义消息
            if i + 5 > n:
                break
            arch = body[i + 1]
            gmsg = struct.unpack_from("<H" if arch == 0 else ">H",
                                      body, i + 2)[0]
            nfields = body[i + 4]
            p = i + 5
            flds = []
            for _ in range(nfields):
                if p + 3 > n:
                    break
                flds.append((body[p], body[p + 1], body[p + 2]))
                p += 3
            dev_sizes = []
            if h & 0x20:                               # 开发者字段定义
                # 布局: (字段定义号, 尺寸, 开发者数据索引)
                ndev = body[p] if p < n else 0
                p += 1
                for _ in range(ndev):
                    if p + 3 > n:
                        break
                    dev_sizes.append(body[p + 1])
                    p += 3
            else:
                ndev = 0
            defs[local] = (gmsg, arch, flds, dev_sizes)
            i = p
            continue
        d = defs.get(local)
        if d is None:
            warnings.append("FIT 数据区在 offset %d 处无法继续解析（已解析部分正常显示）" % i)
            break
        gmsg, arch, flds, dev_sizes = d
        vals, size = _fit_read_fields(body, i, flds, arch, dev_sizes)
        i += size
        if gmsg == 20:                                 # record
            ts = vals.get(253)
            if ts is not None:
                last_ts = ts
            _fit_collect(vals, last_ts, points)
        elif gmsg in (18, 19):                         # session / lap
            entry = {}
            if vals.get(253) is not None:
                entry["time"] = _fit_time(vals[253])
            if vals.get(2) is not None:
                entry["start_time"] = _fit_time(vals[2])
            if vals.get(9) is not None:
                entry["total_distance"] = vals[9] / 100.0
            if gmsg == 18:
                if vals.get(5) is not None:
                    sport = _FIT_SPORTS.get(vals[5], str(vals[5]))
                if entry.get("total_distance") is not None:
                    device_distance_m = entry["total_distance"]
                if entry.get("start_time") is not None:
                    fit_start = entry["start_time"]
                if entry.get("time") is not None:
                    fit_end = entry["time"]
                sessions.append(entry)
            else:
                if device_distance_m is None and entry.get("total_distance") \
                        is not None:
                    device_distance_m = entry["total_distance"]
                laps.append(entry)
    if device_distance_m is None and laps:
        device_distance_m = sum(l.get("total_distance") or 0 for l in laps)
        if device_distance_m <= 0:
            device_distance_m = None
    if fit_start is None and sessions:
        fit_start = sessions[0].get("start_time")
    if fit_end is None and sessions:
        fit_end = sessions[-1].get("time")
    return {"fmt": "FIT", "segments": [points] if points else [],
            "device_distance_m": device_distance_m,
            "name": sport or None, "warnings": warnings,
            "fit_start": fit_start, "fit_end": fit_end}


_FIT_SPORTS = {0: "通用", 1: "跑步", 2: "骑行", 5: "徒步", 6: "登山",
               8: "步行", 9: "游泳", 11: "椭圆机", 12: "爬楼机",
               17: "越野跑", 253: "其他"}


def _fit_time(ts):
    if not ts:
        return None
    try:
        return datetime.fromtimestamp(FIT_EPOCH + ts, tz=timezone.utc)
    except (OverflowError, OSError, ValueError):
        return None


def _fit_collect(vals, ts, points):
    lat = vals.get(0)
    lon = vals.get(1)
    if lat is None or lon is None:
        return
    lat = lat * (180.0 / (1 << 31))
    lon = lon * (180.0 / (1 << 31))
    if not (-90.0 <= lat <= 90.0 and -180.0 <= lon <= 180.0):
        return
    t = _fit_time(ts)
    ele = vals.get(78, vals.get(2))
    if ele is not None:
        ele = ele / 5.0 - 500.0
    points.append((t, lat, lon, ele, None))


def parse_track(path):
    """按扩展名分派；返回统一结构。"""
    ext = os.path.splitext(path)[1].lower()
    if ext == ".gpx":
        return parse_gpx(path)
    if ext == ".tcx":
        return parse_tcx(path)
    if ext == ".fit":
        return parse_fit(path)
    raise ValueError("不支持的文件类型: %s（请选择 GPX / TCX / FIT）" % ext)


class TrackStats(object):
    """由解析结果计算的展示用统计。"""

    def __init__(self, result):
        segs = result["segments"]
        self.fmt = result["fmt"]
        self.name = result.get("name")
        self.device_distance_m = result.get("device_distance_m")
        self.warnings = list(result.get("warnings") or [])
        self.n_points = sum(len(s) for s in segs)
        self.n_valid = 0
        self.distance_m = 0.0
        first = None
        last = None
        self.segments_gcj = []
        for seg in segs:
            gcj = []
            prev = None
            for (t, lat, lon, ele, raw) in seg:
                self.n_valid += 1
                if prev is not None:
                    self.distance_m += haversine_m(prev[0], prev[1], lat, lon)
                prev = (lat, lon)
                if first is None:
                    first = (t, lat, lon, raw)
                last = (t, lat, lon, raw)
                gcj.append((t,) + wgs84_to_gcj02(lat, lon) + (ele, raw))
            if gcj:
                self.segments_gcj.append(gcj)
        self.first = first
        self.last = last
        # FIT 会话起止时间兜底（轨迹点缺时间时）
        if first is None or first[0] is None:
            self.fit_start = result.get("fit_start")
            self.fit_end = result.get("fit_end")
        else:
            self.fit_start = None
            self.fit_end = None
        # FIT 的设备时间挂 UTC，但点时间就是 UTC，无需特殊处理

    @property
    def start_dt(self):
        if self.first and self.first[0] is not None:
            return self.first[0]
        return self.fit_start

    @property
    def end_dt(self):
        if self.last and self.last[0] is not None:
            return self.last[0]
        return self.fit_end

    @property
    def start_raw(self):
        return self.first[3] if self.first else None

    @property
    def end_raw(self):
        return self.last[3] if self.last else None


# ============================================================
# 瓦片下载（后台线程 + 磁盘缓存）
# ============================================================
def _tile_cache_dir(kind):
    d = os.path.join(tempfile.gettempdir(), "amap_tile_cache_v2", kind)
    try:
        os.makedirs(d, exist_ok=True)
    except OSError:
        d = None
    return d


def _disk_tile_path(kind, z, x, y):
    d = _tile_cache_dir(kind)
    if d is None:
        return None
    return os.path.join(d, "%d_%d_%d.bin" % (z, x, y))


def _tile_valid(raw):
    """轻量魔数校验，避免把错误页/半截数据当瓦片写进缓存。"""
    if not raw:
        return False
    return raw[:4] == b"\x89PNG" or raw[:2] == b"\xff\xd8"


class TileLoader(object):
    """后台下载瓦片原始字节，结果经队列回主线程。

    - 磁盘缓存的坏数据自动丢弃重下；
    - 同一瓦片失败 MAX_ATTEMPTS 次后放弃，不再无限重试；
    - 失败原因随结果回传，供界面显示。
    """

    MAX_ATTEMPTS = 3

    def __init__(self, result_queue, workers=4):
        self.result_queue = result_queue
        self.jobs = queue_mod.Queue()
        self.pending = set()
        self.failed = {}                       # key -> 已失败次数
        self.lock = threading.Lock()
        self.stopped = False
        self.threads = []
        for i in range(workers):
            t = threading.Thread(target=self._worker, daemon=True)
            t.start()
            self.threads.append(t)

    def request(self, kind, z, x, y):
        key = (kind, z, x, y)
        with self.lock:
            if key in self.pending:
                return False
            if self.failed.get(key, 0) >= self.MAX_ATTEMPTS:
                return False
            self.pending.add(key)
        self.jobs.put(key)
        return True

    def reset_failures(self, forget_cache=False):
        """「重载地图」：清空失败记录，可选连磁盘缓存一起清。"""
        with self.lock:
            self.failed.clear()
        if not forget_cache:
            return
        for kind in TILE_SOURCES:
            d = _tile_cache_dir(kind)
            if not d:
                continue
            for fn in os.listdir(d):
                try:
                    os.remove(os.path.join(d, fn))
                except OSError:
                    pass

    def _worker(self):
        while not self.stopped:
            try:
                key = self.jobs.get(timeout=0.5)
            except queue_mod.Empty:
                continue
            kind, z, x, y = key
            raw, err = None, ""
            path = _disk_tile_path(kind, z, x, y)
            if path and os.path.exists(path):
                try:
                    with open(path, "rb") as f:
                        raw = f.read()
                except OSError:
                    raw = None
                if raw is not None and not _tile_valid(raw):
                    raw = None                      # 坏缓存，删除后重下
                    try:
                        os.remove(path)
                    except OSError:
                        pass
            if raw is None:
                url = TILE_SOURCES[kind].format(s=(x % 4) + 1, x=x, y=y, z=z)
                for attempt in range(self.MAX_ATTEMPTS):
                    try:
                        data = http_get(url, timeout=15,
                                        referer="https://www.amap.com/")
                        if not _tile_valid(data):
                            raise ValueError("返回内容不是图片（%d 字节）"
                                             % len(data))
                        raw = data
                        break
                    except Exception as e:
                        err = "%s: %s" % (type(e).__name__, e)
                        raw = None
                        if attempt + 1 < self.MAX_ATTEMPTS:
                            time_mod.sleep(0.4 * (attempt + 1))
                if raw and path:
                    try:
                        with open(path, "wb") as f:
                            f.write(raw)
                    except OSError:
                        pass
                if raw is None:
                    with self.lock:
                        self.failed[key] = self.failed.get(key, 0) + 1
            with self.lock:
                self.pending.discard(key)
            try:
                self.result_queue.put(("tile", kind, z, x, y, raw, err))
            except Exception:
                pass

    def stop(self):
        self.stopped = True


# ============================================================
# 照片：目录扫描 / EXIF 读取 / 缩图提取
#   EXIF 与缩图一律交给外部 exiftool（与本目录其它照片工具一致）。
#   批量读取：一次 exiftool 调用带一批文件，比逐张调用快一个数量级
#   （实测 98 张 6K JPEG 约 1 秒）。
# ============================================================

#: 视为「照片」的扩展名（小写，含常见相机 RAW）
PHOTO_EXTS = frozenset((
    ".jpg", ".jpeg", ".jpe", ".jfif", ".png", ".heic", ".heif", ".webp",
    ".hif",   # Sony HEIF（缩图走 exiftool 内嵌 JPEG / sips，均已实测支持）
    ".tif", ".tiff", ".bmp", ".gif",
    ".dng", ".cr2", ".cr3", ".crw", ".nef", ".nrw", ".arw", ".srf", ".sr2",
    ".raf", ".rw2", ".orf", ".pef", ".srw", ".x3f", ".rwl", ".mrw", ".erf",
    ".3fr", ".fff", ".iiq", ".k25", ".dcr", ".mef", ".mos", ".rwz",
))

#: 一次 exiftool 调用最多带多少个文件
EXIF_BATCH = 200

#: 扫描时向 exiftool 索取的标签（-n 取数值，-c 让坐标固定 6 位小数）
_EXIF_TAGS = (
    "-Make", "-Model", "-LensModel", "-LensInfo", "-Lens", "-Software",
    "-DateTimeOriginal", "-CreateDate", "-OffsetTimeOriginal",
    "-ExposureTime", "-FNumber", "-ISO", "-FocalLength",
    "-FocalLengthIn35mmFormat", "-ExposureCompensation", "-Flash",
    "-Orientation", "-ImageSize", "-ExifImageWidth", "-ExifImageHeight",
    "-MIMEType", "-FileSize", "-FileModifyDate",
    "-GPSLatitude", "-GPSLongitude", "-GPSAltitude", "-GPSAltitudeRef",
    "-GPSImgDirection", "-GPSDateTime", "-GPSStatus",
)

#: 缩图标签尝试顺序（exiftool -b 逐个试）
_THUMB_TAGS = ("ThumbnailImage", "JpgFromRaw", "PreviewImage")

#: 超过这个字节数的内嵌缩图，网页版会先压小，免得 HTML 变成几十兆
THUMB_MAX_BYTES = 150000

#: 缩图目标最长边
THUMB_MAX_PX = 480

#: 允许交给内置解码器的像素上限（超过它就必须先压小）。
#: 实测内置解码器吞吐只有 4.8e4 px/s（真实相机 JPEG）～4.9e5 px/s（平滑图）：
#: 1616x1080 要 36.4 秒，4608x3072 跑 4 分钟都没完；而它最终跑在 Tk 主线程里，
#: 所以「大图直接解」= 界面假死、只能强杀进程。超过这个数宁可不显示缩图。
MAX_DECODE_PIXELS = 200000


def _nfc(s):
    """macOS 文件名可能是 NFD，exiftool 回显可能是 NFC——统一后再比对。"""
    try:
        return unicodedata.normalize("NFC", s or "")
    except Exception:
        return s or ""


def list_photo_files(root, recursive=False):
    """列出目录下的照片文件（按文件名排序）。无权限/空目录返回 []。"""
    out = []
    if recursive:
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in dirnames if not d.startswith(".")]
            for fn in filenames:
                if fn.startswith("."):
                    continue
                if os.path.splitext(fn)[1].lower() in PHOTO_EXTS:
                    out.append(os.path.join(dirpath, fn))
    else:
        try:
            names = os.listdir(root)
        except OSError:
            return []
        for fn in names:
            if fn.startswith("."):
                continue
            p = os.path.join(root, fn)
            if not os.path.isfile(p):
                continue
            if os.path.splitext(fn)[1].lower() in PHOTO_EXTS:
                out.append(p)
    out.sort(key=lambda p: p.lower())
    return out


def read_photos_exif(paths, on_progress=None, stop=None):
    """批量读 EXIF，返回 {path: exiftool 的 JSON 项}。

    读不到的文件也会有条目（带 "Error"），方便界面标成「无法读取」。
    on_progress(done, total) 在每批结束后回调（供状态栏显示进度）。
    """
    result = {}
    total = len(paths)
    for i in range(0, total, EXIF_BATCH):
        if stop is not None and stop():
            break
        batch = paths[i:i + EXIF_BATCH]
        cmd = ([EXIFTOOL, "-json", "-n", "-c", "%.6f", "-q", "-q",
                "-charset", "filename=UTF8"] + list(_EXIF_TAGS) + batch)
        try:
            proc = subprocess.run(cmd, capture_output=True, timeout=300,
                                  **hidden_kw())
            data = json.loads((proc.stdout or b"").decode("utf-8", "replace")
                              or "[]")
        except Exception as e:
            for p in batch:
                result[p] = {"Error": "exiftool 调用失败：%s" % e}
            if on_progress:
                on_progress(min(i + EXIF_BATCH, total), total)
            continue
        by_name = {}
        for item in data:
            if isinstance(item, dict):
                by_name[_nfc(os.path.basename(
                    str(item.get("SourceFile") or "")))] = item
        for p in batch:
            item = by_name.get(_nfc(os.path.basename(p)))
            result[p] = item if item is not None else {
                "Error": "exiftool 未返回该文件"}
        if on_progress:
            on_progress(min(i + EXIF_BATCH, total), total)
    return result


def read_all_exif_text(path):
    """exiftool -a -G1 -s 全量转储（「查看全部 EXIF」用）。返回 (out, err)。"""
    proc = subprocess.run(
        [EXIFTOOL, "-a", "-G1", "-s", "-charset", "filename=UTF8", path],
        capture_output=True, timeout=120, **hidden_kw())
    return ((proc.stdout or b"").decode("utf-8", "replace"),
            (proc.stderr or b"").decode("utf-8", "replace"))


def gps_in_range(lat, lon):
    """经纬度是否落在合法范围（大疆遥控器那种 lat=1962 会被挡掉）。"""
    if not isinstance(lat, (int, float)) or not isinstance(lon, (int, float)):
        return False
    if isinstance(lat, bool) or isinstance(lon, bool):
        return False
    if not (-90.0 <= lat <= 90.0 and -180.0 <= lon <= 180.0):
        return False
    return not (abs(lat) < 1e-7 and abs(lon) < 1e-7)


def _is_num(v):
    return isinstance(v, (int, float)) and not isinstance(v, bool)


def fmt_exposure(item):
    """曝光三要素拼一行：1/500s · f/2.8 · ISO 100 · 24mm。"""
    parts = []
    et = item.get("ExposureTime")
    if _is_num(et) and et > 0:
        parts.append("%.1fs" % et if et >= 1 else "1/%.0fs" % round(1.0 / et))
    fn = item.get("FNumber")
    if _is_num(fn):
        parts.append("f/%.1f" % fn)
    iso = item.get("ISO")
    if iso:
        parts.append("ISO %s" % iso)
    fl = item.get("FocalLength")
    if _is_num(fl):
        s = "%.0fmm" % fl
        f35 = item.get("FocalLengthIn35mmFormat")
        if _is_num(f35) and abs(f35 - fl) > 0.6:
            s += "（等效%.0fmm）" % f35
        parts.append(s)
    ev = item.get("ExposureCompensation")
    if _is_num(ev) and abs(ev) > 0.01:
        parts.append("EV%+.1f" % ev)
    return " · ".join(parts)


def fmt_exif_dt(s):
    """'2026:08:22 10:03:36' → '2026-08-22 10:03:36'（拿不准就原样返回）。"""
    s = (s or "").strip()
    if len(s) >= 19 and s[4] == ":" and s[7] == ":":
        return s[:4] + "-" + s[5:7] + "-" + s[8:10] + " " + s[11:19]
    return s


def photo_info_from_exif(item, path=""):
    """把 exiftool 的一项整理成界面直接可用的字典。"""
    item = item or {}

    def g(key):
        v = item.get(key)
        if isinstance(v, (list, tuple)):
            v = " ".join(str(x) for x in v)
        if isinstance(v, str):
            v = v.strip()
            return v or ""
        return v

    d = {
        "path": path,
        "name": os.path.basename(path) or str(g("SourceFile") or "?"),
        "err": g("Error") or "",
        "make": g("Make") or "", "model": g("Model") or "",
        "lens": g("LensModel") or g("Lens") or g("LensInfo") or "",
        "software": g("Software") or "",
        "dt": g("DateTimeOriginal") or g("CreateDate") or "",
        "offset": g("OffsetTimeOriginal") or "",
        "size": g("ImageSize") or "",
        "mime": g("MIMEType") or "",
        "fsize": g("FileSize") if _is_num(g("FileSize")) else None,
        "exposure": fmt_exposure(item),
        "orientation": g("Orientation"),
        "lat": None, "lon": None, "alt": None, "dir_deg": None,
        "ok_gps": False, "gcj": None,
    }
    lat, lon = item.get("GPSLatitude"), item.get("GPSLongitude")
    if gps_in_range(lat, lon):
        d["lat"], d["lon"] = float(lat), float(lon)
        d["ok_gps"] = True
        alt = item.get("GPSAltitude")
        if _is_num(alt):
            if str(item.get("GPSAltitudeRef", "0")) in ("1", "1.0"):
                alt = -alt
            d["alt"] = float(alt)
        hd = item.get("GPSImgDirection")
        if _is_num(hd):
            d["dir_deg"] = float(hd)
    return d


# ---------- 缩图：exiftool 三标签 → 外部后端压小 ----------
def extract_thumb_bytes(path, tags=_THUMB_TAGS):
    """用 exiftool 抽嵌入缩图（ThumbnailImage → JpgFromRaw → PreviewImage）。

    没有该标签时 exiftool 的 stdout 是空的，直接换下一个标签继续试。
    返回 (bytes, 命中的标签名)；都没抽到返回 (None, "")。
    """
    for tag in tags:
        try:
            proc = subprocess.run([EXIFTOOL, "-b", "-" + tag, path],
                                  capture_output=True, timeout=20,
                                  **hidden_kw())
        except Exception:
            continue
        raw = proc.stdout or b""
        if proc.returncode == 0 and len(raw) > 200:
            return raw, tag
    return None, ""


def jpeg_dimensions(data):
    """只扫 JPEG 头返回 (宽, 高)，不碰像素（毫秒级）。

    用来在解码前判断这张图能不能解——把大图喂给内置解码器会冻住界面。
    不是 JPEG / 找不到 SOF 时返回 (0, 0)。
    """
    if len(data) < 4 or data[0] != 0xFF or data[1] != 0xD8:
        return 0, 0
    pos, n = 2, len(data)
    while pos + 4 <= n:
        if data[pos] != 0xFF:
            pos += 1
            continue
        marker = data[pos + 1]
        if marker == 0xFF or marker == 0x01 or 0xD0 <= marker <= 0xD9:
            pos += 2
            continue
        seglen = int.from_bytes(data[pos + 2:pos + 4], "big")
        if seglen < 2:
            return 0, 0
        # SOF0~SOF15，排除 DHT(0xC4) / JPG(0xC8) / DAC(0xCC)
        if 0xC0 <= marker <= 0xCF and marker not in (0xC4, 0xC8, 0xCC):
            body = data[pos + 4: pos + 2 + seglen]
            if len(body) >= 5:
                return (int.from_bytes(body[3:5], "big"),
                        int.from_bytes(body[1:3], "big"))
            return 0, 0
        pos += 2 + seglen
    return 0, 0


# PowerShell + .NET 缩放脚本（Windows 自带，不需要用户装任何东西）。
# $args = 输入路径, 最长边, 输出格式(png/jpeg), JPEG 质量, 输出路径
_PS_RESIZE = (
    "Add-Type -AssemblyName System.Drawing;"
    "$s=[System.Drawing.Image]::FromFile($args[0]);"
    "$m=[int]$args[1];"
    "if($s.Width -ge $s.Height){$nw=$m;$nh=[int]($s.Height*$m/$s.Width)}"
    "else{$nh=$m;$nw=[int]($s.Width*$m/$s.Height)};"
    "if($nw -lt 1){$nw=1};if($nh -lt 1){$nh=1};"
    "$b=New-Object System.Drawing.Bitmap($nw,$nh);"
    "$g=[System.Drawing.Graphics]::FromImage($b);"
    "$g.InterpolationMode="
    "[System.Drawing.Drawing2D.InterpolationMode]::HighQualityBicubic;"
    "$g.DrawImage($s,0,0,$nw,$nh);"
    "if($args[2] -eq 'jpeg'){"
    "$e=[System.Drawing.Imaging.ImageCodecInfo]::GetImageEncoders()|"
    "Where-Object{$_.MimeType -eq 'image/jpeg'};"
    "$p=New-Object System.Drawing.Imaging.EncoderParameters(1);"
    "$p.Param[0]=New-Object System.Drawing.Imaging.EncoderParameter("
    "[System.Drawing.Imaging.Encoder]::Quality,[int64]$args[3]);"
    "$b.Save($args[4],$e,$p)"
    "}else{$b.Save($args[4],[System.Drawing.Imaging.ImageFormat]::Png)};"
    "$g.Dispose();$b.Dispose();$s.Dispose()")


def find_shrinker(osname=None):
    """找一个可用的外部缩放后端，返回命令名（找不到返回 ""）。

    macOS 用 sips，Windows 用系统自带的 PowerShell + System.Drawing——
    两个平台都必须有后端，否则「压不小的大缩图」会原样流到解码器里。
    """
    name = osname or sys.platform
    if name == "darwin":
        return "sips" if shutil.which("sips") else ""
    if name.startswith("win"):
        for exe in ("powershell", "pwsh"):
            if shutil.which(exe):
                return exe
    return ""


def shrink_image_file(path, out_path, max_px=THUMB_MAX_PX, fmt="png",
                      quality=60, osname=None, exe=None):
    """用外部后端把 path 缩到 max_px 以内写到 out_path。成功返回 True。"""
    tool = find_shrinker(osname) if exe is None else exe
    if not tool:
        return False
    if tool == "sips":
        if fmt == "jpeg":
            cmd = ["sips", "-s", "format", "jpeg", "-s", "formatOptions",
                   str(int(quality)), "-Z", str(int(max_px)),
                   path, "--out", out_path]
        else:
            cmd = ["sips", "-s", "format", "png", "-Z", str(int(max_px)),
                   path, "--out", out_path]
    else:
        cmd = [tool, "-NoProfile", "-NonInteractive", "-ExecutionPolicy",
               "Bypass", "-Command", _PS_RESIZE,
               path, str(int(max_px)), fmt, str(int(quality)), out_path]
    try:
        proc = subprocess.run(cmd, capture_output=True, timeout=60,
                              **hidden_kw())
    except Exception:
        return False
    try:
        return proc.returncode == 0 and os.path.getsize(out_path) > 100
    except OSError:
        return False


def shrink_image_bytes(raw, src_path=None, max_px=THUMB_MAX_PX, fmt="png",
                       quality=60, osname=None, exe=None):
    """把图片压到 max_px 以内，返回压缩后的字节；做不到返回 b""。

    raw 有值就用 raw——相机 RAW 文件 System.Drawing 读不了，必须用
    exiftool 抽出来的那份 JPEG；raw 为空（HEIC 之类没有嵌入图的）才把
    原文件交给后端（macOS 的 sips 能直接读 HEIC）。
    """
    tmp_in = ""
    fd, tmp_out = tempfile.mkstemp(
        suffix=".jpg" if fmt == "jpeg" else ".png", prefix="shrink_")
    os.close(fd)
    try:
        if raw:
            fd2, tmp_in = tempfile.mkstemp(prefix="shrinkin_")
            os.close(fd2)
            with open(tmp_in, "wb") as f:
                f.write(raw)
            src = tmp_in
        else:
            # 没有嵌入图（HEIC 之类）时只能拿原文件去压。这里只认 macOS 的
            # sips：它什么都能读；Windows 的 System.Drawing 读不了 HEIC，
            # 而且把用户文件名交给 PowerShell 有风险（文件名里的 $ 会被
            # 当成变量），所以宁可不压。
            tool = find_shrinker(osname) if exe is None else exe
            if tool != "sips":
                return b""
            src = src_path
        if not src or not os.path.exists(src):
            return b""
        if not shrink_image_file(src, tmp_out, max_px, fmt, quality,
                                 osname, exe):
            return b""
        with open(tmp_out, "rb") as f:
            data = f.read()
        return data if len(data) > 100 else b""
    except Exception:
        return b""
    finally:
        for p in (tmp_in, tmp_out):
            if p:
                try:
                    os.remove(p)
                except OSError:
                    pass


def sips_thumb_bytes(path, max_px=320):
    """把原图缩成一张小 PNG（macOS 走 sips，Windows 走 PowerShell）。"""
    return shrink_image_bytes(b"", path, max_px, "png")


def thumb_bytes_for(path, osname=None, exe=None):
    """取缩图字节。返回 (bytes, 来源说明)。

    返回的字节**必须是能直接解码的小图**。踩过的坑：尼康 NEF 没有
    ThumbnailImage，只有 1 MB 的 4608x3072 JpgFromRaw；Windows 上没有
    sips，旧代码把这张大图原样返回，主线程一解码就假死几分钟（macOS 因为
    先被 sips 压到 480px 才没暴露）。所以这里无论哪个平台都要压小，
    压不小又超过解码预算时，宁可不给缩图。
    """
    raw, tag = extract_thumb_bytes(path)
    if raw is None:
        small = shrink_image_bytes(b"", path, THUMB_MAX_PX, "png", 60,
                                   osname, exe)
        if small:
            return small, "外部工具生成"
        return b"", "取不到缩图"
    w, h = jpeg_dimensions(raw)
    if len(raw) > THUMB_MAX_BYTES or w * h > MAX_DECODE_PIXELS:
        small = shrink_image_bytes(raw, path, THUMB_MAX_PX, "png", 60,
                                   osname, exe)
        if small:
            return small, "exiftool %s（已压小）" % tag
        if w * h > MAX_DECODE_PIXELS:
            return b"", ("嵌入预览过大（%dx%d）且无法压小，已跳过解码"
                         % (w, h))
        return raw, "exiftool %s（未压小）" % tag
    return raw, "exiftool %s" % tag



# ---------- 缩图磁盘缓存 ----------
#   抽缩图要起一次 exiftool 子进程（HEIC/无嵌入缩图时还要再起 sips），
#   列表来回点、反复「浏览器打开」都会重复付这个成本，
#   所以按「路径+mtime+大小」做键缓存到临时目录。
def _thumb_cache_dir():
    d = os.path.join(tempfile.gettempdir(), "photo_thumb_cache_v3")
    try:
        os.makedirs(d, exist_ok=True)
    except OSError:
        return ""
    return d


def _thumb_cache_key(path):
    try:
        st = os.stat(path)
        # 末尾的 k2 是缓存格式版本号：升到「压小后再返回」的版本后，
        # 旧缓存里那些没压大的缩图必须作废，否则修好了还会读到坏数据。
        sig = "%s|%d|%d|k2" % (path, st.st_mtime_ns, st.st_size)
    except OSError:
        sig = str(path)
    return hashlib.md5(sig.encode("utf-8", "replace")).hexdigest()


def cache_clear():
    """清空缩图缓存（「重新扫描」时顺带调用）。"""
    d = _thumb_cache_dir()
    if d and os.path.isdir(d):
        try:
            shutil.rmtree(d, ignore_errors=True)
        except Exception:
            pass


def _cache_write(path, data):
    """原子写缓存文件（同目录临时文件 + os.replace）。

    点照片时每张各起一个工作线程，同一张被连续请求两次就会同时写同一个
    缓存文件；直接 open(path, "wb") 会先截断，另一个线程可能读到半截字节
    （表现成「这张的缩图坏了」）。原子替换可以避免。
    """
    try:
        fd, tmp = tempfile.mkstemp(dir=os.path.dirname(path), prefix=".tmp_")
    except OSError:
        return
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(data)
        os.replace(tmp, path)
    except OSError:
        try:
            os.remove(tmp)
        except OSError:
            pass


def thumb_cached(path, use_cache=True):
    """带磁盘缓存的缩图获取。返回 (bytes, 来源说明)。

    缓存文件里存原始缩图字节；取不到缩图时写一个空的 .none 标记，
    避免每次点同一张 HEIC 都白跑一遍 exiftool + sips。
    """
    d = _thumb_cache_dir() if use_cache else ""
    if d:
        key = _thumb_cache_key(path)
        hit = os.path.join(d, key + ".bin")
        miss = os.path.join(d, key + ".none")
        if os.path.exists(hit):
            try:
                with open(hit, "rb") as f:
                    return f.read(), "缓存"
            except OSError:
                pass
        elif os.path.exists(miss):
            return b"", "缓存（先前未取到）"
    raw, src = thumb_bytes_for(path)
    if d:
        _cache_write(os.path.join(d, key + (".bin" if raw else ".none")),
                     raw or b"")
    return raw, src


# ---------- 图片字节 → Tk 图片 / 网页内嵌 ----------
def sniff_image_mime(raw):
    if raw[:8] == b"\x89PNG\r\n\x1a\n":
        return "image/png"
    if raw[:2] == b"\xff\xd8":
        return "image/jpeg"
    if raw[:4] == b"GIF8":
        return "image/gif"
    if raw[:2] == b"BM":
        return "image/bmp"
    if raw[:4] == b"RIFF" and raw[8:12] == b"WEBP":
        return "image/webp"
    if raw[:4] in (b"II*\x00", b"MM\x00*"):
        return "image/tiff"
    return "application/octet-stream"


def prepare_photo_payload(raw, max_px=None):
    """图片字节 → 「构造 PhotoImage 只需一步」的载荷。

    返回 (payload, 格式, 说明)：
      * PNG / GIF：原样给出，Tk 原生解码，主线程开销可忽略；
      * JPEG：在这里解成 PPM。解码前先读头部尺寸，超过
        MAX_DECODE_PIXELS 直接放弃——内置解码器解大图会长时间占着
        解释器，界面照样假死，所以必须在这里就拦住。
    """
    if not raw:
        return b"", "", "无数据"
    if raw[:8] == b"\x89PNG\r\n\x1a\n":
        return raw, "png", ""
    if raw[:4] == b"GIF8":
        return raw, "gif", ""
    if raw[:2] != b"\xff\xd8":
        return b"", "", "不支持的图片格式"
    w, h = jpeg_dimensions(raw)
    if w * h > MAX_DECODE_PIXELS:
        return b"", "", "图片过大（%dx%d），未解码" % (w, h)
    try:
        w, h, rgb = decode_jpeg_rgb(raw)
    except Exception as e:
        return b"", "", "解码失败：%s" % e
    if max_px and max(w, h) > max_px:
        w, h, rgb = downscale_rgb(w, h, rgb, max_px)
    return (b"P6\n%d %d\n255\n" % (w, h)) + bytes(rgb), "ppm", ""


def tk_photo_from_bytes(raw):
    """图片字节 → tk.PhotoImage（PNG/GIF 直传，JPEG 走内置解码器）。"""
    payload, tfmt, _note = prepare_photo_payload(raw)
    if not payload:
        return None
    try:
        return tk.PhotoImage(data=payload, format=tfmt)
    except Exception:
        return None


def subsample_photo(photo, max_px):
    """把 Tk 图片缩到最长边 <= max_px（subsample 只能整数倍，够用）。"""
    if photo is None:
        return None
    try:
        w, h = photo.width(), photo.height()
    except Exception:
        return photo
    if w <= 0 or h <= 0 or max(w, h) <= max_px:
        return photo
    try:
        return photo.subsample(int(math.ceil(max(w, h) / float(max_px))))
    except Exception:
        return photo


# ---------- 鸟种识别联动（bird_scanner.py 生成的边车 JSON，可选增强） ----------
#: 没有这些文件时本工具行为完全不变；识别由独立的 bird_scanner.py 负责

def bird_info_of(path):
    """读取照片旁的 <照片名>.bird.json（bird_scanner.py 生成）。

    纯标准库；文件不存在 / 损坏 / 为空都安全返回 None。
    """
    if not path:
        return None
    sp = os.path.splitext(path)[0] + ".bird.json"
    try:
        if not os.path.isfile(sp):
            return None
        with open(sp, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        birds = data.get("birds") or []
        if not birds:
            return None
        return {"birds": birds,
                "img_w": data.get("img_w"), "img_h": data.get("img_h")}
    except Exception:
        return None


def bird_summary_text(bi):
    """把边车数据压成信息面板里的一行字，如「夜鹭 87.1% / 苍鹭 32.0%（共2只）」。"""
    if not bi:
        return None
    parts = []
    for b in bi["birds"][:3]:
        top = (b.get("top5") or [{}])[0]
        # v2 边车带 species/conf（地域校正后的结论），旧边车回落到 top5[0]
        name = b.get("species") or top.get("cn") or top.get("en") or "?"
        conf = b.get("conf", top.get("conf") or 0.0)
        parts.append("%s %.1f%%" % (name, conf))
    txt = " / ".join(parts)
    n = len(bi["birds"])
    return txt + ("（共%d只）" % n if n > 1 else "")


def draw_bird_boxes(img, bi):
    """在 Tk PhotoImage（缩图）上画红色鸟框。

    边车里的 bbox 是原图坐标，按缩图/原图比例换算；任何异常都吞掉，
    画不了框只影响预览，不影响信息行。
    """
    try:
        w, h = img.width(), img.height()
        iw, ih = bi.get("img_w"), bi.get("img_h")
        if not (w and h and iw and ih):
            return
        sx, sy = w / float(iw), h / float(ih)
        for b in bi["birds"]:
            x1, y1, x2, y2 = b.get("bbox") or (None, None, None, None)
            if x1 is None:
                continue
            ax1, ay1 = int(max(0, x1 * sx)), int(max(0, y1 * sy))
            ax2, ay2 = int(min(w - 1, x2 * sx)), int(min(h - 1, y2 * sy))
            if ax2 - ax1 < 2 or ay2 - ay1 < 2:
                continue
            t = 2  # 框线厚度（缩图像素）
            img.put("#FF3B30", to=(ax1, ay1, ax2 + 1, ay1 + t))
            img.put("#FF3B30", to=(ax1, ay2 + 1 - t, ax2 + 1, ay2 + 1))
            img.put("#FF3B30", to=(ax1, ay1, ax1 + t, ay2 + 1))
            img.put("#FF3B30", to=(ax2 + 1 - t, ay1, ax2 + 1, ay2 + 1))
    except Exception:
        pass


def downscale_rgb(w, h, rgb, max_px):
    """纯 Python 最近邻缩放（给网页版内嵌小图用）。"""
    if w <= 0 or h <= 0 or max(w, h) <= max_px:
        return w, h, bytes(rgb)
    sc = max(w, h) / float(max_px)
    nw, nh = max(1, int(w / sc)), max(1, int(h / sc))
    out = bytearray(nw * nh * 3)
    for y in range(nh):
        sy = min(h - 1, int(y * sc))
        row = sy * w * 3
        o = y * nw * 3
        for x in range(nw):
            sx = min(w - 1, int(x * sc))
            s = row + sx * 3
            out[o + x * 3:o + x * 3 + 3] = rgb[s:s + 3]
    return nw, nh, bytes(out)


def encode_png_rgb(w, h, rgb):
    """RGB 缓冲 → PNG 字节（网页版内嵌缩图用，zlib 就够）。"""
    import zlib
    raw = bytearray()
    for y in range(h):
        raw.append(0)
        raw += rgb[y * w * 3:(y + 1) * w * 3]

    def chunk(tag, data):
        return (struct.pack(">I", len(data)) + tag + data
                + struct.pack(">I", zlib.crc32(tag + data) & 0xFFFFFFFF))

    return (b"\x89PNG\r\n\x1a\n"
            + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 2, 0, 0, 0))
            + chunk(b"IDAT", zlib.compress(bytes(raw), 6))
            + chunk(b"IEND", b""))


def shrink_thumb_for_html(raw, max_px=260):
    """网页版内嵌缩图：小图原样用，大图自己解码缩小后重编码 PNG。"""
    if not raw:
        return b""
    if len(raw) <= THUMB_MAX_BYTES:
        return raw
    if raw[:2] == b"\xff\xd8":
        w, h = jpeg_dimensions(raw)
        if w * h > MAX_DECODE_PIXELS:
            return b""            # 太大，别再硬解（宁可让上面换后端压）
        try:
            w, h, rgb = decode_jpeg_rgb(raw)
            nw, nh, nrgb = downscale_rgb(w, h, rgb, max_px)
            return encode_png_rgb(nw, nh, nrgb)
        except Exception:
            return raw
    return raw


def data_uri(raw):
    """图片字节 → data URI（网页版内嵌缩图，不依赖任何外部资源）。"""
    if not raw:
        return ""
    return "data:%s;base64,%s" % (sniff_image_mime(raw),
                                  base64.b64encode(raw).decode("ascii"))


def sips_thumb_jpeg(path, max_px=200, quality=60):
    """外部后端直接从原图出一张小 JPEG（网页内嵌用）。

    Sony 的嵌入缩图常是 1600px 的大 JPEG，直接内嵌 120 张网页会好几兆；
    交给 sips / PowerShell 一步出 200px 小图又快又小。
    """
    return shrink_image_bytes(b"", path, max_px, "jpeg", quality)


def small_jpeg_bytes(path, raw, max_px=200, quality=60, osname=None,
                     exe=None):
    """要一张小 JPEG：raw 过大就用 raw（RAW 里的嵌入图），否则压原图。"""
    if raw and len(raw) > THUMB_MAX_BYTES:
        return shrink_image_bytes(raw, path, max_px, "jpeg", quality,
                                  osname, exe)
    return shrink_image_bytes(b"", path, max_px, "jpeg", quality,
                              osname, exe)


def html_thumb_bytes(path, raw, max_px=200, osname=None, exe=None):
    """网页内嵌缩图：优先外部后端出小 JPEG，其次用 exiftool 的原缩图。"""
    d = small_jpeg_bytes(path, raw, max_px, 60, osname, exe)
    if d and len(d) <= 60000:
        return d
    if raw and len(raw) <= 60000:
        return raw
    return shrink_thumb_for_html(raw, max_px) or d or raw


def map_parallel(fn, items, workers=4, on_progress=None, stop=None):
    """把逐项任务摊到几个线程上跑，返回与 items 等长的结果列表。

    抽缩图每张都要起一个 exiftool 子进程（HEIC 还要再起 sips），
    上百张时单线程要几十秒；这里并发跑，配合磁盘缓存就够快了。
    """
    n = len(items)
    results = [None] * n
    if not n:
        return results
    lock = threading.Lock()
    cursor = [0]
    done = [0]

    def run():
        while True:
            with lock:
                if stop is not None and stop():
                    return
                i = cursor[0]
                if i >= n:
                    return
                cursor[0] = i + 1
            try:
                val = fn(items[i], i)
            except Exception:
                val = None
            results[i] = val
            with lock:
                done[0] += 1
                if on_progress:
                    try:
                        on_progress(done[0], n)
                    except Exception:
                        pass

    ts = [threading.Thread(target=run, daemon=True)
          for _ in range(max(1, min(workers, n)))]
    for t in ts:
        t.start()
    for t in ts:
        t.join()
    return results


def regeo_point(key, lat, lon, timeout=10):
    """单点逆地理编码。返回 (地址 或 None, 错误说明)。"""
    if not key:
        return None, "未设置高德 Key"
    try:
        url = ("https://restapi.amap.com/v3/geocode/regeo?"
               + urllib.parse.urlencode(
                   {"key": key, "location": "%.6f,%.6f" % (lon, lat)}))
        data = json.loads(http_get(url, timeout=timeout).decode("utf-8"))
    except Exception as e:
        return None, "网络错误：%s" % e
    if str(data.get("status")) == "1":
        addr = (data.get("regeocode") or {}).get("formatted_address") or ""
        return (addr or "（无地址）"), ""
    return None, str(data.get("info") or "查询失败")


# ============================================================
# 内嵌高德地图组件（Canvas 瓦片渲染，GCJ-02）
# ============================================================
def _merc_y(lat):
    lat = max(min(lat, 85.05112878), -85.05112878)
    return (1 - math.log(math.tan(math.radians(lat))
                         + 1 / math.cos(math.radians(lat))) / _PI) / 2


def _gcj_to_world(lat, lon, zoom):
    n = TILE_SIZE * (1 << zoom)
    return (lon + 180.0) / 360.0 * n, _merc_y(lat) * n


def _world_to_gcj(wx, wy, zoom):
    n = TILE_SIZE * (1 << zoom)
    lon = wx / n * 360.0 - 180.0
    yy = wy / n
    lat = math.degrees(math.atan(math.sinh(_PI * (1 - 2 * yy))))
    return lat, lon


class MapView(tk.Canvas):
    ZOOM_STEP_MS = 40
    MAX_PHOTOS = 600

    def __init__(self, master, ui_queue, app, **kw):
        kw.setdefault("bg", "#E8EAED")
        kw.setdefault("highlightthickness", 0)
        super().__init__(master, **kw)
        self.ui_queue = ui_queue
        self.app = app
        self.zoom = 12
        self.center = (39.909, 116.397)       # GCJ-02
        self.layer = "标准图"
        self.track = []                        # 分段的 GCJ 点 (t, lat, lon, ele, raw)
        self.markers = []                      # (lat, lon, text, color)
        self.photo_marks = []                  # 照片标记 [(lat, lon, text)] GCJ-02
        self.photo_sel = -1                    # 当前选中的照片下标（-1 = 无）
        self._photos = {}                      # (kind,z,x,y) -> PhotoImage
        self._photo_order = []
        self._tile_items = {}                  # (kind,z,x,y) -> 画布 item id
        self._missing = set()                  # 当前视口缺瓦片的 key
        self._tile_ok = 0
        self._tile_fail = 0
        self._last_err = ""
        self._tile_epoch = 0
        self._zoom_pending = 0
        self._zoom_after_id = None
        self._drag_mark = None
        self._drag_total = (0, 0)
        self._loader = TileLoader(ui_queue, workers=4)

        self.bind("<Configure>", lambda e: self.redraw())
        self.bind("<MouseWheel>", self._on_wheel)          # macOS / Win
        self.bind("<Button-4>", self._on_wheel)            # Linux
        self.bind("<Button-5>", self._on_wheel)
        self.bind("<ButtonPress-1>", self._on_press)
        self.bind("<B1-Motion>", self._on_drag)
        self.bind("<ButtonRelease-1>", self._on_release)
        self.bind("<Motion>", self._on_motion)
        self.bind("<Leave>", lambda e: self.app.show_coords(""))
        self.bind("<Double-Button-1>", lambda e: self.fit_all())

    # ---------- 几何 ----------
    def _origin(self):
        cw = max(self.winfo_width(), 10)
        ch = max(self.winfo_height(), 10)
        cx, cy = _gcj_to_world(self.center[0], self.center[1], self.zoom)
        return cx - cw / 2.0, cy - ch / 2.0

    # ---------- 绘制 ----------
    def redraw(self):
        """全量重建画布（仅缩放/平移/换层/换轨迹/窗口尺寸变化时调用）。

        瓦片到达时走 on_tile 增量插入，不再 delete("all") 重建整块画布——
        频繁全量重建在 macOS 上会出现黑色残影和明显闪烁。
        """
        self.delete("all")
        self._tile_items.clear()
        self._missing.clear()
        cw = self.winfo_width()
        ch = self.winfo_height()
        if cw < 10 or ch < 10:
            return
        ox, oy = self._origin()
        z = self.zoom
        kinds = dict(MAP_LAYERS)[self.layer]
        tx0 = int(math.floor(ox / TILE_SIZE))
        ty0 = int(math.floor(oy / TILE_SIZE))
        tx1 = int(math.floor((ox + cw) / TILE_SIZE))
        ty1 = int(math.floor((oy + ch) / TILE_SIZE))
        n = 1 << z
        for ty in range(ty0, ty1 + 1):
            if ty < 0 or ty >= n:
                continue
            for tx in range(tx0, tx1 + 1):
                wx = tx * TILE_SIZE - ox
                wy = ty * TILE_SIZE - oy
                for kind in kinds:
                    key = (kind, z, tx % n, ty)
                    photo = self._photos.get(key)
                    if photo is None:
                        # 缺瓦片时不放任何 item，直接透出画布灰底（绝不会黑块）
                        self._missing.add(key)
                        self._request_tile(kind, z, tx % n, ty)
                    else:
                        item = self.create_image(wx, wy, image=photo,
                                                 anchor="nw", tags="tile")
                        self._tile_items[key] = item
        self._draw_track(ox, oy)
        self._draw_photo_marks(ox, oy)
        self._draw_markers(ox, oy)
        self._update_hint()
        self.app.update_tile_status(self._tile_ok, self._tile_fail,
                                    len(self._missing))

    def _update_hint(self):
        """一张瓦片都没成功时，直接说清原因，别让用户对着灰底猜。"""
        self.delete("hint")
        if self._tile_ok > 0 or self._tile_fail == 0:
            return
        lines = ["地图瓦片加载失败（%d 张）" % self._tile_fail,
                 self._last_err or "未知原因"]
        note = ssl_note()
        if note:
            lines.append(note)
        lines.append("请检查网络或代理设置，然后点「重载地图」重试")
        cw = max(self.winfo_width(), 10)
        ch = max(self.winfo_height(), 10)
        self.create_text(cw / 2, ch / 2, text="\n".join(lines),
                         justify="center", tags="hint",
                         font=(self.app.font_name, 12), fill="#B00020")

    def reload_tiles(self, forget_cache=True):
        """重载地图：清空失败记录（默认连磁盘缓存一起清）后重新拉取。"""
        try:
            self._loader.reset_failures(forget_cache=forget_cache)
        except Exception:
            pass
        self._tile_ok = 0
        self._tile_fail = 0
        self._last_err = ""
        self._tile_epoch += 1
        self.redraw()

    def _trim_photos(self):
        """限量回收 PhotoImage——但绝不回收当前视口正在显示的。"""
        if len(self._photo_order) <= self.MAX_PHOTOS:
            return
        active = set(self._tile_items) | self._missing
        drop = len(self._photo_order) - self.MAX_PHOTOS
        keep = []
        for key in self._photo_order:
            if drop > 0 and key not in active:
                self._photos.pop(key, None)
                drop -= 1
            else:
                keep.append(key)
        self._photo_order = keep

    def _request_tile(self, kind, z, x, y):
        epoch = self._tile_epoch
        self.after(80, lambda: self._still_want(epoch, kind, z, x, y)
                   and self._loader.request(kind, z, x, y))

    def _still_want(self, epoch, kind, z, x, y):
        return epoch == self._tile_epoch

    def _draw_track(self, ox, oy):
        if not self.track:
            return
        z = self.zoom
        # 外白内蓝：标准图上干净，卫星图上也可辨认；分段绘制避免段间假连线
        for width, color in ((7, "#FFFFFF"), (4, "#1E6FFF")):
            for seg in self.track:
                coords = []
                for (t, lat, lon, ele, raw) in seg:
                    wx, wy = _gcj_to_world(lat, lon, z)
                    coords.extend((wx - ox, wy - oy))
                if len(coords) >= 4:
                    self.create_line(*coords, width=width, fill=color,
                                     capstyle="round", joinstyle="round")

    def _draw_markers(self, ox, oy):
        z = self.zoom
        fnt = (self.app.font_name, 11, "bold")
        cw = self.winfo_width()
        ch = self.winfo_height()
        for (lat, lon, text, color) in self.markers:
            wx, wy = _gcj_to_world(lat, lon, z)
            x, y = wx - ox, wy - oy
            if x < -40 or y < -40 or x > cw + 40 or y > ch + 40:
                continue
            self.create_oval(x - 7, y - 7, x + 7, y + 7, fill=color,
                             outline="#FFFFFF", width=2)
            self.create_text(x + 11, y, text=text, anchor="w", fill="#FFFFFF",
                             font=fnt)          # 描边
            self.create_text(x + 10, y, text=text, anchor="w",
                             fill="#1A1A1A", font=fnt)

    # ---------- 照片标记 ----------
    def _draw_photo_marks(self, ox, oy):
        """所有带 GPS 的照片画小圆点；选中那张画大一圈并加白边高亮。

        照片动辄上百张，圆点故意画小、不做文字标注，避免糊满地图。
        """
        if not self.photo_marks:
            return
        z = self.zoom
        cw = self.winfo_width()
        ch = self.winfo_height()
        sel = self.photo_sel
        # 先画普通点，再画选中点（保证选中点压在最上层）
        for i, mark in enumerate(self.photo_marks):
            if i == sel:
                continue
            lat, lon = mark[0], mark[1]
            wx, wy = _gcj_to_world(lat, lon, z)
            x, y = wx - ox, wy - oy
            if x < -12 or y < -12 or x > cw + 12 or y > ch + 12:
                continue
            self.create_oval(x - 4, y - 4, x + 4, y + 4, fill="#FF8A00",
                             outline="#FFFFFF", width=1, tags="photopin")
        if 0 <= sel < len(self.photo_marks):
            lat, lon = self.photo_marks[sel][0], self.photo_marks[sel][1]
            wx, wy = _gcj_to_world(lat, lon, z)
            x, y = wx - ox, wy - oy
            self.create_oval(x - 11, y - 11, x + 11, y + 11,
                             outline="#FFFFFF", width=3, tags="photopin")
            self.create_oval(x - 8, y - 8, x + 8, y + 8, fill="#E4572E",
                             outline="#FFFFFF", width=2, tags="photopin")

    def _hit_photo(self, px, py, tol=12):
        """屏幕坐标 (px,py) 命中的照片下标；没命中返回 -1。"""
        if not self.photo_marks:
            return -1
        ox, oy = self._origin()
        z = self.zoom
        best, best_d = -1, tol * tol
        for i, mark in enumerate(self.photo_marks):
            wx, wy = _gcj_to_world(mark[0], mark[1], z)
            dx, dy = wx - ox - px, wy - oy - py
            d = dx * dx + dy * dy
            if d <= best_d:
                best, best_d = i, d
        return best

    def set_photos(self, marks):
        """marks: [(lat, lon, text)]（GCJ-02）。"""
        self.photo_marks = list(marks or [])
        if self.photo_sel >= len(self.photo_marks):
            self.photo_sel = -1
        self.redraw()

    def clear_photos(self):
        self.photo_marks = []
        self.photo_sel = -1
        self.redraw()

    def select_photo(self, idx, pan=True):
        """选中照片：高亮 + （必要时）平移视口让标记可见。"""
        self.photo_sel = idx if 0 <= idx < len(self.photo_marks) else -1
        if pan and self.photo_sel >= 0:
            self.ensure_visible(*self.photo_marks[self.photo_sel][:2])
        self.redraw()

    def ensure_visible(self, lat, lon):
        """点不在视口中央区域时，把它平移到视口中心（尽量少动）。"""
        cw = max(self.winfo_width(), 10)
        ch = max(self.winfo_height(), 10)
        ox, oy = self._origin()
        wx, wy = _gcj_to_world(lat, lon, self.zoom)
        x, y = wx - ox, wy - oy
        mx, my = cw * 0.18, ch * 0.18
        if mx <= x <= cw - mx and my <= y <= ch - my:
            return False
        self.center = (lat, lon)
        self._tile_epoch += 1
        return True

    def fit_points(self, pts):
        """把一组 (lat, lon) 适配进视口（pts 为空时返回 False）。"""
        pts = [p for p in (pts or []) if p]
        if not pts:
            return False
        lats = [p[0] for p in pts]
        lons = [p[1] for p in pts]
        cw = max(self.winfo_width(), 100)
        ch = max(self.winfo_height(), 100)
        best = ZOOM_MIN
        for z in range(ZOOM_MAX, ZOOM_MIN - 1, -1):
            x0, y0 = _gcj_to_world(max(lats), min(lons), z)
            x1, y1 = _gcj_to_world(min(lats), max(lons), z)
            if abs(x1 - x0) <= cw - 100 and abs(y1 - y0) <= ch - 100:
                best = z
                break
        self.zoom = best
        self.center = ((max(lats) + min(lats)) / 2.0,
                       (max(lons) + min(lons)) / 2.0)
        self._tile_epoch += 1
        self.redraw()
        return True

    def fit_photos(self):
        self.fit_points([(m[0], m[1]) for m in self.photo_marks])

    def fit_all(self):
        """轨迹 + 照片 + 起终点，一起适配（双击地图 / 「适配全部」）。"""
        pts = [(m[0], m[1]) for m in self.photo_marks]
        pts += [(m[0], m[1]) for m in self.markers]
        pts += [(p[1], p[2]) for seg in self.track for p in seg]
        if not pts:
            return
        self.fit_points(pts)

    # ---------- 交互 ----------
    def _on_wheel(self, event):
        num = getattr(event, "num", None)
        if num == 4:
            step = 1
        elif num == 5:
            step = -1
        else:
            step = 1 if event.delta > 0 else -1
        self._zoom_pending += step
        if self._zoom_after_id is None:
            self._zoom_after_id = self.after(
                self.ZOOM_STEP_MS, self._flush_zoom, event.x, event.y)

    def _flush_zoom(self, px, py):
        self._zoom_after_id = None
        steps = self._zoom_pending
        self._zoom_pending = 0
        if not steps:
            return
        newz = max(ZOOM_MIN, min(ZOOM_MAX, self.zoom + steps))
        if newz == self.zoom:
            return
        cw = max(self.winfo_width(), 1)
        ch = max(self.winfo_height(), 1)
        ox, oy = self._origin()
        # 光标处的地理坐标
        glat, glon = _world_to_gcj(ox + px, oy + py, self.zoom)
        self.zoom = newz
        # 调整中心，使光标下坐标不动
        wx, wy = _gcj_to_world(glat, glon, newz)
        nlat, nlon = _world_to_gcj(wx - (cw / 2 - px), wy - (ch / 2 - py),
                                   newz)
        self.center = (nlat, nlon)
        self._tile_epoch += 1
        self.redraw()

    def _on_press(self, event):
        self._drag_mark = (event.x, event.y)
        self._drag_total = (0, 0)          # 本次拖拽的累计位移

    def _on_drag(self, event):
        if self._drag_mark is None:
            return
        dx = event.x - self._drag_mark[0]
        dy = event.y - self._drag_mark[1]
        if dx or dy:
            self.move("all", dx, dy)
            self._drag_mark = (event.x, event.y)
            tx, ty = self._drag_total
            self._drag_total = (tx + dx, ty + dy)   # 必须累计，否则松手回弹

    def _on_release(self, event):
        if self._drag_mark is None:
            return
        # 把松手点也当成一次移动，保证「画面位移」与「中心位移」完全一致
        self._on_drag(event)
        dx, dy = self._drag_total
        self._drag_mark = None
        self._drag_total = (0, 0)
        if not (dx or dy):
            # 没拖动 = 单击：命中照片标记就选中它
            idx = self._hit_photo(event.x, event.y)
            if idx >= 0:
                self.app.on_photo_picked(idx)
            return
        cw = max(self.winfo_width(), 1)
        ch = max(self.winfo_height(), 1)
        ox, oy = self._origin()
        lat, lon = _world_to_gcj(ox + cw / 2.0 - dx, oy + ch / 2.0 - dy,
                                 self.zoom)
        self.center = (lat, lon)
        self._tile_epoch += 1
        self.redraw()

    def _on_motion(self, event):
        ox, oy = self._origin()
        lat, lon = _world_to_gcj(ox + event.x, oy + event.y, self.zoom)
        wlat, wlon = gcj02_to_wgs84(lat, lon)
        self.app.show_coords("WGS-84: %.5f, %.5f    (GCJ-02: %.5f, %.5f)"
                             % (wlat, wlon, lat, lon))

    # ---------- 对外 ----------
    def set_track(self, segments_gcj, start, end):
        """segments_gcj: 分段 GCJ 点；start/end: (lat, lon)。"""
        self.track = segments_gcj
        self.markers = []
        self._tile_fail = 0            # 换轨迹/换图层时重置失败计数
        self._last_err = ""
        if start:
            self.markers.append((start[0], start[1], "起点", "#2E9E44"))
        if end:
            self.markers.append((end[0], end[1], "终点", "#D93025"))
        if self.photo_marks:
            self.fit_all()
        else:
            self.fit_track()

    def clear_track(self):
        self.track = []
        self.markers = []
        self.redraw()

    def fit_track(self):
        self.fit_points([(p[1], p[2]) for seg in self.track for p in seg])

    def set_layer(self, name):
        self.layer = name
        self._tile_fail = 0            # 换图层重置失败计数
        self._last_err = ""
        self._tile_epoch += 1
        self.redraw()

    def zoom_by(self, steps):
        newz = max(ZOOM_MIN, min(ZOOM_MAX, self.zoom + steps))
        if newz == self.zoom:
            return
        self.zoom = newz
        self._tile_epoch += 1
        self.redraw()

    # ---------- 瓦片结果 ----------
    def on_tile(self, kind, z, x, y, raw, err=""):
        key = (kind, z, x, y)
        if raw is None:
            self._tile_fail += 1
            if err:
                self._last_err = err
            self._update_hint()
            self.app.update_tile_status(self._tile_ok, self._tile_fail,
                                        len(self._missing))
            return
        if key in self._photos:
            return
        photo = self._make_photo(kind, raw)
        if photo is None:
            self._tile_fail += 1
            self._last_err = "瓦片解码失败（内容不是有效图片）"
            self._update_hint()
            return
        self._photos[key] = photo
        self._photo_order.append(key)
        self._trim_photos()
        self._tile_ok += 1
        # 增量插入：只补这一张，不重建整个画布
        if z == self.zoom and key in self._missing and \
                kind in dict(MAP_LAYERS)[self.layer]:
            ox, oy = self._origin()
            wx = x * TILE_SIZE - ox
            wy = y * TILE_SIZE - oy
            item = self.create_image(wx, wy, image=photo, anchor="nw",
                                     tags="tile")
            self.tag_lower("tile")          # 始终垫在轨迹线下方
            self._tile_items[key] = item
            self._missing.discard(key)
        self._update_hint()
        self.app.update_tile_status(self._tile_ok, self._tile_fail,
                                    len(self._missing))

    def _make_photo(self, kind, raw):
        # 瓦片都是 256px 小图，不走缩放；但要过一遍尺寸上限，
        # 万一缓存里混进大图也不会把界面卡住。
        payload, tfmt, _note = prepare_photo_payload(raw)
        if not payload:
            return None
        try:
            return tk.PhotoImage(data=payload, format=tfmt)
        except Exception:
            return None


class ScrollFrame(ttk.Frame):
    """竖向可滚动容器。

    照片信息项比较多，窗口压到最小尺寸时会超出一屏，套一层滚动最省事。
    """

    def __init__(self, master, bg="#F5F6F8", **kw):
        super().__init__(master, **kw)
        self.canvas = tk.Canvas(self, highlightthickness=0, bd=0, bg=bg)
        self.vs = ttk.Scrollbar(self, orient="vertical",
                                command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vs.set)
        self.vs.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)
        self.body = ttk.Frame(self.canvas, style="Info.TFrame")
        self._win = self.canvas.create_window((0, 0), window=self.body,
                                              anchor="nw")
        self.body.bind("<Configure>", self._sync)
        self.canvas.bind("<Configure>", self._sync)
        for w in (self.canvas, self.body):
            w.bind("<MouseWheel>", self._wheel)
            w.bind("<Button-4>", self._wheel)
            w.bind("<Button-5>", self._wheel)

    def _sync(self, event=None):
        try:
            self.canvas.configure(scrollregion=self.canvas.bbox("all"))
            self.canvas.itemconfigure(self._win,
                                      width=self.canvas.winfo_width())
        except tk.TclError:
            pass

    def _wheel(self, event):
        num = getattr(event, "num", None)
        if num == 4:
            d = -1
        elif num == 5:
            d = 1
        else:
            d = -1 if getattr(event, "delta", 0) > 0 else 1
        try:
            self.canvas.yview_scroll(d * 2, "units")
        except tk.TclError:
            pass

    def reset_scroll(self):
        try:
            self.canvas.yview_moveto(0)
        except tk.TclError:
            pass


# ============================================================
# 主界面
# ============================================================
class App(object):
    def __init__(self, root):
        self.root = root
        self.ui_queue = queue_mod.Queue()
        self.cfg = load_config()
        self.font_name = pick_font()
        self.stats = None
        self.track_path = None
        self._key_validating = False
        # ---- 照片状态 ----
        self.photo_dir = None
        self.photos = []            # [photo_info_from_exif(...)]，目录全量
        self.order = []             # 列表展示顺序（photos 的下标序列）
        self.geo_photos = []        # 有 GPS 的照片在 photos 中的下标
        self.photo_sel = -1         # 当前选中照片（photos 下标）
        self._addr_cache = {}       # "lat,lon" -> 地址
        self._thumb_ref = None      # 持有缩图引用，防止被 GC 回收
        self._full_ref = None
        self._scan_token = 0        # 扫描代次：过期结果直接丢弃
        self._in_select = False     # 防止列表选中 ↔ 地图点击互相回调
        self._html_worker = None

        root.title(APP_TITLE)
        root.geometry("1280x820")
        root.minsize(1000, 640)

        style = ttk.Style(root)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        # macOS 深色模式下 tk.Tk 默认背景是深灰(#323232)，布局留白处会露出
        # 一圈黑条；统一改成 clam 主题底色，让缝隙与控件浑然一体。
        try:
            theme_bg = style.lookup("TFrame", "background") or "#DCDAD5"
        except tk.TclError:
            theme_bg = "#DCDAD5"
        root.configure(bg=theme_bg)
        base = (self.font_name, 12)
        small = (self.font_name, 11)
        bold = (self.font_name, 12, "bold")
        style.configure(".", font=base)
        style.configure("TButton", padding=(10, 5))
        style.configure("Info.TLabelframe.Label", font=bold)
        style.configure("Val.TLabel", font=small, background="#F5F6F8")
        style.configure("Info.TFrame", background="#F5F6F8")
        style.configure("Head.TLabel", font=(self.font_name, 11, "bold"),
                        background="#F5F6F8")
        style.configure("Kw.TLabel", font=(self.font_name, 10),
                        foreground="#5A6270", background="#F5F6F8")

        self._build_topbar()
        self._build_photobar()
        self._build_main()
        self._build_statusbar()

        root.protocol("WM_DELETE_WINDOW", self.on_exit)
        root.after(80, self._poll_queue)
        self.set_key_status()

    # ---------- 布局 ----------
    def _build_topbar(self):
        bar = ttk.Frame(self.root, padding=(10, 8, 10, 2))
        bar.pack(side="top", fill="x")
        ttk.Button(bar, text="📂 选择轨迹文件",
                   command=self.on_pick_file).pack(side="left")
        self.var_file = tk.StringVar(value="（尚未选择轨迹文件）")
        entry = ttk.Entry(bar, textvariable=self.var_file, state="readonly")
        entry.pack(side="left", fill="x", expand=True, padx=(10, 10))
        ttk.Button(bar, text="🔑 设置高德Key",
                   command=self.on_set_key).pack(side="left")
        ttk.Button(bar, text="🌐 浏览器打开",
                   command=self.on_open_browser).pack(side="left", padx=(8, 0))
        ttk.Button(bar, text="退出",
                   command=self.on_exit).pack(side="left", padx=(8, 0))

    def _build_photobar(self):
        bar = ttk.Frame(self.root, padding=(10, 0, 10, 4))
        bar.pack(side="top", fill="x")
        ttk.Button(bar, text="📁 选择照片目录",
                   command=self.on_pick_photo_dir).pack(side="left")
        self.var_photodir = tk.StringVar(value="（尚未选择照片目录）")
        ttk.Entry(bar, textvariable=self.var_photodir,
                  state="readonly").pack(side="left", fill="x", expand=True,
                                         padx=(10, 10))
        self.var_recursive = tk.BooleanVar(value=False)
        ttk.Checkbutton(bar, text="含子目录", variable=self.var_recursive,
                        command=self.rescan_photos).pack(side="left")
        self.var_only_gps = tk.BooleanVar(value=False)
        ttk.Checkbutton(bar, text="只看有GPS", variable=self.var_only_gps,
                        command=self.refill_photo_list).pack(side="left",
                                                             padx=(10, 0))
        ttk.Label(bar, text="排序").pack(side="left", padx=(10, 2))
        self.var_sort = tk.StringVar(value="文件名")
        cb = ttk.Combobox(bar, textvariable=self.var_sort, state="readonly",
                          width=9,
                          values=("文件名", "拍摄时间", "GPS优先"))
        cb.pack(side="left")
        cb.bind("<<ComboboxSelected>>",
                lambda e: self.refill_photo_list())
        ttk.Button(bar, text="🔄 重新扫描",
                   command=self.rescan_photos).pack(side="left", padx=(10, 0))

    def _info_row(self, parent, label, width=12):
        f = ttk.Frame(parent, style="Info.TFrame")
        f.pack(fill="x", pady=1)
        ttk.Label(f, text=label, width=width, anchor="e",
                  style="Kw.TLabel").pack(side="left")
        var = tk.StringVar(value="—")
        ttk.Label(f, textvariable=var, style="Val.TLabel", anchor="w",
                  justify="left").pack(side="left", fill="x", expand=True,
                                       padx=(6, 0))
        return var

    def _head(self, parent, text, pady=(8, 2)):
        ttk.Label(parent, text=text, style="Head.TLabel").pack(anchor="w",
                                                               pady=pady)

    def _build_main(self):
        pane = ttk.PanedWindow(self.root, orient="horizontal")
        pane.pack(side="top", fill="both", expand=True, padx=10, pady=4)

        # ---- 左：照片列表 ----
        listf = ttk.Labelframe(pane, text="照片列表", padding=(6, 4, 6, 6))
        pane.add(listf, weight=0)
        self.var_photocount = tk.StringVar(value="0 张（带 GPS 0 张）")
        ttk.Label(listf, textvariable=self.var_photocount,
                  style="Val.TLabel").pack(anchor="w", pady=(0, 3))
        wrap = ttk.Frame(listf)
        wrap.pack(fill="both", expand=True)
        self.tree = ttk.Treeview(wrap, columns=("name", "time", "gps"),
                                 show="headings", selectmode="browse")
        self.tree.heading("name", text="文件名")
        self.tree.heading("time", text="拍摄时间")
        self.tree.heading("gps", text="GPS")
        self.tree.column("name", width=168, anchor="w", stretch=True)
        self.tree.column("time", width=136, anchor="w", stretch=False)
        self.tree.column("gps", width=44, anchor="center", stretch=False)
        vs = ttk.Scrollbar(wrap, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vs.set)
        self.tree.pack(side="left", fill="both", expand=True)
        vs.pack(side="left", fill="y")
        self.tree.bind("<<TreeviewSelect>>", self.on_tree_select)
        self.tree.tag_configure("nogps", foreground="#9AA0A6")

        # ---- 中：信息面板（轨迹 / 照片 两个页签） ----
        self.nb = ttk.Notebook(pane)
        pane.add(self.nb, weight=0)

        tab_tr = ttk.Frame(self.nb, padding=8)
        self.nb.add(tab_tr, text=" 轨迹信息 ")
        self._build_track_tab(tab_tr)

        tab_ph = ttk.Frame(self.nb, padding=0)
        self.nb.add(tab_ph, text=" 照片信息 ")
        self._build_photo_tab(tab_ph)

        # ---- 右：地图 ----
        mapf = ttk.Labelframe(pane, text="高德地图", padding=6)
        pane.add(mapf, weight=1)

        bar = ttk.Frame(mapf)
        bar.pack(side="top", fill="x", pady=(0, 4))
        self.var_layer = tk.StringVar(value="标准图")
        for name, _ in MAP_LAYERS:
            ttk.Radiobutton(bar, text=name, value=name,
                            variable=self.var_layer,
                            command=self.on_layer).pack(side="left")
        ttk.Button(bar, text="＋", width=3,
                   command=lambda: self.map.zoom_by(1)).pack(side="left",
                                                             padx=(14, 2))
        ttk.Button(bar, text="－", width=3,
                   command=lambda: self.map.zoom_by(-1)).pack(side="left",
                                                              padx=2)
        ttk.Button(bar, text="适配轨迹",
                   command=lambda: self.map.fit_track()).pack(side="left",
                                                              padx=2)
        ttk.Button(bar, text="适配照片",
                   command=lambda: self.map.fit_photos()).pack(side="left",
                                                               padx=2)
        ttk.Button(bar, text="适配全部",
                   command=lambda: self.map.fit_all()).pack(side="left",
                                                            padx=2)
        ttk.Button(bar, text="🔄 重载地图",
                   command=self.on_reload_tiles).pack(side="left", padx=(8, 2))
        self.var_mapinfo = tk.StringVar(value="滚轮缩放 · 拖拽平移 · 双击适配")
        ttk.Label(bar, textvariable=self.var_mapinfo,
                  style="Val.TLabel").pack(side="right")

        self.map = MapView(mapf, self.ui_queue, self)
        self.map.pack(side="top", fill="both", expand=True)

    def _build_track_tab(self, info):
        def row(parent, label):
            return self._info_row(parent, label)

        self.var_fmt = row(info, "格式")
        self.var_points = row(info, "轨迹点数")
        self.var_dist = row(info, "总距离")
        self.var_devdist = row(info, "设备记录")
        self.var_dur = row(info, "时间跨度")

        ttk.Separator(info).pack(fill="x", pady=6)

        f = ttk.Frame(info)
        f.pack(fill="x", pady=(0, 2))
        ttk.Label(f, text="时间口径", width=12, anchor="e").pack(side="left")
        self.var_mode = tk.StringVar(value="按标准时区解析")
        cb = ttk.Combobox(f, textvariable=self.var_mode, state="readonly",
                          values=("按标准时区解析", "小米导出(墙钟挂Z)"),
                          width=17)
        cb.pack(side="left", padx=(6, 0))
        cb.bind("<<ComboboxSelected>>", lambda e: self.refresh_times())

        ttk.Label(info, text="小米等设备导出的 Z 常是本地墙钟，\n"
                             "数字若差 8 小时请切换口径核对。",
                  style="Kw.TLabel", justify="left").pack(
            fill="x", pady=(2, 6))

        ttk.Label(info, text="UTC 时间（文件 Z 值）", style="Head.TLabel",
                  font=(self.font_name, 11, "bold")).pack(anchor="w")
        self.var_utc_start = row(info, "开始")
        self.var_utc_end = row(info, "结束")

        f = ttk.Frame(info)
        f.pack(fill="x", pady=(4, 2))
        ttk.Label(f, text="时区", width=12, anchor="e").pack(side="left")
        self.var_tz = tk.StringVar(value="8.0")
        spin = ttk.Spinbox(f, from_=-12.0, to=14.0, increment=0.5,
                           textvariable=self.var_tz, width=6,
                           command=self.refresh_times)
        spin.pack(side="left", padx=(6, 4))
        spin.bind("<Return>", lambda e: self.refresh_times())
        spin.bind("<FocusOut>", lambda e: self.refresh_times())
        ttk.Label(f, text="(UTC+小时，如中国填 8)",
                  style="Kw.TLabel").pack(side="left")

        ttk.Label(info, text="本地时间", style="Head.TLabel",
                  font=(self.font_name, 11, "bold")).pack(anchor="w",
                                                          pady=(6, 0))
        self.var_local_start = row(info, "开始")
        self.var_local_end = row(info, "结束")

        ttk.Separator(info).pack(fill="x", pady=6)
        self.var_start_addr = row(info, "起点")
        self.var_end_addr = row(info, "终点")
        self.var_start_coord = row(info, "起点坐标")
        self.var_end_coord = row(info, "终点坐标")

    def _build_photo_tab(self, host):
        sf = ScrollFrame(host)
        sf.pack(fill="both", expand=True)
        self.photo_scroll = sf
        body = ttk.Frame(sf.body, padding=8, style="Info.TFrame")
        body.pack(fill="both", expand=True)

        # 缩图预览
        hold = ttk.Frame(body, style="Info.TFrame")
        hold.pack(fill="x", pady=(0, 4))
        self.lbl_thumb = tk.Label(hold, text="（点击左侧照片查看缩图）",
                                  bg="#F5F6F8", fg="#7A8290",
                                  font=(self.font_name, 11), height=8)
        self.lbl_thumb.pack(fill="x")

        self.var_ph_thumb_src = self._info_row(body, "缩图", width=10)

        self.var_ph_name = self._info_row(body, "文件名", width=10)
        self.var_ph_path = self._info_row(body, "完整路径", width=10)
        self.var_ph_time = self._info_row(body, "拍摄时间", width=10)
        self.var_ph_cam = self._info_row(body, "相机", width=10)
        self.var_ph_lens = self._info_row(body, "镜头", width=10)
        self.var_ph_exp = self._info_row(body, "曝光", width=10)
        self.var_ph_size = self._info_row(body, "尺寸", width=10)
        self.var_ph_fsize = self._info_row(body, "文件大小", width=10)

        ttk.Separator(body).pack(fill="x", pady=6)
        self._head(body, "鸟种识别（bird_scanner）", pady=(0, 2))
        self.var_ph_bird = self._info_row(body, "识别结果", width=10)

        ttk.Separator(body).pack(fill="x", pady=6)
        self._head(body, "原始 GPS（EXIF / WGS-84）", pady=(0, 2))
        self.var_ph_wgs = self._info_row(body, "经纬度", width=10)
        self.var_ph_alt = self._info_row(body, "海拔", width=10)
        self.var_ph_dir = self._info_row(body, "拍摄方向", width=10)

        ttk.Separator(body).pack(fill="x", pady=6)
        self._head(body, "高德坐标（GCJ-02）", pady=(0, 2))
        self.var_ph_gcj = self._info_row(body, "经纬度", width=10)

        self._head(body, "地址", pady=(6, 2))
        self.var_ph_addr = tk.StringVar(value="—")
        ttk.Label(body, textvariable=self.var_ph_addr, style="Val.TLabel",
                  anchor="w", justify="left", wraplength=300).pack(
            fill="x", padx=(6, 0))

        f = ttk.Frame(body, style="Info.TFrame")
        f.pack(fill="x", pady=(10, 2))
        ttk.Button(f, text="查看全部 EXIF",
                   command=self.on_show_all_exif).pack(side="left")
        ttk.Button(f, text="在访达中显示",
                   command=self.on_reveal_in_finder).pack(side="left",
                                                          padx=(6, 0))
        ttk.Button(f, text="定位到地图",
                   command=self.on_locate_photo).pack(side="left",
                                                      padx=(6, 0))

    def _build_statusbar(self):
        bar = ttk.Frame(self.root, padding=(10, 2, 10, 6))
        bar.pack(side="bottom", fill="x")
        self.var_coords = tk.StringVar(value="")
        ttk.Label(bar, textvariable=self.var_coords, width=52,
                  style="Val.TLabel").pack(side="left")
        self.var_status = tk.StringVar(value="就绪")
        ttk.Label(bar, textvariable=self.var_status,
                  style="Val.TLabel").pack(side="right")

    # ---------- 状态 ----------
    def show_coords(self, text):
        self.var_coords.set(text)

    def set_status(self, text):
        self.var_status.set(text)

    def update_tile_status(self, ok, fail, missing):
        """地图瓦片进度/失败反馈（由 MapView 回调）。"""
        m = getattr(self, "map", None)      # 布局早期可能尚未挂上地图
        if m is None:
            return
        note = ssl_note()
        if fail and ok == 0:
            msg = "瓦片加载失败 %d 张：%s" % (fail,
                                              (m._last_err or "?")[:58])
            if note:
                msg += "（%s）" % note
            self.set_status(msg)
        elif missing:
            self.set_status("地图瓦片：已加载 %d 张，%d 张下载中…" % (ok, missing))
        elif ok:
            self.set_status("地图瓦片：已加载 %d 张" % ok)

    def set_key_status(self):
        key = self.cfg.get("amap_key") or ""
        if key:
            self.var_mapinfo.set("Key: %s…%s" % (key[:4], key[-4:]))
        else:
            self.var_mapinfo.set("未设置高德 Key（地图浏览不需要，逆地理需要）")

    # ---------- 照片：目录与扫描 ----------
    def on_pick_photo_dir(self):
        d = filedialog.askdirectory(title="选择照片目录",
                                    mustexist=True)
        if not d:
            return
        self.photo_dir = d
        self.var_photodir.set(d)
        self.rescan_photos()

    def rescan_photos(self):
        if not self.photo_dir:
            messagebox.showinfo("提示", "请先选择照片目录。")
            return
        if not EXIFTOOL:
            messagebox.showerror(
                "缺少 exiftool",
                "没有找到 exiftool，无法读取照片 EXIF 与缩图。\n\n"
                "请先安装：macOS 用 Homebrew 执行 `brew install exiftool`，"
                "或到 https://exiftool.org 下载。")
            return
        self._scan_token += 1
        token = self._scan_token
        d = self.photo_dir
        rec = bool(self.var_recursive.get())
        cache_clear()                       # 重扫时顺带清掉缩图缓存
        self.set_status("正在扫描照片目录…")

        def work():
            try:
                files = list_photo_files(d, recursive=rec)
                if not files:
                    self.ui_queue.put(("photos", token, [],
                                       "该目录下没有找到照片文件"))
                    return

                def prog(done, total):
                    if token == self._scan_token:
                        self.ui_queue.put(("photoprog", token, done, total))

                exif = read_photos_exif(
                    files, on_progress=prog,
                    stop=lambda: token != self._scan_token)
                infos = [photo_info_from_exif(exif.get(p), p) for p in files]
                self.ui_queue.put(("photos", token, infos, None))
            except Exception:
                self.ui_queue.put(("photos", token, None,
                                   traceback.format_exc()))

        threading.Thread(target=work, daemon=True).start()

    def _on_photos_scanned(self, token, infos, err):
        if token != self._scan_token:
            return                          # 已有更新的扫描，丢弃
        if err:
            self.set_status("扫描照片失败")
            messagebox.showerror("扫描失败", err)
            return
        self.photos = infos or []
        self.geo_photos = []
        marks = []
        for i, info in enumerate(self.photos):
            info["gcj"] = None
            if info.get("ok_gps"):
                lat, lon = float(info["lat"]), float(info["lon"])
                glat, glon = wgs84_to_gcj02(lat, lon)
                info["gcj"] = (glat, glon)
                self.geo_photos.append(i)
                marks.append((glat, glon, info.get("name") or ""))
        self.photo_sel = -1
        self.map.set_photos(marks)
        self.refill_photo_list()
        self._clear_photo_info()
        if not self.photos:
            self.set_status("该目录下没有找到照片文件")
            return
        if self.geo_photos:
            self.map.fit_photos()
        self.set_status("已扫描 %d 张照片，其中 %d 张带 GPS"
                        % (len(self.photos), len(self.geo_photos)))

    def _sorted_indices(self):
        """按当前排序/过滤设置，返回展示用的 photos 下标列表。"""
        idx = list(range(len(self.photos)))
        only = bool(self.var_only_gps.get())
        if only:
            idx = [i for i in idx if self.photos[i].get("ok_gps")]
        mode = self.var_sort.get()
        if mode == "拍摄时间":
            idx.sort(key=lambda i: (self.photos[i].get("dt") or "~",
                                    self.photos[i].get("name") or ""))
        elif mode == "GPS优先":
            idx.sort(key=lambda i: (0 if self.photos[i].get("ok_gps") else 1,
                                    self.photos[i].get("dt") or "~",
                                    self.photos[i].get("name") or ""))
        else:
            idx.sort(key=lambda i: (self.photos[i].get("name") or "").lower())
        return idx

    def refill_photo_list(self):
        """重建照片列表（排序/过滤变化与扫描完成后调用）。"""
        try:
            self.tree.delete(*self.tree.get_children())
        except tk.TclError:
            return
        self.order = self._sorted_indices()
        for i in self.order:
            info = self.photos[i]
            dt = fmt_exif_dt(info.get("dt"))
            has = "✓" if info.get("ok_gps") else ""
            self.tree.insert("", "end", iid=str(i),
                             values=(info.get("name") or "?",
                                     dt[5:] if len(dt) > 10 else dt, has),
                             tags=() if info.get("ok_gps") else ("nogps",))
        total = len(self.photos)
        n_gps = len(self.geo_photos)
        extra = ""
        if self.order is not None and len(self.order) != total:
            extra = "，当前显示 %d 张" % len(self.order)
        self.var_photocount.set("%d 张（带 GPS %d 张）%s"
                                % (total, n_gps, extra))
        if self.photo_sel >= 0:
            self._select_tree_row(self.photo_sel)

    # ---------- 照片：选中与信息 ----------
    def _select_tree_row(self, i):
        iid = str(i)
        try:
            if not self.tree.exists(iid):
                return
            self.tree.selection_set(iid)
            self.tree.see(iid)
        except tk.TclError:
            pass

    def on_tree_select(self, event=None):
        if self._in_select:
            return
        sel = self.tree.selection()
        if not sel:
            return
        try:
            i = int(sel[0])
        except (TypeError, ValueError):
            return
        self._in_select = True
        try:
            self.select_photo(i, from_tree=True)
        finally:
            self._in_select = False

    def on_photo_picked(self, gi):
        """地图上点了照片标记（gi 是 geo_photos 下标）。"""
        if not (0 <= gi < len(self.geo_photos)):
            return
        i = self.geo_photos[gi]
        self._in_select = True
        try:
            self._select_tree_row(i)
            self.select_photo(i, from_tree=False)
        finally:
            self._in_select = False

    def select_photo(self, i, from_tree=False):
        if not (0 <= i < len(self.photos)):
            return
        self.photo_sel = i
        info = self.photos[i]
        self._show_photo_info(info)
        gi = self._geo_index_of(i)
        if gi >= 0:
            self.map.select_photo(gi, pan=True)
        else:
            self.map.photo_sel = -1
            self.map.redraw()
        self.nb.select(1)                   # 自动切到「照片信息」页签
        self._request_thumb(info)
        if info.get("ok_gps"):
            self._request_photo_addr(info)

    def _geo_index_of(self, i):
        try:
            return self.geo_photos.index(i)
        except ValueError:
            return -1

    def _clear_photo_info(self):
        for var in (self.var_ph_name, self.var_ph_path, self.var_ph_time,
                    self.var_ph_cam, self.var_ph_lens, self.var_ph_exp,
                    self.var_ph_size, self.var_ph_fsize, self.var_ph_bird,
                    self.var_ph_wgs,
                    self.var_ph_alt, self.var_ph_dir, self.var_ph_gcj,
                    self.var_ph_thumb_src):
            var.set("—")
        self.var_ph_addr.set("—")
        self._bird_info = None
        self._thumb_ref = None
        self._full_ref = None
        self.lbl_thumb.configure(image="", text="（点击左侧照片查看缩图）",
                                 height=8)

    def _show_photo_info(self, info):
        self.var_ph_name.set(info.get("name") or "?")
        self.var_ph_path.set(info.get("path") or "—")
        dt = fmt_exif_dt(info.get("dt"))
        off = info.get("offset") or ""
        self.var_ph_time.set((dt or "无拍摄时间")
                             + (("  (" + off + ")") if off else ""))
        cam = " ".join(x for x in (info.get("make"), info.get("model")) if x)
        self.var_ph_cam.set(cam or "—")
        self.var_ph_lens.set(info.get("lens") or "—")
        self.var_ph_exp.set(info.get("exposure") or "—")
        size = info.get("size") or "—"
        if info.get("orientation") not in ("", None, 1, "1"):
            size += "（方向 %s）" % info.get("orientation")
        self.var_ph_size.set(size)
        fs = info.get("fsize")
        self.var_ph_fsize.set("%.1f MB" % (fs / 1048576.0)
                              if isinstance(fs, (int, float)) and fs
                              else "—")
        # 鸟种识别（可选）：照片旁有 bird_scanner 生成的 <名字>.bird.json 才显示
        self._bird_info = bird_info_of(info.get("path"))
        self.var_ph_bird.set(bird_summary_text(self._bird_info)
                             or "—（无识别结果）")
        if info.get("err"):
            self.var_ph_thumb_src.set("读取失败：%s" % info["err"])
        else:
            self.var_ph_thumb_src.set("读取中…")
        if info.get("ok_gps"):
            self.var_ph_wgs.set("%.6f, %.6f" % (info["lat"], info["lon"]))
            self.var_ph_alt.set("%.1f m" % info["alt"]
                                if info.get("alt") is not None else "—")
            self.var_ph_dir.set("%.1f°" % info["dir_deg"]
                                if info.get("dir_deg") is not None else "—")
            gcj = info.get("gcj")
            self.var_ph_gcj.set("%.6f, %.6f" % gcj if gcj else "—")
            self.var_ph_addr.set("查询中…" if self.cfg.get("amap_key")
                                 else "—（未设置高德 Key）")
        else:
            why = "读取失败" if info.get("err") else "该照片没有 GPS 信息"
            self.var_ph_wgs.set("—（%s）" % why)
            self.var_ph_alt.set("—")
            self.var_ph_dir.set("—")
            self.var_ph_gcj.set("—")
            self.var_ph_addr.set("—")
        self.photo_scroll.reset_scroll()

    # ---------- 照片：缩图 ----------
    def _request_thumb(self, info):
        path = info.get("path")
        if not path:
            return
        token = self._scan_token

        def work():
            try:
                raw, src = thumb_cached(path)
            except Exception as e:
                raw, src = b"", "取缩图失败：%s" % e
            # 解码也放在这里做，主线程只剩「构造 PhotoImage」一步。
            # 注意：内置解码器是纯 Python，占着解释器照样会拖住界面，
            # 真正兜底的是 prepare_photo_payload 里的尺寸上限。
            try:
                payload, pfmt, note = prepare_photo_payload(raw, THUMB_MAX_PX)
            except Exception as e:
                payload, pfmt, note = b"", "", "解码失败：%s" % e
            if note:
                src = ("%s（%s）" % (src, note)) if src else note
            self.ui_queue.put(("thumb", token, path, payload, pfmt, src))

        threading.Thread(target=work, daemon=True).start()

    def _on_thumb(self, token, path, payload, pfmt, src):
        if token != self._scan_token:
            return
        cur = self.photos[self.photo_sel] if 0 <= self.photo_sel < len(
            self.photos) else None
        if cur is None or cur.get("path") != path:
            return                          # 用户已切到别的照片
        self.var_ph_thumb_src.set(src or "—")
        if not payload:
            self._thumb_ref = None
            self.lbl_thumb.configure(image="", height=8,
                                     text="（%s）" % (src or "取不到缩图"))
            return
        try:
            photo = tk.PhotoImage(data=payload, format=pfmt or "png")
        except Exception:
            photo = None
        if photo is None:
            self._thumb_ref = None
            self.lbl_thumb.configure(image="", height=8,
                                     text="（缩图格式无法显示）")
            return
        small = subsample_photo(photo, 200)
        self._thumb_ref = small                  # 必须持有引用
        self._full_ref = photo if small is not photo else None
        if getattr(self, "_bird_info", None):
            draw_bird_boxes(small, self._bird_info)
        self.lbl_thumb.configure(image=small, text="", height=0)

    # ---------- 照片：地址 ----------
    def _request_photo_addr(self, info):
        key = self.cfg.get("amap_key")
        if not key:
            return
        gcj = info.get("gcj")
        if not gcj:
            return
        ck = "%.5f,%.5f" % gcj
        if ck in self._addr_cache:
            self.var_ph_addr.set(self._addr_cache[ck])
            return

        def work():
            addr, e = regeo_point(key, gcj[0], gcj[1])
            self.ui_queue.put(("phaddr", ck, addr, e))

        threading.Thread(target=work, daemon=True).start()

    def _on_photo_addr(self, ck, addr, err):
        text = addr if addr else "查询失败：%s" % (err or "?")
        self._addr_cache[ck] = text
        cur = self.photos[self.photo_sel] if 0 <= self.photo_sel < len(
            self.photos) else None
        if cur is not None and cur.get("gcj"):
            if "%.5f,%.5f" % cur["gcj"] == ck:
                self.var_ph_addr.set(text)

    # ---------- 照片：其它操作 ----------
    def on_show_all_exif(self):
        if not (0 <= self.photo_sel < len(self.photos)):
            messagebox.showinfo("提示", "请先在左侧点选一张照片。")
            return
        info = self.photos[self.photo_sel]
        path = info.get("path")
        if not path or not EXIFTOOL:
            messagebox.showinfo("提示", "没有可读取的照片。")
            return
        dlg = tk.Toplevel(self.root)
        dlg.title("全部 EXIF —— %s" % (info.get("name") or path))
        dlg.geometry("760x560")
        dlg.transient(self.root)
        frm = ttk.Frame(dlg, padding=8)
        frm.pack(fill="both", expand=True)
        txt = tk.Text(frm, wrap="none", font=("Menlo", 11))
        ysb = ttk.Scrollbar(frm, orient="vertical", command=txt.yview)
        xsb = ttk.Scrollbar(frm, orient="horizontal", command=txt.xview)
        txt.configure(yscrollcommand=ysb.set, xscrollcommand=xsb.set)
        txt.grid(row=0, column=0, sticky="nsew")
        ysb.grid(row=0, column=1, sticky="ns")
        xsb.grid(row=1, column=0, sticky="ew")
        frm.rowconfigure(0, weight=1)
        frm.columnconfigure(0, weight=1)
        txt.insert("1.0", "正在读取…\n")
        txt.configure(state="disabled")

        def work():
            try:
                out, err = read_all_exif_text(path)
                body = out or err or "（无输出）"
            except Exception as e:
                body = "读取失败：%s" % e
            self.ui_queue.put(("exiftext", dlg, txt, body))

        threading.Thread(target=work, daemon=True).start()

    def _on_exif_text(self, dlg, txt, body):
        try:
            if not dlg.winfo_exists():
                return
            txt.configure(state="normal")
            txt.delete("1.0", "end")
            txt.insert("1.0", body)
            txt.configure(state="disabled")
        except tk.TclError:
            pass

    def on_reveal_in_finder(self):
        if not (0 <= self.photo_sel < len(self.photos)):
            messagebox.showinfo("提示", "请先在左侧点选一张照片。")
            return
        path = self.photos[self.photo_sel].get("path")
        if not path:
            return
        try:
            if sys.platform == "darwin":
                subprocess.Popen(["open", "-R", path], **hidden_kw())
            elif sys.platform.startswith("win"):
                subprocess.Popen(["explorer", "/select,", path], **hidden_kw())
            else:
                subprocess.Popen(["xdg-open", os.path.dirname(path)],
                                 **hidden_kw())
        except Exception as e:
            messagebox.showerror("打开失败", str(e))

    def on_locate_photo(self):
        if not (0 <= self.photo_sel < len(self.photos)):
            return
        info = self.photos[self.photo_sel]
        gcj = info.get("gcj")
        if not gcj:
            self.set_status("这张照片没有 GPS 信息，无法在地图上定位")
            return
        self.map.ensure_visible(gcj[0], gcj[1])
        gi = self._geo_index_of(self.photo_sel)
        self.map.select_photo(gi, pan=False)
        self.set_status("已定位到 %s" % (info.get("name") or "照片"))

    # ---------- 队列轮询 ----------
    def _poll_queue(self):
        try:
            while True:
                msg = self.ui_queue.get_nowait()
                kind = msg[0]
                if kind == "tile":
                    self.map.on_tile(*msg[1:])
                elif kind == "track":
                    self._on_track_parsed(*msg[1:])
                elif kind == "keycheck":
                    self._on_key_checked(*msg[1:])
                elif kind == "regeo":
                    self._on_regeo(*msg[1:])
                elif kind == "photos":
                    self._on_photos_scanned(*msg[1:])
                elif kind == "photoprog":
                    _, _tok, done, total = msg
                    if _tok == self._scan_token:
                        self.set_status("正在读取照片信息 %d/%d …"
                                        % (done, total))
                elif kind == "thumb":
                    self._on_thumb(*msg[1:])
                elif kind == "phaddr":
                    self._on_photo_addr(*msg[1:])
                elif kind == "exiftext":
                    self._on_exif_text(*msg[1:])
                elif kind == "html":
                    self._on_html_ready(*msg[1:])
                elif kind == "error":
                    _, where, err = msg
                    self.set_status("出错：%s" % where)
                    messagebox.showerror("错误", "%s：\n%s" % (where, err))
        except queue_mod.Empty:
            pass
        self.root.after(80, self._poll_queue)

    # ---------- 文件 ----------
    def on_pick_file(self):
        path = filedialog.askopenfilename(
            title="选择轨迹文件",
            filetypes=[("轨迹文件", "*.gpx *.tcx *.fit *.GPX *.TCX *.FIT"),
                       ("GPX", "*.gpx *.GPX"),
                       ("TCX", "*.tcx *.TCX"),
                       ("FIT", "*.fit *.FIT"),
                       ("所有文件", "*.*")])
        if not path:
            return
        self.load_track(path)

    def load_track(self, path):
        self.set_status("正在解析 %s …" % os.path.basename(path))
        self.var_file.set(path)

        def work():
            try:
                result = parse_track(path)
                stats = TrackStats(result)
                self.ui_queue.put(("track", path, stats, None))
            except Exception:
                self.ui_queue.put(("track", path, None, traceback.format_exc()))

        threading.Thread(target=work, daemon=True).start()

    def _on_track_parsed(self, path, stats, err):
        if err:
            self.set_status("解析失败")
            messagebox.showerror("解析失败",
                                 "无法解析轨迹文件：\n%s\n\n%s" % (path, err))
            return
        self.track_path = path
        self.stats = stats
        base = os.path.basename(path)
        self.var_fmt.set(stats.fmt + ("  ·  " + stats.name
                                      if stats.name else ""))
        self.var_points.set("%d（有效 %d）" % (stats.n_points, stats.n_valid))
        self.var_dist.set("%.2f km" % (stats.distance_m / 1000.0))
        if stats.device_distance_m:
            diff = abs(stats.device_distance_m - stats.distance_m)
            note = ""
            if stats.distance_m > 0 and diff / stats.distance_m > 0.02:
                note = "（与轨迹点推算差异较大）"
            self.var_devdist.set("%.2f km %s"
                                 % (stats.device_distance_m / 1000.0, note))
        else:
            self.var_devdist.set("—")
        warn = "；".join(stats.warnings)
        self.set_status(("已加载 %s（%s）" % (base, stats.fmt))
                        + (("；" + warn) if warn else ""))
        # 地图
        segs = stats.segments_gcj
        start = (segs[0][0][1], segs[0][0][2]) if segs and segs[0] else None
        end = None
        if segs and segs[-1]:
            end = (segs[-1][-1][1], segs[-1][-1][2])
        self.map.set_track(segs, start, end)
        # 坐标行
        if start:
            wlat, wlon = gcj02_to_wgs84(start[0], start[1])
            self.var_start_coord.set("%.5f, %.5f" % (wlat, wlon))
        else:
            self.var_start_coord.set("—")
        if end:
            wlat, wlon = gcj02_to_wgs84(end[0], end[1])
            self.var_end_coord.set("%.5f, %.5f" % (wlat, wlon))
        else:
            self.var_end_coord.set("—")
        self.var_start_addr.set("查询中…" if self.cfg.get("amap_key")
                                else "—（未设置 Key）")
        self.var_end_addr.set("查询中…" if self.cfg.get("amap_key") else "—")
        self.refresh_times()
        if self.cfg.get("amap_key") and start:
            self._request_regeo(start, end)
        else:
            self.var_start_addr.set("—（未设置 Key）")
            self.var_end_addr.set("—（未设置 Key）")

    # ---------- 时间 ----------
    def _tz_value(self):
        try:
            v = float(self.var_tz.get())
        except ValueError:
            v = 8.0
        return max(-12.0, min(14.0, v))

    def refresh_times(self):
        s = self.stats
        if s is None:
            return
        tz = self._tz_value()
        pseudo = self.var_mode.get().startswith("小米")
        sd, ed = s.start_dt, s.end_dt
        self.var_utc_start.set(fmt_utc_z(utc_of(sd, tz, pseudo)))
        self.var_utc_end.set(fmt_utc_z(utc_of(ed, tz, pseudo)))
        self.var_local_start.set(fmt_local(sd, tz, pseudo))
        self.var_local_end.set(fmt_local(ed, tz, pseudo))
        dur = ""
        if s.start_dt and s.end_dt:
            secs = (s.end_dt - s.start_dt).total_seconds()
            if secs < 0:
                secs = 0
            h, m = int(secs // 3600), int(secs % 3600 // 60)
            dur = "%d小时%02d分" % (h, m) if h else "%d分%02d秒" % (m,
                                                                   int(secs % 60))
        self.var_dur.set(dur or "—")
        try:
            self.var_tz.set(("%.1f" % tz))
        except Exception:
            pass

    # ---------- Key ----------
    def on_set_key(self):
        dlg = tk.Toplevel(self.root)
        dlg.title("设置高德 Key")
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.resizable(False, False)
        frm = ttk.Frame(dlg, padding=16)
        frm.pack(fill="both", expand=True)
        ttk.Label(frm, text="高德开放平台 Key（32 位）:",
                  font=(self.font_name, 12)).pack(anchor="w")
        var = tk.StringVar(value=self.cfg.get("amap_key") or "")
        ent = ttk.Entry(frm, textvariable=var, width=40)
        ent.pack(fill="x", pady=6)
        var_status = tk.StringVar(value=(
            "保存前会先在线校验。地图瓦片不依赖 Key；"
            "Key 用于起点/终点中文地址。") if not self.cfg.get("amap_key")
            else "当前已保存 Key：%s…%s" % (self.cfg["amap_key"][:4],
                                           self.cfg["amap_key"][-4:]))
        ttk.Label(frm, textvariable=var_status, style="Val.TLabel",
                  justify="left", wraplength=340).pack(fill="x")

        def do_save():
            key = var.get().strip()
            if not _KEY_RE.match(key):
                messagebox.showwarning("格式不对",
                                       "高德 Key 应为 32 位十六进制字符串。",
                                       parent=dlg)
                return
            btn.config(state="disabled")
            var_status.set("正在在线校验…")

            def work():
                ok, info = validate_amap_key(key)
                self.ui_queue.put(("keycheck", dlg, var, var_status, btn,
                                   key, ok, info))

            threading.Thread(target=work, daemon=True).start()

        btn = ttk.Button(frm, text="校验并保存", command=do_save)
        btn.pack(side="left", pady=(8, 0))
        ttk.Button(frm, text="取消", command=dlg.destroy).pack(
            side="left", padx=(8, 0), pady=(8, 0))
        ent.focus_set()
        dlg.wait_visibility()
        dlg.grab_set()

    def _on_key_checked(self, dlg, var, var_status, btn, key, ok, info):
        btn.config(state="normal")
        if ok:
            if save_amap_key(key):
                self.cfg = load_config()
                self.set_key_status()
                var_status.set("✅ 校验通过，已保存到 exif_viewer_config.json")
                self.set_status("高德 Key 已保存")
                dlg.after(900, dlg.destroy)
                if self.stats:
                    segs = self.stats.segments_gcj
                    if segs and segs[0]:
                        self._request_regeo((segs[0][0][1], segs[0][0][2]),
                                            (segs[-1][-1][1],
                                             segs[-1][-1][2]))
        else:
            if "PLAT_NOMATCH" in str(info):
                if messagebox.askyesno(
                        "Key 平台不匹配",
                        "该 Key 是「Web端(JS API)」类型，逆地理编码会报 "
                        "USERKEY_PLAT_NOMATCH。\n内嵌地图不依赖 Key，"
                        "仍可正常显示轨迹。\n\n仍要保存这个 Key 吗？",
                        parent=dlg):
                    if save_amap_key(key):
                        self.cfg = load_config()
                        self.set_key_status()
                        var_status.set("已保存（注意：该 Key 不能用于逆地理）")
                        dlg.after(900, dlg.destroy)
                else:
                    var_status.set("未保存。")
            else:
                var_status.set("❌ 校验失败：%s\n未保存。" % info)

    # ---------- 逆地理 ----------
    def _request_regeo(self, start, end):
        key = self.cfg.get("amap_key")
        if not key:
            return

        def work():
            res = {}
            for tag, (lat, lon) in (("start", start), ("end", end)):
                try:
                    url = ("https://restapi.amap.com/v3/geocode/regeo?"
                           + urllib.parse.urlencode(
                               {"key": key, "location": "%.6f,%.6f"
                                % (lon, lat)}))
                    data = json.loads(http_get(url, timeout=10).decode("utf-8"))
                    if str(data.get("status")) == "1":
                        res[tag] = (data["regeocode"].get("formatted_address")
                                    or "（无地址）")
                    else:
                        res[tag] = "查询失败:%s" % data.get("info", "?")
                except Exception as e:
                    res[tag] = "查询失败:%s" % e
            self.ui_queue.put(("regeo", res))

        threading.Thread(target=work, daemon=True).start()

    def _on_regeo(self, res):
        self.var_start_addr.set(res.get("start", "—"))
        self.var_end_addr.set(res.get("end", "—"))

    # ---------- 图层 ----------
    def on_layer(self):
        self.map.set_layer(self.var_layer.get())

    def on_reload_tiles(self):
        """清掉磁盘缓存与失败记录后重新拉取（网络恢复/换环境时用）。"""
        self.map.reload_tiles(forget_cache=True)
        self.set_status("已清空瓦片缓存，正在重新加载地图…")

    # ---------- 浏览器打开 ----------
    def on_open_browser(self):
        has_track = bool(self.stats and self.stats.segments_gcj)
        has_photo = bool(self.geo_photos)
        if not has_track and not has_photo:
            messagebox.showinfo("提示", "请先加载轨迹文件，或选择带 GPS 的照片目录。")
            return
        if self._html_worker is not None and self._html_worker.is_alive():
            self.set_status("正在生成网页，请稍候…")
            return
        self.set_status("正在生成网页版…（正在提取照片缩图）")

        def work():
            try:
                html = self._build_html()
                fd, path = tempfile.mkstemp(prefix="photo_track_map_",
                                            suffix=".html")
                with os.fdopen(fd, "w", encoding="utf-8") as f:
                    f.write(html)
                self.ui_queue.put(("html", path, None))
            except Exception:
                self.ui_queue.put(("html", None, traceback.format_exc()))

        self._html_worker = threading.Thread(target=work, daemon=True)
        self._html_worker.start()

    def _on_html_ready(self, path, err):
        if err:
            self.set_status("生成网页失败")
            messagebox.showerror("错误", "生成网页失败：\n%s" % err)
            return
        try:
            webbrowser.open("file://" + path)
        except Exception as e:
            messagebox.showerror("打开失败", str(e))
            return
        n = len(self.geo_photos)
        self.set_status("已在浏览器打开（网页版自带瓦片地图，无需 Key；"
                        "含 %d 个照片标记）" % n)

    def _build_html_photos(self):
        """把带 GPS 的照片整理成网页端可用的 JSON 结构（含内嵌缩图）。"""
        key = self.cfg.get("amap_key")
        # 还没查过地址的照片，趁生成网页时并发补上（限量，避免刷爆配额）
        if key:
            todo = [i for i in self.geo_photos
                    if self.photos[i].get("gcj")
                    and "%.5f,%.5f" % self.photos[i]["gcj"]
                    not in self._addr_cache][:400]
            if todo:
                def fetch(i, _n):
                    g = self.photos[i]["gcj"]
                    addr, _e = regeo_point(key, g[0], g[1])
                    return ("%.5f,%.5f" % g), addr
                got = map_parallel(fetch, todo, workers=4)
                for ck, addr in got:
                    if ck and addr:
                        self._addr_cache[ck] = addr

        items = []
        for i in self.geo_photos:
            info = self.photos[i]
            gcj = info.get("gcj")
            if not gcj:
                continue
            items.append({
                "la": round(gcj[0], 6), "lo": round(gcj[1], 6),
                "wla": round(float(info["lat"]), 6),
                "wlo": round(float(info["lon"]), 6),
                "n": info.get("name") or "",
                "t": fmt_exif_dt(info.get("dt")),
                "a": self._addr_cache.get("%.5f,%.5f" % gcj, ""),
                "alt": info.get("alt"),
                "dir": info.get("dir_deg"),
                "cam": " ".join(x for x in (info.get("make"),
                                            info.get("model")) if x),
                "exp": info.get("exposure") or "",
                "p": info.get("path") or "",
                "_u": "",
            })
        if not items:
            return items
        # 缩图：并发抽取（走磁盘缓存），单张上限 ~200px，避免 HTML 过大
        def one(item, _i):
            try:
                raw, _src = thumb_cached(item["p"])
            except Exception:
                raw = b""
            try:
                return data_uri(html_thumb_bytes(item["p"], raw, 200))
            except Exception:
                return ""

        uris = map_parallel(one, items, workers=4)
        for item, u in zip(items, uris):
            item["_u"] = u or ""
        return items

    def _build_html(self):
        """网页版：自己拼高德瓦片，不加载 JS API，因此不依赖任何 Key。"""
        pts = []
        has_track = bool(self.stats and self.stats.segments_gcj)
        if has_track:
            for seg in self.stats.segments_gcj:
                for (t, lat, lon, ele, raw) in seg:
                    pts.append((lon, lat))
            step = max(1, len(pts) // 4000)       # 控制网页端渲染量
            pts = pts[::step]
        photos = self._build_html_photos()
        # 轨迹与照片都没有时不做无谓的页面
        if not pts and not photos:
            return ""

        name = os.path.basename(self.track_path or "") or "照片地图"
        html = _BROWSER_HTML
        safe = name.replace("&", "&amp;").replace("<", "&lt;")
        html = html.replace("__TITLE__", safe)
        html = html.replace("__NAME_HTML__", safe)
        if has_track:
            start = self.stats.segments_gcj[0][0]
            end = self.stats.segments_gcj[-1][-1]
            km = self.stats.distance_m / 1000.0
            html = html.replace("__KM__", "%.2f" % km)
            html = html.replace("__NPT__", "%d" % self.stats.n_valid)
            html = html.replace("__TRACK__", ",".join("[%.6f,%.6f]" % p
                                                      for p in pts))
            html = html.replace("__SPOS__",
                                "[%.6f,%.6f]" % (start[2], start[1]))
            html = html.replace("__EPOS__", "[%.6f,%.6f]" % (end[2], end[1]))
            html = html.replace("__TRACK_ROW__", "")
        else:
            html = html.replace("__KM__", "0")
            html = html.replace("__NPT__", "0")
            html = html.replace("__TRACK__", "")
            html = html.replace("__SPOS__", "null")
            html = html.replace("__EPOS__", "null")
            html = html.replace("__TRACK_ROW__", "display:none")
        html = html.replace("__NPH__", "%d" % len(photos))
        html = html.replace("__PHOTOS__",
                            json.dumps(photos, ensure_ascii=False,
                                       separators=(",", ":")))
        return html

    # ---------- 退出 ----------
    def on_exit(self):
        try:
            self.map._loader.stop()
        except Exception:
            pass
        self.root.destroy()


# ============================================================
# 网页版模板：自绘瓦片地图，不加载高德 JS API，因此不需要任何 Key
# （把 __XXX__ 占位符替换后即为完整页面）
# ============================================================
_BROWSER_HTML = """<!DOCTYPE html>
<html lang="zh-CN"><head><meta charset="utf-8">
<meta name="referrer" content="no-referrer">
<title>__TITLE__ - 轨迹照片地图</title>
<style>
 html,body{margin:0;padding:0;height:100%;overflow:hidden;background:#E8EAED;
  font:13px/1.6 -apple-system,BlinkMacSystemFont,'PingFang SC','Microsoft YaHei',sans-serif}
 #map{position:absolute;left:0;top:0;right:0;bottom:0;overflow:hidden;cursor:grab}
 #map.drag{cursor:grabbing}
 #map img.t{position:absolute;width:256px;height:256px;border:0;
  pointer-events:none;-webkit-user-drag:none;user-select:none}
 #ov{position:absolute;left:0;top:0;pointer-events:none}
 #bar{position:absolute;top:10px;right:10px;z-index:20;background:#fff;
  padding:9px 12px;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,.22)}
 #bar b{display:block;margin-bottom:5px;max-width:320px;overflow:hidden;
  text-overflow:ellipsis;white-space:nowrap}
 label{margin-right:10px;cursor:pointer;white-space:nowrap}
 button{margin-top:6px;padding:3px 10px;font:inherit;cursor:pointer}
 #tip{position:absolute;left:10px;bottom:10px;z-index:20;
  background:rgba(255,255,255,.94);padding:7px 11px;border-radius:8px;
  box-shadow:0 2px 10px rgba(0,0,0,.22);color:#333}
 #tip span{margin-right:14px}
 #err{position:absolute;left:50%;top:50%;transform:translate(-50%,-50%);z-index:30;
  background:#fff3f3;color:#b00020;padding:12px 16px;border-radius:8px;
  display:none;box-shadow:0 2px 12px rgba(0,0,0,.25);max-width:70%;text-align:center}
 #photo{position:absolute;right:10px;bottom:10px;z-index:25;background:#fff;
  padding:10px;border-radius:8px;box-shadow:0 2px 12px rgba(0,0,0,.3);
  display:none;width:252px}
 #photo img{display:block;width:232px;height:auto;border-radius:5px;
  background:#eee;min-height:40px}
 #photo .nm{font-weight:700;margin-top:6px;word-break:break-all}
 #photo .mt{color:#555;font-size:12px;margin-top:3px;word-break:break-all}
 #photo .cl{position:absolute;right:6px;top:4px;cursor:pointer;color:#888;
  font-size:17px;line-height:1;border:0;background:none;padding:2px 5px;
  margin:0}
</style></head><body>
<div id="map"></div><svg id="ov"></svg>
<div id="bar">
 <b>__NAME_HTML__</b>
 <label><input type="radio" name="ly" value="std" checked>标准图</label>
 <label><input type="radio" name="ly" value="sat">卫星图</label>
 <div style="margin-top:5px;color:#666">拖拽平移 · 滚轮缩放 · 双击适配<br>
  点橙色圆点查看照片</div>
 <button id="fit">适配全部</button>
 <button id="toggleP">隐藏照片标记</button>
</div>
<div id="tip">
 <span style="__TRACK_ROW__">距离 <b>__KM__</b> km</span>
 <span style="__TRACK_ROW__">轨迹点 <b>__NPT__</b></span>
 <span>照片 <b>__NPH__</b> 张</span>
 <span style="color:#2E9E44">● 起点</span>
 <span style="color:#D93025">● 终点</span>
 <span style="color:#FF8A00">● 照片</span></div>
<div id="photo"><button class="cl" onclick="hidePhoto()">&times;</button>
 <div id="phimg"></div><div class="nm" id="phname"></div>
 <div class="mt" id="phmeta"></div></div>
<div id="err"></div>
<script>
var TRACK=[__TRACK__],START=__SPOS__,END=__EPOS__,PHOTOS=__PHOTOS__;
var TS=256,MINZ=3,MAXZ=17,NS='http://www.w3.org/2000/svg';
var LAYERS={
 std:['https://webrd0[s].is.autonavi.com/appmaptile?lang=zh_cn&size=1&scale=1&style=8&x=[x]&y=[y]&z=[z]'],
 sat:['https://webst0[s].is.autonavi.com/appmaptile?style=6&x=[x]&y=[y]&z=[z]']
};
var mapEl=document.getElementById('map'),ov=document.getElementById('ov');
var Z=12,CLAT=39.909,CLON=116.397,W=0,H=0,layer='std',tiles={},fails=0;
var showP=true,selP=-1,pinG=null;
function proj(lat,lon,z){var n=TS*Math.pow(2,z);
 var s=Math.sin(lat*Math.PI/180);s=Math.max(-0.9999,Math.min(0.9999,s));
 return [(lon+180)/360*n,(0.5-Math.log((1+s)/(1-s))/(4*Math.PI))*n];}
function invProj(x,y,z){var n=TS*Math.pow(2,z);
 return [Math.atan(Math.sinh(Math.PI*(1-2*y/n)))*180/Math.PI,x/n*360-180];}
function origin(){var c=proj(CLAT,CLON,Z);return [c[0]-W/2,c[1]-H/2];}
function size(){W=mapEl.clientWidth;H=mapEl.clientHeight;
 ov.setAttribute('width',W);ov.setAttribute('height',H);}
function tileUrl(x,y,z){
 return LAYERS[layer][0].replace('[s]',1+(x%4)).replace('[x]',x)
  .replace('[y]',y).replace('[z]',z);}
function svg(tag,a){var e=document.createElementNS(NS,tag);
 for(var k in a)e.setAttribute(k,a[k]);ov.appendChild(e);return e;}
var pOut=svg('polyline',{fill:'none',stroke:'#FFFFFF','stroke-width':7,
 'stroke-linecap':'round','stroke-linejoin':'round'});
var pIn=svg('polyline',{fill:'none',stroke:'#1E6FFF','stroke-width':4,
 'stroke-linecap':'round','stroke-linejoin':'round'});
pinG=svg('g',{});
var cS=svg('circle',{r:7,fill:'#2E9E44',stroke:'#FFFFFF','stroke-width':2});
var cE=svg('circle',{r:7,fill:'#D93025',stroke:'#FFFFFF','stroke-width':2});
var tS=svg('text',{'font-size':13,'font-weight':700,fill:'#1A1A1A',stroke:'#FFFFFF',
 'stroke-width':3,'paint-order':'stroke'});tS.textContent='起点';
var tE=svg('text',{'font-size':13,'font-weight':700,fill:'#1A1A1A',stroke:'#FFFFFF',
 'stroke-width':3,'paint-order':'stroke'});tE.textContent='终点';
function renderTiles(){var o=origin(),n=Math.pow(2,Z);
 var tx0=Math.floor(o[0]/TS),ty0=Math.floor(o[1]/TS);
 var tx1=Math.floor((o[0]+W)/TS),ty1=Math.floor((o[1]+H)/TS),need={};
 for(var ty=ty0;ty<=ty1;ty++){if(ty<0||ty>=n)continue;
  for(var tx=tx0;tx<=tx1;tx++){var k=Z+'_'+tx+'_'+ty;need[k]=1;
   var im=tiles[k];
   if(!im){im=document.createElement('img');im.className='t';
    im.onerror=function(){fails++;checkErr();};
    im.src=tileUrl(tx,ty,Z);tiles[k]=im;mapEl.appendChild(im);}
   im.style.left=(tx*TS-o[0])+'px';im.style.top=(ty*TS-o[1])+'px';}}
 for(var k2 in tiles){if(!need[k2]){var e=tiles[k2];
  if(e.parentNode)e.parentNode.removeChild(e);delete tiles[k2];}}}
function checkErr(){var good=false;
 for(var k in tiles){var e=tiles[k];if(e.complete&&e.naturalWidth>0){good=true;break;}}
 if(!good&&fails>3){var el=document.getElementById('err');el.style.display='block';
  el.innerHTML='地图瓦片加载失败<br>请检查网络或代理设置后刷新页面';}}
function renderTrack(){var o=origin(),a=[];
 if(TRACK.length){for(var i=0;i<TRACK.length;i++){
  var p=proj(TRACK[i][1],TRACK[i][0],Z);
  a.push((p[0]-o[0]).toFixed(1)+','+(p[1]-o[1]).toFixed(1));}
  var s=a.join(' ');pOut.setAttribute('points',s);pIn.setAttribute('points',s);}
 place(cS,tS,START,o);place(cE,tE,END,o);}
function place(c,t,pos,o){if(!pos){c.setAttribute('r',0);t.textContent='';return;}
 var p=proj(pos[1],pos[0],Z),x=p[0]-o[0],y=p[1]-o[1];
 c.setAttribute('r',7);c.setAttribute('cx',x);c.setAttribute('cy',y);
 t.setAttribute('x',x+13);t.setAttribute('y',y+5);}
function renderPhotos(){while(pinG.firstChild)pinG.removeChild(pinG.firstChild);
 if(!showP)return;var o=origin();
 for(var i=0;i<PHOTOS.length;i++){var p=PHOTOS[i];
  var q=proj(p.la,p.lo,Z),x=q[0]-o[0],y=q[1]-o[1];
  if(x<-24||y<-24||x>W+24||y>H+24)continue;
  var c=document.createElementNS(NS,'circle'),big=(i===selP);
  c.setAttribute('cx',x.toFixed(1));c.setAttribute('cy',y.toFixed(1));
  c.setAttribute('r',big?9:5.5);
  c.setAttribute('fill',big?'#E4572E':'#FF8A00');
  c.setAttribute('stroke','#fff');c.setAttribute('stroke-width',big?2.5:1.5);
  c.style.pointerEvents='auto';c.style.cursor='pointer';
  c.addEventListener('click',(function(k){return function(ev){
   ev.stopPropagation();showPhoto(k);};})(i));
  pinG.appendChild(c);}}
function esc(s){return String(s==null?'':s).replace(/[&<>"]/g,function(c){
 return {'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c];});}
function showPhoto(i){var p=PHOTOS[i];if(!p)return;
 selP=i;renderPhotos();
 document.getElementById('phimg').innerHTML=p._u
  ?'<img src="'+p._u+'" alt="">'
  :'<div style="color:#999;padding:24px 0;text-align:center">（无缩图）</div>';
 document.getElementById('phname').textContent=p.n||'';
 var m=[];
 if(p.t)m.push('拍摄：'+p.t);
 if(p.cam)m.push(p.cam);
 if(p.exp)m.push(p.exp);
 if(p.alt!==null&&p.alt!==undefined)m.push('海拔 '+Number(p.alt).toFixed(1)+' m');
 if(p.a)m.push('地址：'+p.a);
 m.push('WGS-84 '+Number(p.wla).toFixed(6)+', '+Number(p.wlo).toFixed(6));
 m.push('高德 GCJ-02 '+Number(p.la).toFixed(6)+', '+Number(p.lo).toFixed(6));
 document.getElementById('phmeta').innerHTML=m.map(esc).join('<br>');
 document.getElementById('photo').style.display='block';}
function hidePhoto(){selP=-1;
 document.getElementById('photo').style.display='none';renderPhotos();}
function draw(){size();renderTiles();renderTrack();renderPhotos();}
function fit(){size();var la=[],lo=[],i;
 for(i=0;i<TRACK.length;i++){lo.push(TRACK[i][0]);la.push(TRACK[i][1]);}
 for(i=0;i<PHOTOS.length;i++){lo.push(PHOTOS[i].lo);la.push(PHOTOS[i].la);}
 if(!la.length){draw();return;}
 var mla=Math.max.apply(null,la),nla=Math.min.apply(null,la);
 var mlo=Math.max.apply(null,lo),nlo=Math.min.apply(null,lo),best=MINZ;
 for(var z=MAXZ;z>=MINZ;z--){var a=proj(mla,nlo,z),b=proj(nla,mlo,z);
  if(Math.abs(b[0]-a[0])<=W-100&&Math.abs(b[1]-a[1])<=H-100){best=z;break;}}
 Z=best;CLAT=(mla+nla)/2;CLON=(mlo+nlo)/2;draw();}
var drag=false,lx=0,ly=0;
mapEl.addEventListener('mousedown',function(e){drag=true;lx=e.clientX;ly=e.clientY;
 mapEl.classList.add('drag');e.preventDefault();});
window.addEventListener('mousemove',function(e){if(!drag)return;
 var dx=e.clientX-lx,dy=e.clientY-ly;lx=e.clientX;ly=e.clientY;
 var o=origin(),c=invProj(o[0]+W/2-dx,o[1]+H/2-dy,Z);
 CLAT=c[0];CLON=c[1];draw();});
window.addEventListener('mouseup',function(){drag=false;
 mapEl.classList.remove('drag');});
mapEl.addEventListener('wheel',function(e){e.preventDefault();
 var nz=Math.max(MINZ,Math.min(MAXZ,Z+(e.deltaY<0?1:-1)));
 if(nz===Z)return;var o=origin(),g=invProj(o[0]+e.clientX,o[1]+e.clientY,Z);
 Z=nz;var p=proj(g[0],g[1],Z);
 var c=invProj(p[0]-(W/2-e.clientX),p[1]-(H/2-e.clientY),Z);
 CLAT=c[0];CLON=c[1];draw();},{passive:false});
mapEl.addEventListener('dblclick',function(e){e.preventDefault();fit();});
document.getElementById('fit').onclick=fit;
document.getElementById('toggleP').onclick=function(){showP=!showP;
 this.textContent=showP?'隐藏照片标记':'显示照片标记';renderPhotos();};
var rs=document.getElementsByName('ly');
for(var ri=0;ri<rs.length;ri++){rs[ri].onchange=function(){if(!this.checked)return;
 layer=this.value;for(var k in tiles){var e=tiles[k];
  if(e.parentNode)e.parentNode.removeChild(e);}tiles={};fails=0;renderTiles();};}
window.addEventListener('resize',draw);
fit();
</script></body></html>"""


# ============================================================
# 高德 Key 在线校验（regeo 测试点）
# ============================================================
def validate_amap_key(key):
    """返回 (是否可用, 说明)。"""
    try:
        url = ("https://restapi.amap.com/v3/geocode/regeo?"
               + urllib.parse.urlencode(
                   {"key": key, "location": "116.397428,39.909230"}))
        data = json.loads(http_get(url, timeout=10).decode("utf-8"))
    except Exception as e:
        return False, "网络错误：%s" % e
    if str(data.get("status")) == "1":
        return True, "ok"
    info = str(data.get("info", ""))
    return False, info or "未知错误"


def main():
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
