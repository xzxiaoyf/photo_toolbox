#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
照片EXIF信息查看器 v2（修复版）
- 深色背景高对比度文本框（保留）
- GPS信息合并至EXIF显示区（保留）
- WGS-84 → GCJ-02 坐标转换（地图+逆地理编码）（保留）
- 地图先显示标记点，点击后显示照片（保留）
- 一键显示目录下所有照片坐标点（保留，修复视野自适应）
- GUI配置高德Key并持久化保存（保留，明文；改为三个字段）
- exiftool提取缩略图（保留，增加 sips 兜底）

相对原版的关键修复（每一条都实机复现过）
----------------------------------------
[P0-1] 去掉 requests 依赖，逆地理编码改用标准库 urllib。
       原版 import requests 在直接运行 .py 时即崩（实测 4 个 Python 全无 requests）。
       附加实测：python.org 装的 3.11/3.12 urllib 会证书校验失败
       （CERTIFICATE_VERIFY_FAILED，未运行 Install Certificates.command），
       已做降级兜底：先标准校验，失败再用不校验证书的方式重试（只读 GET，可接受）。
[P0-2] Key 配置改为三个字段（各自独立，明文保存不变）：
       ① Web端(JS API) Key —— 地图显示用
       ② JS API 安全密钥 securityJsCode —— 2021-12-02 之后申请的 JS API Key
          必须配合它，且必须在加载 API 脚本之前设置 window._AMapSecurityConfig
          （官方文档确认；原版没设 → 新 key 地图打不开）
       ③ Web服务 Key —— 逆地理编码（restapi）用。
       原版只让填一个 key：key 分平台，一个 key 不可能同时供 JS API 和
       REST 用，必有一边报 USERKEY_PLAT_NOMATCH。
       旧的 amap_key 字段自动迁移为 JS API Key。
[P0-3] 「显示全部照片位置」视野自适应修复。
       实测（浏览器加载真实高德 JS API 2.0）：new AMap.Bounds() 无参构造
       不报错但结果是全世界 [-180,-90,180,90]，且 extend() 后不收敛，
       原版 setBounds 等于把视野设成全世界 —— 静默失效。
       改为加完全部标记后 map.setFitView()。
[P1-4] 配置文件路径锚定到程序所在目录（pyinstaller 打包/双击启动时
       工作目录不固定，原版相对路径会"key 存了又丢"）。
       发现同目录存在旧配置时自动迁移。
[P1-5] 「显示全部照片位置」改后台线程扫描：不再冻结界面，实时进度，
       扫描中可点同一按钮取消。
[P1-6] 读取单张照片 EXIF（含逆地理编码网络请求）也放后台线程，
       点选照片不再卡界面（原版逆地理最多同步等 6 秒）。
[P2-7] 缩略图提取链扩展：exiftool ThumbnailImage → JpgFromRaw → PreviewImage
       → Pillow（装了才用）→ macOS sips 缩放兜底（实测能处理 HEIC）。
       原版对 JPEG/CR2 的提取逻辑一字未动。
[P2-8] 跨平台字体：Mac 用 PingFang SC / Menlo，Windows 用微软雅黑 / Consolas。
[P2-9] 照片名注入 HTML/JS 改用 json.dumps 转义，文件名带引号/反斜杠不再出坏页面。

依赖
----
- 纯 Python 标准库（requests / Pillow 都不再需要；Pillow 装了会优先用于缩略图）
- 外部命令 exiftool（缩略图与 EXIF 读取）

运行
----
    python3 photo_exif_viewer_v2.py
#  pyinstaller -F photo_exif_viewer_v2.py
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import subprocess
import json
import os
import sys
import math
import webbrowser
import re
import base64
import io
import tempfile
import threading
import queue as queue_mod
import urllib.request
import urllib.error
import urllib.parse

APP_TITLE = "📷 照片 EXIF 信息查看器"
APP_VERSION = "v2.0"

PHOTO_EXTENSIONS = {
    '.jpg', '.jpeg', '.png', '.tiff', '.tif', '.bmp',
    '.gif', '.heic', '.heif','.hif', '.raw', '.cr2', '.cr3',
    '.nef', '.arw', '.dng', '.orf', '.rw2', '.sr2'
}

# ============================================================
# 配置：锚定到程序所在目录（打包/双击启动时 CWD 不可靠），明文保存
# ============================================================
def _config_path():
    if getattr(sys, "frozen", False):          # pyinstaller
        base = os.path.dirname(os.path.abspath(sys.executable))
    else:
        base = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base, "exif_viewer_config2.json")


CONFIG_PATH = _config_path()
#: 兼容旧版写在任意工作目录的配置，找到了就迁移过来
_LEGACY_CANDIDATES = [
    os.path.join(os.getcwd(), "exif_viewer_config2.json"),
]


def load_config():
    """返回 {js_key, js_code, rest_key}。兼容旧版 amap_key 字段。"""
    cfg = {"js_key": "", "js_code": "", "rest_key": ""}
    for path in [CONFIG_PATH] + _LEGACY_CANDIDATES:
        if not os.path.exists(path):
            continue
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            continue
        cfg["js_key"] = (data.get("js_key") or data.get("amap_key") or "").strip()
        cfg["js_code"] = (data.get("js_code") or "").strip()
        cfg["rest_key"] = (data.get("rest_key") or "").strip()
        if path != CONFIG_PATH and cfg != {"js_key": "", "js_code": "", "rest_key": ""}:
            try:                       # 旧配置迁移到程序目录
                save_config(cfg)
            except Exception:
                pass
        break
    return cfg


def save_config(cfg):
    with open(CONFIG_PATH, "w", encoding="utf-8") as f:
        json.dump(cfg, f, indent=2, ensure_ascii=False)


KEYS = load_config()

# ============================================================
# 跨平台字体
# ============================================================
def pick_font():
    if sys.platform == "darwin":
        return "PingFang SC", "Menlo"
    if sys.platform.startswith("win"):
        return "Microsoft YaHei UI", "Consolas"
    return "WenQuanYi Micro Hei", "DejaVu Sans Mono"


UI_FONT, MONO_FONT = pick_font()


# ============================================================
# WGS-84 → GCJ-02 坐标转换（与原版一致）
# ============================================================
_A = 6378245.0
_EE = 0.00669342162296594323


def _out_of_china(lat, lng):
    return not (72.004 <= lng <= 137.8347 and 0.8293 <= lat <= 55.8271)


def _transform_lat(x, y):
    ret = (-100.0 + 2.0 * x + 3.0 * y + 0.2 * y * y +
           0.1 * x * y + 0.2 * math.sqrt(abs(x)))
    ret += (20.0 * math.sin(6.0 * x * math.pi) +
            20.0 * math.sin(2.0 * x * math.pi)) * 2.0 / 3.0
    ret += (20.0 * math.sin(y * math.pi) +
            40.0 * math.sin(y / 3.0 * math.pi)) * 2.0 / 3.0
    ret += (160.0 * math.sin(y / 12.0 * math.pi) +
            320.0 * math.sin(y * math.pi / 30.0)) * 2.0 / 3.0
    return ret


def _transform_lng(x, y):
    ret = (300.0 + x + 2.0 * y + 0.1 * x * x +
           0.1 * x * y + 0.1 * math.sqrt(abs(x)))
    ret += (20.0 * math.sin(6.0 * x * math.pi) +
            20.0 * math.sin(2.0 * x * math.pi)) * 2.0 / 3.0
    ret += (20.0 * math.sin(x * math.pi) +
            40.0 * math.sin(x / 3.0 * math.pi)) * 2.0 / 3.0
    ret += (150.0 * math.sin(x / 12.0 * math.pi) +
            300.0 * math.sin(x / 30.0 * math.pi)) * 2.0 / 3.0
    return ret


def wgs84_to_gcj02(wgs_lat, wgs_lng):
    if _out_of_china(wgs_lat, wgs_lng):
        return wgs_lat, wgs_lng
    d_lat = _transform_lat(wgs_lng - 105.0, wgs_lat - 35.0)
    d_lng = _transform_lng(wgs_lng - 105.0, wgs_lat - 35.0)
    rad_lat = wgs_lat / 180.0 * math.pi
    magic = math.sin(rad_lat)
    magic = 1 - _EE * magic * magic
    sqrt_magic = math.sqrt(magic)
    d_lat = (d_lat * 180.0) / ((_A * (1 - _EE)) / (magic * sqrt_magic) * math.pi)
    d_lng = (d_lng * 180.0) / (_A / sqrt_magic * math.cos(rad_lat) * math.pi)
    return wgs_lat + d_lat, wgs_lng + d_lng


# ============================================================
# 逆地理编码：标准库 urllib（带证书降级）
# ============================================================
def _ssl_cert_error_type():
    try:
        return __import__("ssl").SSLCertVerificationError
    except Exception:
        return ()


def _ssl_unverified_ctx():
    import ssl
    ctx = ssl.create_default_context()
    ctx.check_hostname = False
    ctx.verify_mode = ssl.CERT_NONE
    return ctx


def _urlopen_json(url, timeout=6):
    """HTTPS GET → dict。先标准证书校验；失败原因是证书问题
    （python.org 版 Python 未运行 Install Certificates.command 时常发生）
    再用不校验方式重试。只读 GET，可接受。其他网络错误照常抛出。"""
    try:
        with urllib.request.urlopen(url, timeout=timeout) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.URLError as e:
        reason = getattr(e, "reason", None)
        if isinstance(reason, _ssl_cert_error_type()) or \
                "CERTIFICATE" in str(reason).upper():
            pass                                        # 证书问题 → 降级重试
        else:
            raise
    with urllib.request.urlopen(url, timeout=timeout,
                                context=_ssl_unverified_ctx()) as resp:
        return json.loads(resp.read().decode("utf-8"))


def reverse_geocode(rest_key, gcj_lat, gcj_lon, timeout=6):
    """返回地址字符串；失败时返回以「解析失败」开头的说明，不抛异常。"""
    if not rest_key:
        return "（未配置 Web服务 Key，无法解析地址）"
    qs = urllib.parse.urlencode({
        "key": rest_key,
        "location": "%.6f,%.6f" % (gcj_lon, gcj_lat),
        "extensions": "base",
    })
    try:
        data = _urlopen_json("https://restapi.amap.com/v3/geocode/regeo?" + qs,
                             timeout=timeout)
        if data.get("status") == "1":
            return data["regeocode"]["formatted_address"]
        return "解析失败（%s）" % data.get("info", "")
    except Exception as e:
        return "解析失败：%s" % e


# ============================================================
# 坐标解析（与原版一致，实测无问题）
# ============================================================
def gps_range_ok(lat, lon):
    """合法 GPS 范围校验：纬度 ±90、经度 ±180。
    实测大疆部分机型/遥控器会写入越界值（如 lat=1962, lon=6712），
    这种坐标不能送高德逆地理/地图，否则报错。"""
    if lat is None or lon is None:
        return False
    return -90.0 <= lat <= 90.0 and -180.0 <= lon <= 180.0


def parse_coord(value, ref=None):
    if value is None:
        return None
    if isinstance(value, (int, float)):
        coord = float(value)
        if ref and coord > 0:
            if str(ref).strip().upper() in ("S", "W"):
                coord = -coord
        return coord
    s = str(value).strip()
    if not s:
        return None
    try:
        coord = float(s)
        if ref and coord > 0:
            if str(ref).strip().upper() in ("S", "W"):
                coord = -coord
        return coord
    except ValueError:
        pass
    m = re.match(
        r"([\d.]+)\s*(?:deg|°)\s*([\d.]+)\s*['′]\s*([\d.]+)\s*[\"″]?\s*([NSEW])?",
        s, re.IGNORECASE)
    if m:
        d, mi, sec = float(m.group(1)), float(m.group(2)), float(m.group(3))
        coord = d + mi / 60 + sec / 3600
        direction = (m.group(4) or "").upper()
        if not direction and ref:
            direction = str(ref).strip().upper()
        if direction in ("S", "W"):
            coord = -coord
        return coord
    m2 = re.match(r"([\d.]+)\s*([NSEW])", s, re.IGNORECASE)
    if m2:
        coord = float(m2.group(1))
        if m2.group(2).upper() in ("S", "W"):
            coord = -coord
        return coord
    return None


# ============================================================
# 缩略图提取：exiftool 三标签 → Pillow（可选）→ sips（macOS）
# ============================================================
_THUMB_TAGS = ("ThumbnailImage", "JpgFromRaw", "PreviewImage")


def _exiftool_thumb(path):
    for tag in _THUMB_TAGS:
        try:
            proc = subprocess.run(["exiftool", "-b", "-" + tag, path],
                                  capture_output=True, timeout=8)
            if proc.returncode == 0 and len(proc.stdout) > 100:
                return base64.b64encode(proc.stdout).decode()
        except Exception:
            continue
    return None


def _pillow_thumb(path, max_px=200):
    try:
        from PIL import Image, ImageOps          # 装了才用
    except ImportError:
        return None
    try:
        try:
            from pillow_heif import register_heif_opener
            register_heif_opener()
        except ImportError:
            pass
        img = Image.open(path)
        img = ImageOps.exif_transpose(img)
        img.thumbnail((max_px, max_px))
        if img.mode in ("RGBA", "P"):
            img = img.convert("RGB")
        buf = io.BytesIO()
        img.save(buf, format="JPEG", quality=60)
        return base64.b64encode(buf.getvalue()).decode()
    except Exception:
        return None


def _sips_thumb(path, max_px=400):
    """macOS 兜底：sips 缩放转 JPEG（实测能处理 HEIC / 无嵌入缩略图的图）。"""
    if sys.platform != "darwin":
        return None
    fd, tmp = tempfile.mkstemp(suffix=".jpg")
    os.close(fd)
    try:
        proc = subprocess.run(
            ["sips", "-s", "format", "jpeg", "-Z", str(max_px),
             path, "--out", tmp],
            capture_output=True, timeout=20)
        if proc.returncode == 0 and os.path.exists(tmp) \
                and os.path.getsize(tmp) > 100:
            with open(tmp, "rb") as f:
                return base64.b64encode(f.read()).decode()
    except Exception:
        pass
    finally:
        try:
            os.remove(tmp)
        except OSError:
            pass
    return None


def img_to_base64(path):
    b64 = _exiftool_thumb(path)
    if b64:
        return b64
    b64 = _pillow_thumb(path)
    if b64:
        return b64
    return _sips_thumb(path)


# ============================================================
# exiftool 读取 EXIF（返回展示行 + GPS）
# ============================================================
def read_exif_lines(filepath):
    """返回 (lines, gps_lat, gps_lon)。抛 FileNotFoundError 表示缺 exiftool。"""
    cmd = ["exiftool", "-json", "-n", "-c", "%.6f",
           "-Make", "-Model", "-LensModel", "-LensInfo", "-Lens",
           "-Software",
           "-DateTimeOriginal", "-CreateDate",
           "-GPSLatitude", "-GPSLongitude",
           "-GPSLatitudeRef", "-GPSLongitudeRef",
           "-GPSAltitude",
           filepath]
    proc = subprocess.run(cmd, capture_output=True, text=True,
                          encoding="utf-8", timeout=15)
    if proc.returncode != 0:
        raise RuntimeError("exiftool 错误：%s" % proc.stderr.strip())

    data = json.loads(proc.stdout)
    if not data:
        raise RuntimeError("未获取到 EXIF 数据")

    info = data[0]
    make = (info.get("Make") or "未知").strip()
    model = (info.get("Model") or "未知").strip()
    software = (info.get("Software") or "未知").strip()
    lens = info.get("LensModel") or info.get("LensInfo") or info.get("Lens") or "未知"
    if isinstance(lens, (list, tuple)):          # LensInfo 可能是数组
        lens = " ".join(str(x) for x in lens)
    date = (info.get("DateTimeOriginal")
            or info.get("CreateDate") or "未知")

    lines = [
        f"相机品牌：{make}", f"相机型号：{model}", f"固件版本：{software}",
        f"镜头型号：{lens}", f"拍摄日期：{date}",
    ]

    lat = parse_coord(info.get("GPSLatitude"), info.get("GPSLatitudeRef"))
    lon = parse_coord(info.get("GPSLongitude"), info.get("GPSLongitudeRef"))

    # 坐标越界（如大疆遥控器错误写入的 lat=1962, lon=6712）：
    # 展示原始值供参考，但不做坐标转换、地址解析，也不允许打开地图
    if lat is not None and lon is not None and not gps_range_ok(lat, lon):
        lines.extend(["", "━━━ GPS 信息 ━━━",
                      f"⚠ GPS 数据非法：{lat:.6f}, {lon:.6f}",
                      "纬度合法范围 ±90、经度合法范围 ±180，",
                      "该坐标超出范围（疑似设备/遥控器错误写入）。",
                      "已跳过地址解析与地图定位。"])
        return lines, None

    if lat is not None and lon is not None:
        alt = info.get("GPSAltitude")
        lines.extend(["", "━━━ GPS 信息 ━━━",
                      f"原始坐标(WGS-84)：{lat:.6f}, {lon:.6f}"])
        if alt is not None:
            lines.append(f"海拔：{alt} m")
        gcj_lat, gcj_lon = wgs84_to_gcj02(lat, lon)
        lines.append(f"高德坐标(GCJ-02)：{gcj_lat:.6f}, {gcj_lon:.6f}")
        lines.append("地  址：" + reverse_geocode(KEYS["rest_key"], gcj_lat, gcj_lon))
        return lines, (lat, lon)

    lines.extend(["", "━━━ GPS 信息 ━━━", "该照片无 GPS 信息"])
    return lines, None


def quick_extract_gps(filepath):
    """扫描用：只取 GPS 和拍摄时间。"""
    try:
        cmd = ["exiftool", "-json", "-n", "-c", "%.6f",
               "-GPSLatitude", "-GPSLongitude",
               "-GPSLatitudeRef", "-GPSLongitudeRef",
               "-DateTimeOriginal",
               filepath]
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              encoding="utf-8", timeout=10)
        if proc.returncode != 0:
            return None, None, None
        data = json.loads(proc.stdout)
        if not data:
            return None, None, None
        info = data[0]
        lat = parse_coord(info.get("GPSLatitude"), info.get("GPSLatitudeRef"))
        lon = parse_coord(info.get("GPSLongitude"), info.get("GPSLongitudeRef"))
        if not gps_range_ok(lat, lon):      # 越界坐标（如大疆错误写入）不进地图
            return None, None, info.get("DateTimeOriginal") or ""
        return lat, lon, info.get("DateTimeOriginal") or ""
    except Exception:
        return None, None, None


# ============================================================
# 地图 HTML 生成
# ============================================================
def _js_name(name):
    """照片名安全注入 JS/HTML（json.dumps 处理引号/反斜杠/Unicode）。"""
    return json.dumps(name, ensure_ascii=False)


def _security_config_html():
    """安全密钥必须在 amap 脚本加载之前设置（官方要求）。"""
    if not KEYS["js_code"]:
        return ""
    return ("<script>window._AMapSecurityConfig = {securityJsCode: %s};</script>"
            % _js_name(KEYS["js_code"]))


_GEO_JS = """var PI=Math.PI,A=6378245.0,EE=0.00669342162296594;
function outOfChina(a,b){{return(b<72.004||b>137.8347||a<0.8293||a>55.8271)}}
function tLat(x,y){{var r=-100+2*x+3*y+.2*y*y+.1*x*y+.2*Math.sqrt(Math.abs(x));
r+=(20*Math.sin(6*x*PI)+20*Math.sin(2*x*PI))*2/3;r+=(20*Math.sin(y*PI)+40*Math.sin(y/3*PI))*2/3;
r+=(160*Math.sin(y/12*PI)+320*Math.sin(y*PI/30))*2/3;return r}}
function tLng(x,y){{var r=300+x+2*y+.1*x*x+.1*x*y+.1*Math.sqrt(Math.abs(x));
r+=(20*Math.sin(6*x*PI)+20*Math.sin(2*x*PI))*2/3;r+=(20*Math.sin(x*PI)+40*Math.sin(x/3*PI))*2/3;
r+=(150*Math.sin(x/12*PI)+300*Math.sin(x/30*PI))*2/3;return r}}
function w2g(a,b){{if(outOfChina(a,b))return[a,b];var d=tLat(b-105,a-35),e=tLng(b-105,a-35),
r=a/180*PI,m=Math.sin(r);m=1-EE*m*m;var s=Math.sqrt(m);
d=d*180/((A*(1-EE))/(m*s)*PI);e=e*180/(A/s*Math.cos(r)*PI);return[a+d,b+e]}}"""


def build_single_map_html(lat, lon, name, img_b64):
    safe = _js_name(name)
    if img_b64:
        img_html = (
            '<img src="data:image/jpeg;base64,{0}" '
            'style="max-width:260px;max-height:200px;'
            'border-radius:6px;box-shadow:0 2px 8px rgba(0,0,0,.25);'
            'margin-top:6px;">'.format(img_b64))
    else:
        img_html = '<p style="color:#999;font-size:12px;">（无缩略图）</p>'

    return """<!DOCTYPE html>
<html lang="zh-CN"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>📷 {title}</title>
<style>*{{margin:0;padding:0;box-sizing:border-box}}
#map{{width:100%;height:100vh}}
.bar{{position:absolute;top:12px;left:50%;transform:translateX(-50%);z-index:99;
background:rgba(255,255,255,.95);padding:8px 24px;border-radius:24px;
box-shadow:0 2px 12px rgba(0,0,0,.15);font:14px/1.6 '{font}',sans-serif}}
.hint{{position:absolute;bottom:20px;left:50%;transform:translateX(-50%);z-index:99;
background:rgba(0,0,0,.6);color:#fff;padding:6px 18px;border-radius:16px;
font:13px/1.4 '{font}',sans-serif;pointer-events:none;transition:opacity .5s}}
</style></head><body>
<div class="bar">📷 {title} 的拍摄位置</div>
<div class="hint" id="hint">💡 点击标记点查看照片</div>
<div id="map"></div>
{sec}<script src="https://webapi.amap.com/maps?v=2.0&key={key}"></script>
<script>
{geo}
var g=w2g({lat},{lon});
var map=new AMap.Map('map',{{zoom:16,center:[g[1],g[0]],resizeEnable:true}});
var mc=document.createElement('div');
mc.innerHTML='<div style="width:28px;height:28px;border-radius:50%;background:#e74c3c;border:3px solid #fff;box-shadow:0 2px 8px rgba(0,0,0,.4);cursor:pointer;position:relative"><div style="position:absolute;top:50%;left:50%;transform:translate(-50%,-50%);width:10px;height:10px;border-radius:50%;background:#fff"></div></div><div style="width:0;height:0;margin:-2px auto 0;border-left:8px solid transparent;border-right:8px solid transparent;border-top:10px solid #e74c3c"></div>';
var mk=new AMap.Marker({{position:[g[1],g[0]],content:mc,offset:new AMap.Pixel(-14,-38),title:{title}}});
map.add(mk);
var iw=new AMap.InfoWindow({{content:'<div style="text-align:center;padding:8px;font-family:{font},sans-serif;min-width:200px"><h3 style="font-size:14px;margin:0 0 6px;color:#333">📷 {title}</h3>{img_html}<p style="font-size:12px;color:#888;margin:6px 0 0">WGS-84: {lat:.6f}, {lon:.6f}<br>GCJ-02: '+g[0].toFixed(6)+', '+g[1].toFixed(6)+'</p></div>',offset:new AMap.Pixel(0,-42),closeWhenClickMap:true}});
mk.on('click',function(){{iw.open(map,mk.getPosition());document.getElementById('hint').style.opacity='0'}});
setTimeout(function(){{var h=document.getElementById('hint');if(h&&h.style.opacity!=='0')h.style.opacity='0'}},5000);
</script></body></html>""".format(
        title=safe, font=UI_FONT, sec=_security_config_html(),
        key=KEYS["js_key"], geo=_GEO_JS, lat=lat, lon=lon, img_html=img_html)


def build_all_markers_map_html(markers):
    count = len(markers)
    # 用 json.dumps 整体序列化，文件名带引号/反斜杠/中文都安全
    items = [{
        "n": m["name"], "wla": m["wgs_lat"], "wlo": m["wgs_lon"],
        "gla": m["gcj_lat"], "glo": m["gcj_lon"],
        "d": m["date"] or "", "img": m["img"] or "",
    } for m in markers]
    js_array = json.dumps(items, ensure_ascii=False, indent=1)

    return """<!DOCTYPE html>
<html lang="zh-CN"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>📷 全部照片位置 ({count}张)</title>
<style>
*{{margin:0;padding:0;box-sizing:border-box}}
#map{{width:100%;height:100vh}}
.bar{{position:absolute;top:12px;left:50%;transform:translateX(-50%);z-index:99;
background:rgba(255,255,255,.95);padding:8px 24px;border-radius:24px;
box-shadow:0 2px 12px rgba(0,0,0,.15);font:14px/1.6 '{font}',sans-serif;white-space:nowrap}}
.hint{{position:absolute;bottom:20px;left:50%;transform:translateX(-50%);z-index:99;
background:rgba(0,0,0,.6);color:#fff;padding:6px 18px;border-radius:16px;
font:13px/1.4 '{font}',sans-serif;pointer-events:none;transition:opacity .5s}}
.iw{{text-align:center;padding:10px;font-family:'{font}',sans-serif;min-width:220px;max-width:300px}}
.iw h3{{font-size:13px;margin:0 0 6px;color:#333;word-break:break-all}}
.iw img{{max-width:240px;max-height:180px;border-radius:6px;box-shadow:0 2px 8px rgba(0,0,0,.2);margin-top:4px}}
.iw p{{font-size:11px;color:#888;margin:6px 0 0;line-height:1.5}}
.iw .no-img{{color:#bbb;font-size:12px;padding:20px 0}}
</style></head><body>
<div class="bar">📷 共 {count} 张照片拍摄位置</div>
<div class="hint" id="hint">💡 点击标记点查看照片详情 | 滚轮缩放 | 拖拽移动</div>
<div id="map"></div>

{sec}<script src="https://webapi.amap.com/maps?v=2.0&key={key}"></script>
<script>
{geo}

var photos = {js_array};

var map = new AMap.Map('map', {{
    zoom: 12,
    resizeEnable: true,
    mapStyle: 'amap://styles/light'
}});

var currentIW = null;
var markers = [];

photos.forEach(function(p, idx) {{
    var mc = document.createElement('div');
    mc.innerHTML =
        '<div style="' +
        'width:22px;height:22px;border-radius:50%;' +
        'background:#e74c3c;border:2px solid #fff;' +
        'box-shadow:0 1px 6px rgba(0,0,0,.35);' +
        'cursor:pointer;position:relative;' +
        'transition:transform .2s;' +
        '" onmouseover="this.style.transform=\\'scale(1.3)\\'" ' +
        'onmouseout="this.style.transform=\\'scale(1)\\'">' +
        '<span style="' +
        'position:absolute;top:50%;left:50%;transform:translate(-50%,-50%);' +
        'font:bold 10px/1 sans-serif;color:#fff;' +
        '">' + (idx + 1) + '</span>' +
        '</div>';

    var marker = new AMap.Marker({{
        position: [p.glo, p.gla],
        content: mc,
        offset: new AMap.Pixel(-11, -11),
        title: p.n,
        extData: idx
    }});

    var imgHtml = p.img
        ? '<img src="data:image/jpeg;base64,' + p.img + '">'
        : '<div class="no-img">📷 无缩略图</div>';

    var iwContent =
        '<div class="iw">' +
        '<h3>📷 ' + p.n + '</h3>' +
        imgHtml +
        '<p>' +
        (p.d ? '拍摄时间：' + p.d + '<br>' : '') +
        'WGS-84: ' + p.wla.toFixed(6) + ', ' + p.wlo.toFixed(6) + '<br>' +
        'GCJ-02: ' + p.gla.toFixed(6) + ', ' + p.glo.toFixed(6) +
        '</p></div>';

    var iw = new AMap.InfoWindow({{
        content: iwContent,
        offset: new AMap.Pixel(0, -14),
        closeWhenClickMap: true
    }});

    marker.on('click', function() {{
        if (currentIW) currentIW.close();
        iw.open(map, marker.getPosition());
        currentIW = iw;
        var hint = document.getElementById('hint');
        if (hint) hint.style.opacity = '0';
    }});

    map.add(marker);
    markers.push(marker);
}});

// ✅ 修复：加完全部标记后自动适配视野（原版先建空 Bounds 再逐点 extend，
// 实测得到的是全世界范围且 extend 不收敛，setBounds 静默失效）
map.setFitView(markers, false, [60, 60, 60, 60]);

setTimeout(function() {{
    var h = document.getElementById('hint');
    if (h && h.style.opacity !== '0') h.style.opacity = '0';
}}, 6000);
</script></body></html>""".format(
        count=count, font=UI_FONT, sec=_security_config_html(),
        key=KEYS["js_key"], geo=_GEO_JS, js_array=js_array)


# ============================================================
# 主应用
# ============================================================
class PhotoExifViewer:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("%s %s" % (APP_TITLE, APP_VERSION))
        self.root.geometry("1320x860")
        self.root.minsize(1020, 700)

        self.photo_dir = ""
        self.photo_files = []
        self.selected_photo_path = ""
        self.gps_data = None

        self._q = queue_mod.Queue()
        self._scan_cancel = False
        self._scanning = False

        self._build_ui()
        self.root.after(80, self._poll)

        # 启动时提示 Key 配置状态
        missing = []
        if not KEYS["js_key"]:
            missing.append("JS API Key（地图）")
        if not KEYS["rest_key"]:
            missing.append("Web服务 Key（地址）")
        if missing:
            self.status_var.set(
                "⚠️ 未配置：%s。地图/地址功能受影响，请点击 [🔑 配置高德Key]。" %
                "、".join(missing))
        else:
            self.status_var.set("就绪（JS API Key 与 Web服务 Key 均已配置）")

    # ------------------------------------------------------------------ UI
    def _build_ui(self):
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass

        # ---------- 顶部工具栏 ----------
        toolbar = ttk.Frame(self.root, padding=6)
        toolbar.pack(fill=tk.X)

        self.btn_dir = ttk.Button(toolbar, text="📁 选择照片目录",
                                  command=self._select_directory)
        self.btn_dir.pack(side=tk.LEFT)

        self.all_map_btn = ttk.Button(
            toolbar, text="🗺️ 显示全部照片位置",
            command=self._toggle_all_photos_map, state=tk.DISABLED)
        self.all_map_btn.pack(side=tk.LEFT, padx=(10, 0))

        ttk.Button(toolbar, text="🔑 配置高德Key",
                   command=self._set_amap_key).pack(side=tk.LEFT, padx=(10, 0))

        ttk.Button(toolbar, text="❌ 退出程序",
                   command=self._exit_app).pack(side=tk.LEFT, padx=(10, 0))

        self.dir_var = tk.StringVar(value="未选择目录")
        ttk.Label(toolbar, textvariable=self.dir_var,
                  foreground="gray").pack(side=tk.LEFT, padx=15)

        # ---------- 主体 ----------
        body = ttk.Frame(self.root, padding=5)
        body.pack(fill=tk.BOTH, expand=True)

        # ---- 左侧：文件列表 ----
        left = ttk.LabelFrame(body, text="📋 照片文件列表", padding=5)
        left.pack(side=tk.LEFT, fill=tk.Y)

        list_inner = ttk.Frame(left)
        list_inner.pack(fill=tk.BOTH, expand=True)

        self.file_listbox = tk.Listbox(
            list_inner, selectmode=tk.SINGLE,
            font=(UI_FONT, 10), activestyle="none")
        sb = ttk.Scrollbar(list_inner, orient=tk.VERTICAL,
                           command=self.file_listbox.yview)
        self.file_listbox.config(yscrollcommand=sb.set)
        self.file_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        self.file_listbox.bind("<<ListboxSelect>>", self._on_photo_selected)

        self.count_label = ttk.Label(left, text="共 0 个文件")
        self.count_label.pack(pady=(4, 0))

        # ---- 右侧：信息 + 地图 ----
        right = ttk.Frame(body)
        right.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(6, 0))

        name_frame = ttk.LabelFrame(right, text="📸 当前照片", padding=5)
        name_frame.pack(fill=tk.X)
        self.name_var = tk.StringVar(value="未选择照片")
        ttk.Label(name_frame, textvariable=self.name_var,
                  font=(UI_FONT, 13, "bold")).pack()

        exif_frame = ttk.LabelFrame(right, text="📝 EXIF / GPS 信息", padding=5)
        exif_frame.pack(fill=tk.BOTH, expand=True, pady=(6, 0))

        self.exif_text = tk.Text(
            exif_frame, font=(MONO_FONT, 11),
            bg="#2b2b2b", fg="#e0e0e0",
            insertbackground="#e0e0e0", selectbackground="#4a6fa5",
            relief=tk.FLAT, wrap=tk.WORD, padx=10, pady=8)
        exif_sb = ttk.Scrollbar(exif_frame, orient=tk.VERTICAL,
                                command=self.exif_text.yview)
        self.exif_text.config(yscrollcommand=exif_sb.set)
        self.exif_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        exif_sb.pack(side=tk.RIGHT, fill=tk.Y)
        self.exif_text.config(state=tk.DISABLED)

        map_frame = ttk.LabelFrame(right, text="🗺️ 地图", padding=5)
        map_frame.pack(fill=tk.X, pady=(6, 0))

        self.map_btn = ttk.Button(
            map_frame, text="🗺️ 在高德地图上查看拍摄位置",
            command=self._show_map, state=tk.DISABLED)
        self.map_btn.pack(pady=8)

        self.map_status = ttk.Label(
            map_frame, text="选择有 GPS 信息的照片后可查看地图",
            foreground="gray")
        self.map_status.pack()

        # ---------- 底部状态栏 ----------
        self.status_var = tk.StringVar(value="就绪")
        ttk.Label(self.root, textvariable=self.status_var,
                  relief=tk.SUNKEN, anchor=tk.W,
                  padding=(6, 2)).pack(fill=tk.X, side=tk.BOTTOM)

    # ---------------------------------------------------------- Key 配置
    def _set_amap_key(self):
        dlg = tk.Toplevel(self.root)
        dlg.title("配置高德 API Key")
        dlg.geometry("560x330")
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.resizable(False, False)

        frm = ttk.Frame(dlg, padding=14)
        frm.pack(fill=tk.BOTH, expand=True)
        frm.columnconfigure(1, weight=1)

        ttk.Label(frm, text="各 Key 均在高德开放平台（lbs.amap.com）控制台申请，"
                            "明文保存在程序目录的 exif_viewer_config2.json。").grid(
            row=0, column=0, columnspan=3, sticky=tk.W, pady=(0, 10))

        v_js = tk.StringVar(value=KEYS["js_key"])
        v_code = tk.StringVar(value=KEYS["js_code"])
        v_rest = tk.StringVar(value=KEYS["rest_key"])

        ttk.Label(frm, text="JS API Key").grid(row=1, column=0, sticky=tk.W, pady=3)
        e1 = ttk.Entry(frm, textvariable=v_js, width=44)
        e1.grid(row=1, column=1, columnspan=2, sticky=tk.W, padx=(8, 0))
        ttk.Label(frm, text="「Web端(JS API)」类型，地图显示用", foreground="gray").grid(
            row=2, column=1, columnspan=2, sticky=tk.W)

        ttk.Label(frm, text="安全密钥").grid(row=3, column=0, sticky=tk.W, pady=3)
        e2 = ttk.Entry(frm, textvariable=v_code, width=44)
        e2.grid(row=3, column=1, columnspan=2, sticky=tk.W, padx=(8, 0))
        ttk.Label(frm, text="securityJsCode，与 JS API Key 成对申请；"
                            "2021-12-02 后申请的 key 必填", foreground="gray").grid(
            row=4, column=1, columnspan=2, sticky=tk.W)

        ttk.Label(frm, text="Web服务 Key").grid(row=5, column=0, sticky=tk.W, pady=3)
        e3 = ttk.Entry(frm, textvariable=v_rest, width=44)
        e3.grid(row=5, column=1, columnspan=2, sticky=tk.W, padx=(8, 0))
        ttk.Label(frm, text="「Web服务」类型，逆地理编码（地址）用", foreground="gray").grid(
            row=6, column=1, columnspan=2, sticky=tk.W)

        def save():
            KEYS["js_key"] = v_js.get().strip()
            KEYS["js_code"] = v_code.get().strip()
            KEYS["rest_key"] = v_rest.get().strip()
            try:
                save_config(KEYS)
                self._update_map_gate()
                self.status_var.set("✅ Key 配置已保存：%s" % CONFIG_PATH)
                dlg.destroy()
            except Exception as ex:
                messagebox.showerror("保存失败", "无法写入配置文件:\n%s" % ex,
                                     parent=dlg)

        btns = ttk.Frame(frm)
        btns.grid(row=7, column=0, columnspan=3, pady=(14, 0))
        ttk.Button(btns, text="保存", command=save).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(btns, text="取消", command=dlg.destroy).pack(side=tk.LEFT)
        e1.focus_set()

    def _update_map_gate(self):
        """根据当前照片 GPS 与 Key 配置刷新地图按钮状态。"""
        if self.gps_data:
            if KEYS["js_key"]:
                self.map_btn.config(state=tk.NORMAL)
                self.map_status.config(
                    text="GPS: (%.6f, %.6f)" % self.gps_data, foreground="green")
            else:
                self.map_btn.config(state=tk.DISABLED)
                self.map_status.config(
                    text="已读到 GPS，但未配置 JS API Key，无法显示地图",
                    foreground="#a04000")
        else:
            self.map_btn.config(state=tk.DISABLED)
            self.map_status.config(text="无 GPS 信息", foreground="gray")

    # ---------------------------------------------------------- 目录 & 列表
    def _select_directory(self):
        path = filedialog.askdirectory(title="选择照片目录")
        if not path:
            return
        self.photo_dir = path
        self.dir_var.set(path)
        self._load_photos()

    def _load_photos(self):
        self.file_listbox.delete(0, tk.END)
        self.photo_files.clear()
        try:
            entries = sorted(os.listdir(self.photo_dir))
        except OSError as e:
            messagebox.showerror("错误", "无法读取目录：%s" % e)
            return
        for name in entries:
            if os.path.splitext(name)[1].lower() in PHOTO_EXTENSIONS:
                self.photo_files.append(name)
                self.file_listbox.insert(tk.END, name)
        n = len(self.photo_files)
        self.count_label.config(text="共 %d 个文件" % n)
        self.all_map_btn.config(state=tk.NORMAL if n > 0 else tk.DISABLED)
        self.status_var.set("已加载 %d 个照片文件" % n)

    # ---------------------------------------------------------- 选择照片
    def _on_photo_selected(self, _event=None):
        sel = self.file_listbox.curselection()
        if not sel:
            return
        filename = self.photo_files[sel[0]]
        self.selected_photo_path = os.path.join(self.photo_dir, filename)
        self.name_var.set(filename)
        self.status_var.set("正在读取 %s 的 EXIF …" % filename)
        self._set_text(self.exif_text, "读取中…")
        # 后台线程：EXIF + 逆地理（网络请求不再冻结界面）
        threading.Thread(target=self._worker_exif,
                         args=(self.selected_photo_path,), daemon=True).start()

    def _worker_exif(self, path):
        try:
            lines, gps = read_exif_lines(path)
            self._q.put(("exif_done", (path, lines, gps)))
        except FileNotFoundError:
            self._q.put(("exif_no_exiftool", path))
        except Exception:
            import traceback
            self._q.put(("exif_error", (path, traceback.format_exc())))

    # ---------------------------------------------------------- 全部照片地图
    def _toggle_all_photos_map(self):
        if self._scanning:            # 扫描中再点一次 = 取消
            self._scan_cancel = True
            return
        if not self.photo_dir or not self.photo_files:
            messagebox.showwarning("提示", "请先选择包含照片的目录")
            return
        if not KEYS["js_key"]:
            messagebox.showwarning(
                "提示", "显示地图需要「Web端(JS API)」类型的 Key，"
                        "请先点击 [🔑 配置高德Key] 配置。")
            return
        self._scan_cancel = False
        self._scanning = True
        self.all_map_btn.config(text="⏹ 停止扫描")
        self.btn_dir.config(state=tk.DISABLED)
        threading.Thread(target=self._worker_scan, daemon=True).start()

    def _worker_scan(self):
        markers = []
        total = len(self.photo_files)
        try:
            for i, filename in enumerate(self.photo_files):
                if self._scan_cancel:
                    self._q.put(("scan_cancel", (len(markers), total)))
                    return
                filepath = os.path.join(self.photo_dir, filename)
                self._q.put(("scan_prog", (i + 1, total, filename)))
                lat, lon, date = quick_extract_gps(filepath)
                if lat is not None and lon is not None:
                    gcj_lat, gcj_lon = wgs84_to_gcj02(lat, lon)
                    markers.append({
                        "name": filename,
                        "wgs_lat": lat, "wgs_lon": lon,
                        "gcj_lat": gcj_lat, "gcj_lon": gcj_lon,
                        "date": date,
                        "img": img_to_base64(filepath),
                    })
            self._q.put(("scan_done", markers))
        except Exception:
            import traceback
            self._q.put(("scan_error", traceback.format_exc()))

    # ---------------------------------------------------------- 单张照片地图
    def _show_map(self):
        if not self.gps_data:
            messagebox.showwarning("提示", "当前照片无 GPS 信息")
            return
        if not KEYS["js_key"]:
            messagebox.showwarning("提示", "请先点击 [🔑 配置高德Key] 配置 JS API Key")
            return
        lat, lon = self.gps_data
        photo_name = os.path.basename(self.selected_photo_path)
        img_b64 = img_to_base64(self.selected_photo_path)
        html = build_single_map_html(lat, lon, photo_name, img_b64)
        html_path = os.path.join(tempfile.gettempdir(), "photo_map.html")
        with open(html_path, "w", encoding="utf-8") as f:
            f.write(html)
        webbrowser.open("file:///" + html_path.replace("\\", "/"))
        self.status_var.set("已在浏览器中打开高德地图")

    # ---------------------------------------------------------- 队列轮询
    def _poll(self):
        try:
            while True:
                kind, payload = self._q.get_nowait()
                if kind == "exif_done":
                    path, lines, gps = payload
                    if path != self.selected_photo_path:
                        continue                     # 用户已切到别的照片
                    self._set_text(self.exif_text, "\n".join(lines) + "\n")
                    self.gps_data = gps
                    self._update_map_gate()
                    self.status_var.set(
                        "已读取 %s 的 EXIF 信息" % os.path.basename(path))
                elif kind == "exif_no_exiftool":
                    messagebox.showerror(
                        "缺少 exiftool",
                        "未找到 exiftool，请先安装并加入系统 PATH。\n"
                        "下载地址：https://exiftool.org/")
                    self._exif_error("未找到 exiftool")
                elif kind == "exif_error":
                    path, tb = payload
                    self._set_text(self.exif_text, "⚠ 读取 EXIF 出错：\n%s" % tb)
                    self.gps_data = None
                    self._update_map_gate()
                    self.status_var.set("读取 EXIF 失败")
                elif kind == "scan_prog":
                    i, total, name = payload
                    self.status_var.set("扫描 GPS (%d/%d): %s" % (i, total, name))
                elif kind == "scan_done":
                    self._scan_finish()
                    if not payload:
                        messagebox.showinfo("提示", "目录下没有找到含 GPS 信息的照片")
                        self.status_var.set("未找到含 GPS 的照片")
                    else:
                        self.status_var.set(
                            "正在生成地图（%d 张照片有 GPS）…" % len(payload))
                        html = build_all_markers_map_html(payload)
                        html_path = os.path.join(tempfile.gettempdir(),
                                                 "all_photos_map.html")
                        with open(html_path, "w", encoding="utf-8") as f:
                            f.write(html)
                        webbrowser.open("file:///" + html_path.replace("\\", "/"))
                        self.status_var.set(
                            "已打开地图，共 %d 个照片坐标点" % len(payload))
                elif kind == "scan_cancel":
                    self._scan_finish()
                    self.status_var.set("已停止扫描（已找到 %d 个 GPS 点）" % payload[0])
                elif kind == "scan_error":
                    self._scan_finish()
                    self.status_var.set("扫描出错")
                    messagebox.showerror("扫描出错", payload.splitlines()[-1])
        except queue_mod.Empty:
            pass
        self.root.after(80, self._poll)

    def _scan_finish(self):
        self._scanning = False
        self.all_map_btn.config(text="🗺️ 显示全部照片位置")
        self.btn_dir.config(state=tk.NORMAL)

    # ---------------------------------------------------------- 工具方法
    @staticmethod
    def _set_text(widget: tk.Text, content: str):
        widget.config(state=tk.NORMAL)
        widget.delete("1.0", tk.END)
        widget.insert(tk.END, content)
        widget.config(state=tk.DISABLED)

    def _exif_error(self, msg: str):
        self._set_text(self.exif_text, "⚠ %s" % msg)
        self.gps_data = None
        self._update_map_gate()
        self.status_var.set("读取 EXIF 失败")

    def _exit_app(self):
        if messagebox.askyesno("确认退出", "确定要退出程序吗？"):
            self.root.destroy()


def main():
    root = tk.Tk()
    PhotoExifViewer(root)
    root.mainloop()


if __name__ == "__main__":
    main()
