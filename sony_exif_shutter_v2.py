#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Sony 照片 EXIF 信息读取器 v2（ttk / clam 风格）

功能：
- 读取 Sony 照片的相机型号、固件、镜头、机身序列号、真实快门数、拍摄时间、GPS
- GPS 有值时：WGS-84 → GCJ-02 转换后调用高德逆地理编码，显示中文地址
- 高德 Key 外置保存在程序同目录的 exif_viewer_config.json（明文），
  界面提供 [🔑 设置高德Key] 按钮，录入后先校验再保存
- 「运行 py」与「PyInstaller 编译后」都在程序同目录查找配置文件

依赖：仅 Python 标准库 + 系统 exiftool 命令行（不依赖 pyexiftool / requests）
"""

import json
import math
import os
import re
import subprocess
import sys
import threading
import queue as queue_mod
import urllib.error
import urllib.parse
import urllib.request
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

APP_TITLE = "Sony 照片 EXIF 信息读取器 v2"


# ============================================================
# 配置文件：与主程序/其他工具共用 exif_viewer_config.json
# 运行 py 用脚本目录；编译后用 exe/.app 所在目录
# ============================================================
def _config_path():
    if getattr(sys, "frozen", False):           # PyInstaller
        base = os.path.dirname(os.path.abspath(sys.executable))
        # macOS .app 包：回到 .app 所在目录
        parent = os.path.dirname(os.path.dirname(base))
        if sys.platform == "darwin" and parent.endswith(".app"):
            base = os.path.dirname(parent)
    else:
        base = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base, "exif_viewer_config.json")


CONFIG_PATH = _config_path()

#: 旧版配置可能写在任意工作目录，找到就迁移到程序目录
_LEGACY_CANDIDATES = [os.path.join(os.getcwd(), "exif_viewer_config.json")]


def load_config():
    """读配置，保留其它工具写入的字段（js_key/js_code 等）。
    兼容旧版单字段 amap_key → 迁移为 rest_key。"""
    cfg = {}
    for path in [CONFIG_PATH] + _LEGACY_CANDIDATES:
        if not os.path.exists(path):
            continue
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict) and data:
                cfg = data
                if path != CONFIG_PATH:          # 旧位置 → 迁到程序目录
                    save_config(cfg)
                break
        except Exception:
            continue
    if not cfg.get("rest_key") and cfg.get("amap_key"):
        cfg["rest_key"] = str(cfg["amap_key"]).strip()   # 旧字段迁移
    cfg.setdefault("rest_key", "")
    cfg.setdefault("js_key", "")
    cfg.setdefault("js_code", "")
    return cfg


def save_config(cfg):
    """明文写回，保留调用方传入的全部字段。"""
    try:
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(cfg, f, indent=2, ensure_ascii=False)
        return True
    except Exception as e:
        messagebox.showerror("保存失败", "无法写入配置文件：\n%s\n\n%s"
                             % (CONFIG_PATH, e))
        return False


KEYS = load_config()


# ============================================================
# exiftool 定位：编译版/Finder 双击启动时 PATH 常缺
# /opt/homebrew/bin 等目录，PATH 找不到就按常见安装位置兜底
# ============================================================
def find_exiftool():
    import shutil
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
                                 capture_output=True, text=True, timeout=5)
            p = out.stdout.strip()
            if p and os.path.isfile(p) and os.access(p, os.X_OK):
                return p
        except Exception:
            pass
    return None


EXIFTOOL = find_exiftool() or "exiftool"


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
# 坐标解析与合法性校验
# ============================================================
def parse_coord(value, ref=None):
    """解析坐标：-n 读出的数字已带符号（S/W 为负），不要按 Ref 再取反。"""
    if value is None:
        return None
    if isinstance(value, (int, float)):
        coord = float(value)
        if ref and coord > 0 and str(ref).strip().upper() in ("S", "W"):
            coord = -coord
        return coord
    s = str(value).strip()
    if not s:
        return None
    try:
        coord = float(s)
        if ref and coord > 0 and str(ref).strip().upper() in ("S", "W"):
            coord = -coord
        return coord
    except ValueError:
        pass
    m = re.match(r"([\d.]+)\s*(?:deg|°)\s*([\d.]+)\s*['′]\s*([\d.]+)\s*[\"″]?\s*([NSEW])?",
                 s, re.IGNORECASE)
    if m:
        d, mi, sec = float(m.group(1)), float(m.group(2)), float(m.group(3))
        coord = d + mi / 60 + sec / 3600
        direction = (m.group(4) or "").upper() or (str(ref).strip().upper() if ref else "")
        return -coord if direction in ("S", "W") else coord
    m2 = re.match(r"([\d.]+)\s*([NSEW])", s, re.IGNORECASE)
    if m2:
        coord = float(m2.group(1))
        return -coord if m2.group(2).upper() in ("S", "W") else coord
    return None


def gps_range_ok(lat, lon):
    """合法 GPS 范围：纬度 ±90、经度 ±180。
    （实测个别设备会写入越界脏数据，如大疆遥控器的 lat=1962/lon=6712）"""
    if lat is None or lon is None:
        return False
    return -90.0 <= lat <= 90.0 and -180.0 <= lon <= 180.0


# ============================================================
# WGS-84 → GCJ-02（高德/国测局坐标）
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
    magic = 1 - _EE * math.sin(rad_lat) ** 2
    sqrt_magic = math.sqrt(magic)
    d_lat = (d_lat * 180.0) / ((_A * (1 - _EE)) / (magic * sqrt_magic) * math.pi)
    d_lng = (d_lng * 180.0) / (_A / sqrt_magic * math.cos(rad_lat) * math.pi)
    return wgs_lat + d_lat, wgs_lng + d_lng


# ============================================================
# 高德 Web服务：Key 校验 + 逆地理编码（标准库 urllib，带证书降级）
# ============================================================
def _ssl_cert_error_type():
    try:
        return __import__("ssl").SSLCertVerificationError
    except Exception:
        return ()


def _urlopen_json(url, timeout=6):
    try:
        with urllib.request.urlopen(url, timeout=timeout) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.URLError as e:
        reason = getattr(e, "reason", None)
        if isinstance(reason, _ssl_cert_error_type()) or \
                "CERTIFICATE" in str(reason).upper():
            pass                                  # 证书问题 → 降级重试
        else:
            raise
    import ssl
    ctx = ssl.create_default_context()
    ctx.check_hostname = False
    ctx.verify_mode = ssl.CERT_NONE
    with urllib.request.urlopen(url, timeout=timeout, context=ctx) as resp:
        return json.loads(resp.read().decode("utf-8"))


#: 校验用的测试坐标（北京天安门），能取到地址说明 Key 可用
_TEST_LOCATION = "116.397428,39.909230"


def validate_amap_key(key, timeout=8):
    """校验 Key 是否为可用的「Web服务」Key。
    返回 (状态, 说明)：状态 ∈ {"ok", "bad", "net"}。"""
    key = (key or "").strip()
    if not key:
        return "bad", "Key 不能为空"
    qs = urllib.parse.urlencode({
        "key": key, "location": _TEST_LOCATION, "extensions": "base",
    })
    url = "https://restapi.amap.com/v3/geocode/regeo?" + qs
    try:
        data = _urlopen_json(url, timeout=timeout)
    except Exception as e:
        return "net", "网络异常，无法校验：%s" % e

    info = str(data.get("info", ""))
    if data.get("status") == "1":
        addr = (data.get("regeocode") or {}).get("formatted_address", "")
        return "ok", "校验通过，示例地址：%s" % (addr or "（空）")
    if "PLAT_NOMATCH" in info.upper():
        return "bad", "这是「Web端(JS API)」Key，本工具需要「Web服务」Key"
    if "INVALID_USER_KEY" in info.upper():
        return "bad", "Key 无效或已被删除"
    if "OVER_LIMIT" in info.upper() or "QUOTA" in info.upper():
        return "bad", "Key 有效但今日配额已用尽（%s）" % info
    return "bad", "校验失败（%s）" % (info or "未知错误")


def reverse_geocode(key, gcj_lat, gcj_lon, timeout=8):
    """GCJ-02 坐标 → 中文地址；失败返回以「解析失败」开头的说明，不抛异常。"""
    if not key:
        return "（未配置高德 Key，未解析地址）"
    qs = urllib.parse.urlencode({
        "key": key,
        "location": "%.6f,%.6f" % (gcj_lon, gcj_lat),
        "extensions": "base",
    })
    try:
        data = _urlopen_json(
            "https://restapi.amap.com/v3/geocode/regeo?" + qs, timeout=timeout)
        if data.get("status") == "1":
            return (data.get("regeocode") or {}).get("formatted_address", "解析失败")
        return "解析失败（%s）" % data.get("info", "")
    except Exception as e:
        return "解析失败：%s" % e


# ============================================================
# exiftool 读取（标准库 subprocess）
# ============================================================
def _run_exiftool(args, timeout=30):
    return subprocess.run([EXIFTOOL] + args, capture_output=True,
                          text=True, encoding="utf-8", errors="replace",
                          timeout=timeout)


def _meta_get(meta, *names):
    """按「分组:标签 → 裸标签」两种写法取值，返回第一个非空。"""
    for n in names:
        if ":" in n and meta.get(n):
            return meta[n]
        for k, v in meta.items():
            if k.split(":")[-1] == n and v not in (None, ""):
                return v
    return None


def read_photo_info(file_path):
    """读取照片信息，返回 dict（可独立测试）：
    {file_name, directory, model, firmware, lens, serial, shutter, date,
     lat, lon, alt, gps_raw, gps_invalid}
    """
    proc = _run_exiftool(["-json", "-n", "-c", "%.6f",
                          "-charset", "filename=utf8", file_path])
    if proc.returncode != 0:
        raise RuntimeError("exiftool 错误：%s" % (proc.stderr or "").strip()[:300])
    try:
        meta = json.loads(proc.stdout)[0]
    except Exception:
        raise RuntimeError("未能解析 exiftool 输出")

    info = {
        "file_name": os.path.basename(file_path),
        "directory": os.path.dirname(file_path) or _meta_get(meta, "Directory") or "未找到",
        "model": _meta_get(meta, "Model") or "未找到",
        "firmware": _meta_get(meta, "Software") or "未找到",
        "lens": _meta_get(meta, "LensModel", "LensInfo", "Lens") or "未找到",
        "serial": _meta_get(meta, "SerialNumber", "InternalSerialNumber") or "未找到",
        "date": _meta_get(meta, "DateTimeOriginal", "CreateDate") or "未找到",
        "shutter": None,
        "lat": None, "lon": None, "alt": None,
        "gps_raw": None, "gps_invalid": False,
    }
    if isinstance(info["lens"], (list, tuple)):
        info["lens"] = " ".join(str(x) for x in info["lens"])

    # ---- 真实快门数：先按已知标签，再按关键字扫描（Sony 机型差异大）----
    shutter = _meta_get(meta, "ShutterCount", "ImageCount",
                        "ShutterActuationCount", "ReleaseMode2")
    if not shutter:
        for k, v in meta.items():
            kl = k.lower()
            if "shutter" in kl and "count" in kl and v not in (None, ""):
                shutter = v
                break
    if not shutter:
        for k, v in meta.items():
            if k.lower().endswith("imagecount") and v not in (None, ""):
                shutter = v
                break
    info["shutter"] = shutter if shutter not in (None, "") else "未找到"

    # ---- GPS：优先 EXIF 坐标 + Ref；退回 Composite（已含符号）----
    lat = parse_coord(_meta_get(meta, "GPSLatitude"), _meta_get(meta, "GPSLatitudeRef"))
    lon = parse_coord(_meta_get(meta, "GPSLongitude"), _meta_get(meta, "GPSLongitudeRef"))
    if lat is None or lon is None:
        lat = lat if lat is not None else parse_coord(_meta_get(meta, "GPSLatitude"))
        lon = lon if lon is not None else parse_coord(_meta_get(meta, "GPSLongitude"))
    alt = _meta_get(meta, "GPSAltitude")

    if lat is not None and lon is not None:
        if gps_range_ok(lat, lon):
            info["lat"], info["lon"] = lat, lon
            info["alt"] = alt
        else:
            info["gps_raw"] = (lat, lon)
            info["gps_invalid"] = True
    return info


def build_report(info, rest_key, geocode=True):
    """把 info 排版成展示文本。geocode=False 时跳过网络请求。"""
    # ── 第一块：基本信息（字段之间空行，与原版观感一致）──
    head = "\n\n".join([
        "📁 文件名: %s" % info["file_name"],
        "📁 存放路径: %s" % info["directory"],
        "📷 相机型号: %s" % info["model"],
        "⚙️ 固件版本: %s" % info["firmware"],
        "🔭 镜头型号: %s" % info["lens"],
        "🔢 机身序列号: %s" % info["serial"],
        "🔧 实际快门数: %s" % info["shutter"],
    ])

    # ── 第二块：GPS 与中文地址 ──
    gps = []
    if info["gps_invalid"]:
        lat, lon = info["gps_raw"]
        gps += [
            "📍 GPS坐标: ⚠ 数据非法（%.6f, %.6f）" % (lat, lon),
            "   纬度须在 ±90、经度须在 ±180 内，该坐标越界",
            "   （疑似设备错误写入），已跳过坐标转换与地址解析。",
            "🏠 中文地址: 无（GPS 数据非法）",
        ]
    elif info["lat"] is not None:
        gcj_lat, gcj_lon = wgs84_to_gcj02(info["lat"], info["lon"])
        gps += [
            "📍 GPS坐标(WGS-84): %.6f, %.6f" % (info["lat"], info["lon"]),
            "📍 高德坐标(GCJ-02): %.6f, %.6f" % (gcj_lat, gcj_lon),
        ]
        if info["alt"] is not None:
            gps.append("🏔️ 海拔: %s m" % info["alt"])
        if not rest_key:
            gps.append("🏠 中文地址: （未配置高德 API Key，不显示地址）")
        elif geocode:
            gps.append("🏠 中文地址: %s" % reverse_geocode(rest_key, gcj_lat, gcj_lon))
        else:
            gps.append("🏠 中文地址: （读取中…）")
    else:
        gps += ["📍 GPS坐标: 未记录", "🏠 中文地址: 无GPS信息"]

    # ── 第三块：拍摄时间 ──
    tail = "⏱️ 拍摄时间: %s" % info["date"]
    return "\n\n".join([head, "\n".join(gps), tail])


# ============================================================
# 高德 Key 录入窗口
# ============================================================
class KeyDialog(tk.Toplevel):
    """录入 → 在线校验 → 保存到 exif_viewer_config.json。"""

    def __init__(self, parent, on_saved=None):
        super().__init__(parent)
        self.parent = parent
        self.on_saved = on_saved
        self.result_q = queue_mod.Queue()

        self.title("设置高德 API Key")
        self.configure(bg="#f0f0f0")
        self.resizable(False, False)
        self.transient(parent)
        self.grab_set()

        pad = {"padx": 18, "pady": 6}
        tk.Label(self, text="高德 Web服务 Key", bg="#f0f0f0",
                 font=(UI_FONT, 12, "bold")).grid(row=0, column=0,
                                                  sticky="w", padx=18, pady=(16, 2))
        hint = ("用途：把照片 GPS 转成高德坐标后查询中文拍摄地址。\n"
                "获取：高德开放平台 → 应用管理 → 创建应用 → 添加 Key，\n"
                "　　　服务平台必须选「Web服务」（不是「Web端(JS API)」）。")
        tk.Label(self, text=hint, bg="#f0f0f0", fg="#666666", justify="left",
                 font=(UI_FONT, 10)).grid(row=1, column=0, sticky="w", padx=18)

        self.key_var = tk.StringVar(value=KEYS.get("rest_key", ""))
        self.entry = ttk.Entry(self, textvariable=self.key_var, width=48,
                               font=(MONO_FONT, 12))
        self.entry.grid(row=2, column=0, sticky="we", padx=18, pady=(10, 4))

        self.status_var = tk.StringVar(value="录入后请点击「校验并保存」")
        self.status_label = ttk.Label(self, textvariable=self.status_var,
                                      style="Hint.TLabel", wraplength=420,
                                      justify="left")
        self.status_label.grid(row=3, column=0, sticky="w", padx=18, pady=(0, 8))

        btns = ttk.Frame(self)
        btns.grid(row=4, column=0, sticky="e", padx=18, pady=(0, 16))
        self.save_btn = ttk.Button(btns, text="✅ 校验并保存", style="Accent.TButton",
                                   command=self.on_validate_save)
        self.save_btn.pack(side="left", padx=4)
        ttk.Button(btns, text="🗑 清除已保存 Key",
                   command=self.on_clear).pack(side="left", padx=4)
        ttk.Button(btns, text="取消", command=self.destroy).pack(side="left", padx=4)

        self.bind("<Return>", lambda e: self.on_validate_save())
        self.entry.focus_set()
        self.after(100, self._center)
        self.after(100, self._poll)

    def _center(self):
        self.update_idletasks()
        p = self.parent
        x = p.winfo_rootx() + (p.winfo_width() - self.winfo_width()) // 2
        y = p.winfo_rooty() + (p.winfo_height() - self.winfo_height()) // 3
        self.geometry("+%d+%d" % (max(x, 0), max(y, 0)))

    # ---- 校验并保存 ----
    def on_validate_save(self):
        key = self.key_var.get().strip()
        if not key:
            self.status_var.set("⚠ 请先粘贴 Key")
            return
        self.save_btn.config(state="disabled")
        self.status_var.set("⏳ 正在校验 Key…")
        threading.Thread(target=self._worker_validate, args=(key,),
                         daemon=True).start()

    def _worker_validate(self, key):
        try:
            state, msg = validate_amap_key(key)
        except Exception as e:
            state, msg = "net", "校验异常：%s" % e
        self.result_q.put((state, msg, key))

    def _poll(self):
        try:
            while True:
                state, msg, key = self.result_q.get_nowait()
                self.save_btn.config(state="normal")
                if state == "ok":
                    KEYS["rest_key"] = key
                    if not save_config(KEYS):
                        self.status_var.set("❌ 保存失败")
                        continue
                    self.status_var.set("✅ %s（已保存）\n%s" % (msg, CONFIG_PATH))
                    if self.on_saved:
                        self.on_saved()
                    self.after(700, self.destroy)
                elif state == "net":
                    self.status_var.set("⚠ %s" % msg)
                    if messagebox.askyesno(
                            "网络异常", "%s\n\n仍要保存这个 Key 吗？" % msg, parent=self):
                        KEYS["rest_key"] = key
                        if save_config(KEYS):
                            self.status_var.set("⚠ 已保存（未经校验）")
                            if self.on_saved:
                                self.on_saved()
                            self.after(500, self.destroy)
                else:
                    self.status_var.set("❌ %s" % msg)
        except queue_mod.Empty:
            pass
        if self.winfo_exists():
            self.after(120, self._poll)

    def on_clear(self):
        if not messagebox.askyesno("确认", "清除配置文件中保存的高德 Key？", parent=self):
            return
        KEYS["rest_key"] = ""
        if save_config(KEYS):
            self.key_var.set("")
            self.status_var.set("已清除 Key（照片将不再显示中文地址）")
            if self.on_saved:
                self.on_saved()


# ============================================================
# 主界面（ttk / clam）
# ============================================================
class SonyExifReaderGUI:
    def __init__(self, root):
        self.root = root
        self.root.title(APP_TITLE)
        self.root.geometry("760x680")
        self.root.minsize(640, 520)

        self.current_path = None
        self.info_q = queue_mod.Queue()

        self._setup_style()
        self._build_ui()
        self.root.after(120, self._poll_info)
        self.root.after(300, self._startup_check)

    # ---------------------------------------------------------- 样式
    def _setup_style(self):
        style = ttk.Style(self.root)
        try:
            style.theme_use("clam")              # 统一 clam 风格
        except tk.TclError:
            pass
        bg = "#f0f0f0"
        self.root.configure(bg=bg)

        style.configure(".", font=(UI_FONT, 11), background=bg)
        style.configure("TFrame", background=bg)
        style.configure("TLabel", background=bg, foreground="#222222")
        style.configure("Title.TLabel", font=(UI_FONT, 18, "bold"),
                        foreground="#2c3e50")
        style.configure("Hint.TLabel", font=(UI_FONT, 10), foreground="#666666")
        style.configure("Info.TLabel", font=(UI_FONT, 10), foreground="#1a5fb4")
        style.configure("Card.TLabelframe", background="#ffffff")
        style.configure("Card.TLabelframe.Label", background=bg,
                        font=(UI_FONT, 11, "bold"))

        style.configure("TButton", font=(UI_FONT, 11), padding=(10, 6))
        style.configure("Accent.TButton", font=(UI_FONT, 11, "bold"),
                        foreground="#ffffff", background="#4CAF50",
                        padding=(12, 7))
        style.map("Accent.TButton",
                  background=[("active", "#45a049"), ("disabled", "#a5d6a7")])
        style.configure("Key.TButton", font=(UI_FONT, 11, "bold"),
                        foreground="#ffffff", background="#1a73e8",
                        padding=(12, 7))
        style.map("Key.TButton",
                  background=[("active", "#1666cc"), ("disabled", "#9dc0f0")])
        style.configure("Danger.TButton", font=(UI_FONT, 11, "bold"),
                        foreground="#ffffff", background="#e74c3c",
                        padding=(12, 7))
        style.map("Danger.TButton",
                  background=[("active", "#c0392b"), ("disabled", "#f0a49c")])

    # ---------------------------------------------------------- 布局
    def _build_ui(self):
        outer = ttk.Frame(self.root, padding=(16, 14, 16, 10))
        outer.pack(fill="both", expand=True)

        ttk.Label(outer, text="📷 Sony 照片 EXIF 信息读取器",
                  style="Title.TLabel").pack(pady=(0, 4))
        ttk.Label(outer, text="读取机身序列号、真实快门数、拍摄时间与 GPS 拍摄地",
                  style="Hint.TLabel").pack(pady=(0, 12))

        bar = ttk.Frame(outer)
        bar.pack(fill="x", pady=(0, 10))
        ttk.Button(bar, text="📂 选择照片", style="Accent.TButton",
                   command=self.select_file).pack(side="left")
        ttk.Button(bar, text="🔑 设置高德Key", style="Key.TButton",
                   command=self.open_key_dialog).pack(side="left", padx=8)
        ttk.Button(bar, text="💾 保存结果", command=self.save_result).pack(side="left")
        ttk.Button(bar, text="❌ 退出", style="Danger.TButton",
                   command=self.root.destroy).pack(side="right")

        card = ttk.LabelFrame(outer, text="EXIF 信息", style="Card.TLabelframe",
                              padding=8)
        card.pack(fill="both", expand=True)
        self.text = tk.Text(card, wrap="word", font=(MONO_FONT, 14),
                            bg="#ffffff", fg="#2c3e50", padx=14, pady=12,
                            relief="flat", borderwidth=0, state="disabled")
        sb = ttk.Scrollbar(card, orient="vertical", command=self.text.yview)
        self.text.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.text.pack(side="left", fill="both", expand=True)

        self.status_var = tk.StringVar(value="就绪")
        self.status_label = ttk.Label(outer, textvariable=self.status_var,
                                      style="Info.TLabel", anchor="w")
        self.status_label.pack(fill="x", pady=(8, 0))

        self._refresh_key_status()

    # ---------------------------------------------------------- 状态
    def _refresh_key_status(self):
        if KEYS.get("rest_key"):
            self.status_var.set("已配置高德 Key：%s…（配置文件 %s）"
                                % (KEYS["rest_key"][:8], CONFIG_PATH))
        else:
            self.status_var.set("未配置高德 Key — 照片有 GPS 时不会显示中文地址"
                                "（点「🔑 设置高德Key」录入）")

    def _set_text(self, s):
        self.text.config(state="normal")
        self.text.delete("1.0", "end")
        self.text.insert("1.0", s)
        self.text.config(state="disabled")

    # ---------------------------------------------------------- 启动检查
    def _startup_check(self):
        """配置文件不存在 / 没有 Key 时提示录入。"""
        has_file = os.path.exists(CONFIG_PATH)
        has_key = bool(KEYS.get("rest_key"))
        if has_key:
            return
        if not has_file:
            msg = ("未找到高德 API Key 配置文件：\n%s\n\n"
                   "没有 Key 时，照片的中文拍摄地址将无法显示。\n"
                   "是否现在录入？" % CONFIG_PATH)
        else:
            msg = ("配置文件中还没有「高德 Web服务 Key」：\n%s\n\n"
                   "没有 Key 时，照片的中文拍摄地址将无法显示。\n"
                   "是否现在录入？" % CONFIG_PATH)
        if messagebox.askyesno("需要配置高德 Key", msg, parent=self.root):
            self.open_key_dialog()

    # ---------------------------------------------------------- 选择照片
    def select_file(self):
        path = filedialog.askopenfilename(
            title="选择一张 Sony 照片",
            filetypes=[("照片文件", "*.jpg *.jpeg *.arw *.tif *.tiff *.png *.heic *.hif"),
                       ("所有文件", "*.*")])
        if not path:
            return
        self.current_path = path
        self.status_var.set("正在读取 %s …" % os.path.basename(path))
        self._set_text("读取中…")
        threading.Thread(target=self._worker_read, args=(path,), daemon=True).start()

    def _worker_read(self, path):
        try:
            if EXIFTOOL == "exiftool" and find_exiftool() is None:
                self.info_q.put(("no_exiftool", None))
                return
            info = read_photo_info(path)
            # 无 GPS 或 无 Key 时不发网络请求
            need_geo = (info["lat"] is not None and bool(KEYS.get("rest_key")))
            text = build_report(info, KEYS.get("rest_key", ""), geocode=need_geo)
            self.info_q.put(("done", (path, text)))
        except Exception as e:
            self.info_q.put(("error", (path, str(e))))

    def _poll_info(self):
        try:
            while True:
                kind, payload = self.info_q.get_nowait()
                if kind == "no_exiftool":
                    messagebox.showerror(
                        "缺少 exiftool",
                        "未找到 exiftool，请先安装并加入 PATH。\n"
                        "下载地址：https://exiftool.org/")
                    self._set_text("⚠ 未找到 exiftool")
                    self.status_var.set("读取失败：缺少 exiftool")
                elif kind == "done":
                    path, text = payload
                    if path != self.current_path:
                        continue
                    self._set_text(text)
                    self.status_var.set("已读取 %s" % os.path.basename(path))
                elif kind == "error":
                    path, err = payload
                    if path != self.current_path:
                        continue
                    self._set_text("⚠ 读取失败：\n%s" % err)
                    self.status_var.set("读取失败")
        except queue_mod.Empty:
            pass
        self.root.after(120, self._poll_info)

    # ---------------------------------------------------------- Key 窗口
    def open_key_dialog(self):
        KeyDialog(self.root, on_saved=self._after_key_saved)

    def _after_key_saved(self):
        self._refresh_key_status()
        if self.current_path:                      # 已有照片则刷新地址
            self.select_file_refresh()

    def select_file_refresh(self):
        path = self.current_path
        if not path:
            return
        self.status_var.set("Key 已更新，正在刷新地址…")
        threading.Thread(target=self._worker_read, args=(path,), daemon=True).start()

    # ---------------------------------------------------------- 保存结果
    def save_result(self):
        content = self.text.get("1.0", "end").strip()
        if not content or content == "读取中…":
            messagebox.showinfo("提示", "还没有可保存的内容", parent=self.root)
            return
        default = "exif_result.txt"
        if self.current_path:
            default = os.path.splitext(os.path.basename(self.current_path))[0] + "_exif.txt"
        path = filedialog.asksaveasfilename(
            title="保存读取结果", initialfile=default,
            defaultextension=".txt",
            filetypes=[("文本文件", "*.txt"), ("所有文件", "*.*")])
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write(content + "\n")
            self.status_var.set("已保存：%s" % path)
        except Exception as e:
            messagebox.showerror("保存失败", str(e), parent=self.root)


# ============================================================
if __name__ == "__main__":
    root = tk.Tk()
    app = SonyExifReaderGUI(root)
    root.mainloop()
