#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
照片 GPS 坐标管理工具 - 修复版 v2.1
在原版基础上修复以下问题：
  1. [P0] 地图瓦片改为异步加载（后台线程 + 占位图 + 防抖补绘），不再阻塞界面
  2. [P1] RAW 缩略图提取改为按 ThumbnailImage → JpgFromRaw → PreviewImage 逐个尝试，
          避免多标签二进制拼接产出非法图片
  3. [P1] 地址反查加入请求序号校验，快速切换照片/选点时丢弃过期结果，不再"串门"
  4. [P1] 坐标解析保留南纬/西经符号：含 S/W 字母时返回负值；Ref 字段缺失时不再丢失符号
  5. [P1] 写入 GPS/日期前自动备份原文件到照片目录**同级**的可见 exif_backup/ 目录
          （如照片在 /Users/xxx/Photos，备份在 /Users/xxx/exif_backup；Finder 直接可见），
          备份失败则取消写入
  6. [P2] 兼容 Linux 滚轮（Button-4/Button-5），缩放操作加防抖
  7. [P2] 瓦片缓存改为 LRU（上限 512 张），防止内存无限增长
  8. [P2] tk scaling 按系统真实 DPI 计算，替代硬编码 2.0
  9. [P2] 清理裸 except，统一为 except Exception 并在状态栏输出关键错误
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import os, sys, json, math, subprocess, threading, io, re, platform, shutil
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime

def _config_path():
    if getattr(sys, "frozen", False):          # pyinstaller
        base = os.path.dirname(os.path.abspath(sys.executable))
    else:
        base = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base, "exif_viewer_config.json")

try:
    import requests
except ImportError:
    print("请安装 requests: pip install requests");
    sys.exit(1)

try:
    from PIL import Image, ImageTk, ExifTags
except ImportError:
    print("请安装 Pillow: pip install Pillow");
    sys.exit(1)

try:
    import pillow_heif

    pillow_heif.register_heif_opener()
except ImportError:
    pass

AMAP_KEY = ""
#CONFIG_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "exif_viewer_config.json")
CONFIG_FILE = _config_path()
# print(CONFIG_FILE)

SUPPORTED_EXTENSIONS = {'.jpg', '.jpeg', '.png', '.tiff', '.tif', '.bmp', '.gif',
                        '.heic', '.heif','.hif', '.webp', '.raw', '.cr2', '.nef', '.arw', '.dng', '.orf', '.rw2'}
RAW_EXTENSIONS = {'.raw', '.cr2', '.nef', '.arw', '.dng', '.orf', '.rw2'}

IS_WIN = platform.system() == "Windows"

# 备份目录：选择照片目录时自动设为其同级的 exif_backup/（可见目录，Finder 不隐藏）
BACKUP_DIR = ""


# ─────────────── 跨平台字体与样式适配 ───────────────
class StyleAdapter:
    @staticmethod
    def get_font(size=10, bold=False):
        if IS_WIN:
            family = 'Microsoft YaHei UI'
            size = max(9, size)
        else:
            family = 'PingFang SC'
        weight = 'bold' if bold else 'normal'
        return (family, size, weight)

    @staticmethod
    def apply_styles(style):
        BG = '#f0f0f0'
        style.theme_use('clam')
        style.configure('TLabel', background=BG, font=StyleAdapter.get_font(10))
        style.configure('TFrame', background=BG)
        style.configure('Toolbar.TButton', padding=(8, 4), font=StyleAdapter.get_font(10))
        style.configure('Action.TButton', padding=(10, 6), font=StyleAdapter.get_font(10))
        style.configure('Info.TLabel', font=StyleAdapter.get_font(9), background=BG)
        style.configure('KeyOK.TLabel', foreground='green', background=BG, font=StyleAdapter.get_font(9))
        style.configure('KeyMissing.TLabel', foreground='red', background=BG, font=StyleAdapter.get_font(9))
        style.configure('Treeview', rowheight=26, background='#fff', fieldbackground='#fff',
                        font=StyleAdapter.get_font(9))
        style.configure('Treeview.Heading', font=StyleAdapter.get_font(10, bold=True))
        if IS_WIN:
            style.configure('Compact.TButton', padding=(5, 3), font=StyleAdapter.get_font(9))
        else:
            style.configure('Compact.TButton', padding=(7, 4), font=StyleAdapter.get_font(9))


# ─────────────── 坐标转换 ───────────────
class CoordTransform:
    PI = math.pi;
    A = 6378245.0;
    EE = 0.00669342162296594323

    @staticmethod
    def _transform_lat(lng, lat):
        ret = (-100 + 2 * lng + 3 * lat + 0.2 * lat * lat + 0.1 * lng * lat + 0.2 * math.sqrt(abs(lng)))
        ret += (20 * math.sin(6 * lng * CoordTransform.PI) + 20 * math.sin(2 * lng * CoordTransform.PI)) * 2 / 3
        ret += (20 * math.sin(lat * CoordTransform.PI) + 40 * math.sin(lat / 3 * CoordTransform.PI)) * 2 / 3
        ret += (160 * math.sin(lat / 12 * CoordTransform.PI) + 320 * math.sin(lat * CoordTransform.PI / 30)) * 2 / 3
        return ret

    @staticmethod
    def _transform_lng(lng, lat):
        ret = (300 + lng + 2 * lat + 0.1 * lng * lng + 0.1 * lng * lat + 0.1 * math.sqrt(abs(lng)))
        ret += (20 * math.sin(6 * lng * CoordTransform.PI) + 20 * math.sin(2 * lng * CoordTransform.PI)) * 2 / 3
        ret += (20 * math.sin(lng * CoordTransform.PI) + 40 * math.sin(lng / 3 * CoordTransform.PI)) * 2 / 3
        ret += (150 * math.sin(lng / 12 * CoordTransform.PI) + 300 * math.sin(lng / 30 * CoordTransform.PI)) * 2 / 3
        return ret

    @staticmethod
    def _out_of_china(lng, lat):
        return not (72.004 <= lng <= 137.8347 and 0.8293 <= lat <= 55.8271)

    @staticmethod
    def wgs84_to_gcj02(lng, lat):
        if CoordTransform._out_of_china(lng, lat): return lng, lat
        dlat = CoordTransform._transform_lat(lng - 105, lat - 35)
        dlng = CoordTransform._transform_lng(lng - 105, lat - 35)
        radlat = lat / 180 * CoordTransform.PI
        magic = math.sin(radlat);
        magic = 1 - CoordTransform.EE * magic * magic
        smagic = math.sqrt(magic)
        dlat = (dlat * 180) / ((CoordTransform.A * (1 - CoordTransform.EE)) / (magic * smagic) * CoordTransform.PI)
        dlng = (dlng * 180) / (CoordTransform.A / smagic * math.cos(radlat) * CoordTransform.PI)
        return lng + dlng, lat + dlat

    @staticmethod
    def gcj02_to_wgs84(lng, lat):
        if CoordTransform._out_of_china(lng, lat): return lng, lat
        gl, ga = CoordTransform.wgs84_to_gcj02(lng, lat)
        return lng - (gl - lng), lat - (ga - lat)


# ─────────────── 瓦片管理（异步加载 + LRU 缓存） ───────────────
class TileManager:
    TS = 256
    CACHE_MAX = 512
    _cache = OrderedDict()   # LRU：最近使用的放尾部
    _pending = set()         # 正在下载的瓦片
    _failed = set()          # 下载失败的瓦片（本次缩放级别内不再重试）
    _lock = threading.Lock()
    _pool = ThreadPoolExecutor(max_workers=6)
    _session = requests.Session()

    @staticmethod
    def lnglat_to_pixel(lng, lat, z):
        n = 2 ** z
        x = (lng + 180) / 360 * n * TileManager.TS
        lr = math.radians(lat)
        y = (1 - math.log(math.tan(lr) + 1 / math.cos(lr)) / math.pi) / 2 * n * TileManager.TS
        return x, y

    @staticmethod
    def pixel_to_lnglat(px, py, z):
        n = 2 ** z
        lng = px / (n * TileManager.TS) * 360 - 180
        lr = math.atan(math.sinh(math.pi * (1 - 2 * py / (n * TileManager.TS))))
        return lng, math.degrees(lr)

    @staticmethod
    def get_cached(x, y, z):
        """同步取缓存中的瓦片，未命中返回 None（不阻塞）"""
        k = (x, y, z)
        with TileManager._lock:
            if k in TileManager._cache:
                TileManager._cache.move_to_end(k)
                return TileManager._cache[k]
        return None

    @staticmethod
    def _cache_put(key, img):
        with TileManager._lock:
            TileManager._cache[key] = img
            while len(TileManager._cache) > TileManager.CACHE_MAX:
                TileManager._cache.popitem(last=False)

    @staticmethod
    def fetch_async(key, on_ready):
        """异步下载瓦片，成功后回调 on_ready(key)。失败进入 _failed 集合，不反复重试"""
        with TileManager._lock:
            if key in TileManager._cache or key in TileManager._pending or key in TileManager._failed:
                return
            TileManager._pending.add(key)
        TileManager._pool.submit(TileManager._download, key, on_ready)

    @staticmethod
    def _download(key, on_ready):
        x, y, z = key
        ss = ['webrd01', 'webrd02', 'webrd03', 'webrd04']
        url = f"https://{ss[(x + y) % 4]}.is.autonavi.com/appmaptile?lang=zh_cn&size=1&scale=1&style=8&x={x}&y={y}&z={z}"
        try:
            r = TileManager._session.get(url, timeout=6,
                                         headers={'User-Agent': 'Mozilla/5.0', 'Referer': 'https://www.amap.com'})
            if r.status_code == 200:
                img = Image.open(io.BytesIO(r.content))
                img.load()
                TileManager._cache_put(key, img)
                on_ready(key)
                return
        except Exception:
            pass
        with TileManager._lock:
            TileManager._pending.discard(key)
            TileManager._failed.add(key)

    @staticmethod
    def clear_failed():
        with TileManager._lock:
            TileManager._failed.clear()


# ─────────────── ExifTool (跨平台兼容) ───────────────
class ExifTool:
    @staticmethod
    def _run(args, binary=False):
        env = os.environ.copy()
        cmd = ['exiftool'] + args
        startupinfo = None
        if IS_WIN:
            startupinfo = subprocess.STARTUPINFO()
            startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
            startupinfo.wShowWindow = 0
        try:
            r = subprocess.run(
                cmd, capture_output=True, timeout=30,
                encoding=None if binary else 'utf-8',
                errors=None if binary else 'replace',
                env=env, startupinfo=startupinfo
            )
            return r.stdout, r.stderr, r.returncode
        except FileNotFoundError:
            hint = "Windows: 下载exiftool.exe放入PATH或程序同目录\nmacOS: brew install exiftool"
            return b"" if binary else "", f"exiftool 未安装。\n{hint}", 1
        except subprocess.TimeoutExpired:
            return b"" if binary else "", "exiftool 执行超时", 1

    @staticmethod
    def read_exif(fp):
        out, _, rc = ExifTool._run([
            '-json', '-charset', 'utf8',
            '-DateTimeOriginal', '-CreateDate', '-ModifyDate',
            '-Model', '-Make', '-LensModel', '-LensInfo',
            '-GPSLatitude', '-GPSLongitude',
            '-GPSLatitudeRef', '-GPSLongitudeRef',
            '-ImageWidth', '-ImageHeight',
            '-FocalLength', '-FNumber', '-ExposureTime', '-ISO',
            '-Orientation', fp
        ])
        if rc != 0: return {}
        try:
            cleaned = out.strip().lstrip('\ufeff')
            d = json.loads(cleaned)
            return d[0] if d else {}
        except Exception:
            return {}

    @staticmethod
    def _extract_single_tag(fp, tag):
        """提取单个二进制标签（一次只请求一个，避免多标签二进制拼接成非法图片）"""
        out, _, rc = ExifTool._run(['-b', tag, fp], binary=True)
        if rc == 0 and len(out) > 1000:
            try:
                return Image.open(io.BytesIO(out))
            except Exception:
                return None
        return None

    @staticmethod
    def extract_thumbnail(fp):
        """按优先级逐个尝试：ThumbnailImage → JpgFromRaw → PreviewImage"""
        for tag in ('-ThumbnailImage', '-JpgFromRaw', '-PreviewImage'):
            img = ExifTool._extract_single_tag(fp, tag)
            if img is not None:
                return img
        return None

    @staticmethod
    def _parse_coord(val):
        """解析坐标字符串为数值。
        含 S/W 半球字母时返回负值；Ref 字段缺失时符号由字母推断，不再静默丢负号"""
        if val is None: return None
        if isinstance(val, (int, float)): return float(val)
        s = str(val).strip()
        neg = bool(re.search(r'[SWsw]', s))
        nums = re.findall(r'[\d.]+', s)
        mag = None
        if len(nums) >= 3:
            try:
                mag = float(nums[0]) + float(nums[1]) / 60.0 + float(nums[2]) / 3600.0
            except Exception:
                mag = None
        elif len(nums) == 2:
            try:
                mag = float(nums[0]) + float(nums[1]) / 60.0
            except Exception:
                mag = None
        if mag is None and nums:
            try:
                mag = float(nums[0])
            except Exception:
                return None
        if mag is None:
            return None
        return -mag if neg else mag

    @staticmethod
    def parse_gps(exif):
        la = ExifTool._parse_coord(exif.get('GPSLatitude'))
        lo = ExifTool._parse_coord(exif.get('GPSLongitude'))
        if la is None or lo is None: return None, None
        # Ref 字段存在时以 Ref 为准（取绝对值再赋符号）；缺失时保留字母推断出的符号
        la_ref = str(exif.get('GPSLatitudeRef', '')).strip().upper()
        lo_ref = str(exif.get('GPSLongitudeRef', '')).strip().upper()
        if la_ref == 'S': la = -abs(la)
        elif la_ref == 'N': la = abs(la)
        if lo_ref == 'W': lo = -abs(lo)
        elif lo_ref == 'E': lo = abs(lo)
        if not (-90 <= la <= 90) or not (-180 <= lo <= 180): return None, None
        return lo, la

    @staticmethod
    def set_backup_dir(photo_dir):
        """设置备份目录为照片目录的**同级** exif_backup/（可见目录）。
        例：照片目录 /Users/xxx/Photos → 备份 /Users/xxx/exif_backup"""
        global BACKUP_DIR
        try:
            if not photo_dir:
                BACKUP_DIR = ""
                return
            parent = os.path.dirname(photo_dir.rstrip(os.sep))
            if not parent:  # 照片目录本身就是根/一级目录时，退回其内部
                parent = photo_dir
            BACKUP_DIR = os.path.join(parent, 'exif_backup')
        except Exception:
            BACKUP_DIR = ""

    @staticmethod
    def backup_file(fp):
        """写入前备份原文件到同级 exif_backup/ 目录，失败返回 None"""
        try:
            bak_dir = BACKUP_DIR or os.path.join(os.path.dirname(fp), 'exif_backup')
            os.makedirs(bak_dir, exist_ok=True)
            dst = os.path.join(bak_dir, os.path.basename(fp))
            if not os.path.exists(dst):
                shutil.copy2(fp, dst)
            return dst
        except Exception:
            return None

    @staticmethod
    def write_gps(fp, lng, lat):
        bak = ExifTool.backup_file(fp)
        if bak is None:
            return False, "原文件备份失败，已取消写入（请检查磁盘权限/空间）"
        _, e, rc = ExifTool._run([
            f'-GPSLatitude={abs(lat)}', f'-GPSLongitude={abs(lng)}',
            f'-GPSLatitudeRef={"N" if lat >= 0 else "S"}',
            f'-GPSLongitudeRef={"E" if lng >= 0 else "W"}',
            '-overwrite_original', fp
        ])
        return rc == 0, e

    @staticmethod
    def write_datetime(fp, dt):
        bak = ExifTool.backup_file(fp)
        if bak is None:
            return False, "原文件备份失败，已取消写入（请检查磁盘权限/空间）"
        _, e, rc = ExifTool._run([
            f'-DateTimeOriginal={dt}', f'-CreateDate={dt}', f'-ModifyDate={dt}',
            '-overwrite_original', fp
        ])
        return rc == 0, e


# ─────────────── 高德API ───────────────
class AmapAPI:
    @staticmethod
    def validate_key(key):
        try:
            d = requests.get("https://restapi.amap.com/v3/config/district",
                             params={'key': key, 'subdistrict': 0}, timeout=10).json()
            return (True, "Key 验证成功！") if d.get('status') == '1' else (False, f"失败:{d.get('info', '')}")
        except Exception as e:
            return False, f"网络错误:{e}"

    @staticmethod
    def reverse_geocode(lng, lat, key):
        if not key: return "未配置高德Key"
        try:
            d = requests.get("https://restapi.amap.com/v3/geocode/regeo",
                             params={'key': key, 'location': f'{lng:.6f},{lat:.6f}', 'radius': 100}, timeout=10).json()
            if d.get('status') == '1':
                a = d.get('regeocode', {}).get('formatted_address', '')
                return a if a else "未获取到地址"
            return f"失败:{d.get('info', '')}"
        except Exception as e:
            return f"异常:{e}"

    @staticmethod
    def geocode(addr, key):
        if not key: return None, None, "未配置Key"
        try:
            d = requests.get("https://restapi.amap.com/v3/geocode/geo",
                             params={'key': key, 'address': addr, 'output': 'JSON'}, timeout=10).json()
            if d.get('status') == '1' and d.get('geocodes'):
                loc = d['geocodes'][0].get('location', '')
                if ',' in loc:
                    lo, la = loc.split(',')
                    return float(lo), float(la), d['geocodes'][0].get('formatted_address', addr)
            return None, None, f"未找到:{addr}"
        except Exception as e:
            return None, None, f"异常:{e}"


# ─────────────── 配置 ───────────────
class ConfigManager:
    @staticmethod
    def load():
        global AMAP_KEY
        try:
            if os.path.exists(CONFIG_FILE):
                with open(CONFIG_FILE, 'r', encoding='utf-8') as f:
                    AMAP_KEY = json.load(f).get('amap_key', '')
        except Exception:
            AMAP_KEY = ""

    @staticmethod
    def save():
        try:
            with open(CONFIG_FILE, 'w', encoding='utf-8') as f:
                json.dump({'amap_key': AMAP_KEY}, f, ensure_ascii=False, indent=2)
        except Exception:
            pass


# ─────────────── 地图Canvas（异步瓦片渲染） ───────────────
class MapCanvas(tk.Canvas):
    def __init__(self, parent, width=500, height=400, click_cb=None, **kw):
        super().__init__(parent, width=width, height=height, bg='#e8e8e8', highlightthickness=0, **kw)
        self.mw, self.mh = width, height
        self.zoom = 12
        self.clng, self.clat = 116.397428, 39.90923
        self.click_cb = click_cb
        self.mkr_lng, self.mkr_lat = None, None
        self._imgs = []
        self._zid = None
        self._render_scheduled = False
        self.bind('<Configure>', self._on_resize)
        self._drag_data = {"x": 0, "y": 0, "moved": False}
        self.bind('<Button-1>', self._on_press)
        self.bind('<B1-Motion>', self._on_drag)
        self.bind('<ButtonRelease-1>', self._on_release)
        self.bind('<MouseWheel>', self._scroll)
        # Linux 滚轮事件
        self.bind('<Button-4>', lambda e: self._scroll_dir(1, e.x, e.y))
        self.bind('<Button-5>', lambda e: self._scroll_dir(-1, e.x, e.y))
        self.after(100, self.render)

    def _on_resize(self, event):
        if event.width > 1 and event.height > 1:
            self.mw = event.width
            self.mh = event.height
            self.render()

    def set_view(self, lng, lat, zoom=None, marker=True):
        self.clng, self.clat = lng, lat
        if zoom is not None and zoom != self.zoom:
            self.zoom = max(3, min(18, zoom))
            TileManager.clear_failed()  # 换缩放级别后允许重试之前失败的瓦片
        if marker:
            self.mkr_lng, self.mkr_lat = lng, lat
        else:
            self.mkr_lng, self.mkr_lat = None, None
        self.render()

    def clear_marker(self):
        self.mkr_lng, self.mkr_lat = None, None
        self.render()

    def render(self):
        self.delete("all")
        self._imgs.clear()
        cx, cy = TileManager.lnglat_to_pixel(self.clng, self.clat, self.zoom)
        sx, sy = cx - self.mw / 2, cy - self.mh / 2
        ts = TileManager.TS
        n = 2 ** self.zoom
        need_fetch = []
        for ty in range(max(0, int(sy // ts)), min(n, int((sy + self.mh) // ts) + 2)):
            for tx in range(int(sx // ts), int((sx + self.mw) // ts) + 2):
                wx = tx % n
                tile = TileManager.get_cached(wx, ty, self.zoom)
                px, py = tx * ts - sx, ty * ts - sy
                if tile:
                    ti = ImageTk.PhotoImage(tile)
                    self._imgs.append(ti)
                    self.create_image(px, py, image=ti, anchor='nw')
                else:
                    # 占位图，异步加载完成后防抖补绘
                    self.create_rectangle(px, py, px + ts, py + ts,
                                          fill='#e4e8ec', outline='#d5dade', width=1)
                    need_fetch.append((wx, ty, self.zoom))
        for key in need_fetch:
            TileManager.fetch_async(key, self._on_tile_ready)
        if self.mkr_lng is not None and self.mkr_lat is not None:
            px, py = self._to_canvas(self.mkr_lng, self.mkr_lat)
            r = 8
            self.create_oval(px - r, py - r, px + r, py + r, fill='red', outline='white', width=2, tags="mkr")
            self.create_line(px, py + r, px, py + r + 12, fill='red', width=2, tags="mkr")
            emoji_font = ('Segoe UI Emoji', 14) if IS_WIN else ('Apple Color Emoji', 14)
            self.create_text(px, py - r - 6, text="📍", font=emoji_font, tags="mkr")
        self._draw_hint()

    def _on_tile_ready(self, key):
        """瓦片下载完成回调：仅当级别仍匹配时，防抖触发一次补绘"""
        if key[2] != self.zoom:
            return
        if not self._render_scheduled:
            self._render_scheduled = True
            self.after(80, self._deferred_render)

    def _deferred_render(self):
        self._render_scheduled = False
        self.render()

    def _draw_hint(self):
        hint_text = "💡 左键点击选点 | 左键拖拽平移 | 滚轮缩放"
        font = StyleAdapter.get_font(9)
        bbox = self.create_text(0, 0, text=hint_text, font=font, anchor='nw')
        bx1, by1, bx2, by2 = self.bbox(bbox)
        tw, th = bx2 - bx1, by2 - by1
        self.delete(bbox)
        pad_x, pad_y = 8, 4
        x2 = self.mw - 10
        y2 = self.mh - 10
        x1 = x2 - tw - pad_x * 2
        y1 = y2 - th - pad_y * 2
        self.create_rectangle(x1, y1, x2, y2, fill='#ffffff', outline='#cccccc', width=1, stipple='gray50',
                              tags="hint_bg")
        self.create_text(x2 - pad_x, y2 - pad_y, anchor='se',
                         text=hint_text, fill='#333333', font=font, tags="hint_text")

    def _to_canvas(self, lng, lat):
        px, py = TileManager.lnglat_to_pixel(lng, lat, self.zoom)
        cx, cy = TileManager.lnglat_to_pixel(self.clng, self.clat, self.zoom)
        return px - cx + self.mw / 2, py - cy + self.mh / 2

    def _from_canvas(self, cx, cy):
        cpx, cpy = TileManager.lnglat_to_pixel(self.clng, self.clat, self.zoom)
        return TileManager.pixel_to_lnglat(cpx + (cx - self.mw / 2), cpy + (cy - self.mh / 2), self.zoom)

    def _on_press(self, e):
        self._drag_data = {"x": e.x, "y": e.y, "moved": False}

    def _on_drag(self, e):
        dx = e.x - self._drag_data["x"]
        dy = e.y - self._drag_data["y"]
        if abs(dx) > 5 or abs(dy) > 5:
            self._drag_data["moved"] = True
        if self._drag_data["moved"]:
            cx, cy = TileManager.lnglat_to_pixel(self.clng, self.clat, self.zoom)
            self.clng, self.clat = TileManager.pixel_to_lnglat(cx - dx, cy - dy, self.zoom)
            self._drag_data["x"] = e.x
            self._drag_data["y"] = e.y
            self.render()

    def _on_release(self, e):
        if not self._drag_data["moved"]:
            lng, lat = self._from_canvas(e.x, e.y)
            self.set_view(lng, lat, marker=True)
            if self.click_cb:
                self.click_cb(lng, lat)

    def _scroll(self, e):
        d = 1 if e.delta > 0 else -1
        self._zoom_debounced(d, e.x, e.y)

    def _scroll_dir(self, d, x, y):
        self._zoom_debounced(d, x, y)

    def _zoom_debounced(self, d, x, y):
        if self._zid: self.after_cancel(self._zid)
        self._zid = self.after(50, lambda: self._zoom_at(d, x, y))

    def _zoom_at(self, d, mx, my):
        nz = self.zoom + d
        if nz < 3 or nz > 18: return
        lng, lat = self._from_canvas(mx, my)
        self.zoom = nz
        TileManager.clear_failed()
        ncx, ncy = TileManager.lnglat_to_pixel(lng, lat, self.zoom)
        ox, oy = mx - self.mw / 2, my - self.mh / 2
        self.clng, self.clat = TileManager.pixel_to_lnglat(ncx - ox, ncy - oy, self.zoom)
        self.render()


# ─────────────── 主应用 ───────────────
class PhotoGPSApp:
    def __init__(self, root):
        self.root = root
        self.root.title("📷 照片 GPS 坐标管理工具")
        self.root.geometry("1200x800")
        self.root.minsize(1000, 650)
        ConfigManager.load()
        self.cur_dir = ""
        self.files = []
        self.cur_file = None
        self.cur_exif = {}
        self.wgs_lng = None
        self.wgs_lat = None
        self.pgcj_lng = None
        self.pgcj_lat = None
        self._addr_seq = {}  # 各地址标签的请求序号，用于丢弃过期反查结果
        self.style = ttk.Style()
        StyleAdapter.apply_styles(self.style)
        self._ui()
        self._key_status()

    def _log(self, msg):
        try:
            self.lbl_st.config(text=f" {msg}")
        except Exception:
            pass

    def _ui(self):
        BG = '#f0f0f0'
        TITLE_FG = '#333333'
        TITLE_FONT = StyleAdapter.get_font(11, bold=True)
        self.root.configure(bg=BG)

        tb = tk.Frame(self.root, bg=BG, padx=5, pady=5)
        tb.pack(side='top', fill='x')
        ttk.Button(tb, text="📂 选择目录", style='Toolbar.TButton', command=self._sel_dir).pack(side='left', padx=(0, 5))
        self.lbl_dir = tk.Label(tb, text=" 未选择目录", bg='#fff', fg='#333', relief='solid', borderwidth=1, anchor='w',
                                padx=5, pady=2, font=StyleAdapter.get_font(10))
        self.lbl_dir.pack(side='left', fill='x', expand=True, padx=(0, 5))
        ttk.Button(tb, text="🔑 设置Key", style='Toolbar.TButton', command=self._key_dlg).pack(side='left', padx=(0, 5))
        self.lbl_key = ttk.Label(tb, text="", style='KeyMissing.TLabel')
        self.lbl_key.pack(side='left', padx=(0, 10))
        ttk.Button(tb, text="❌ 退出", style='Toolbar.TButton', command=self.root.quit).pack(side='right')

        body = tk.Frame(self.root, bg=BG)
        body.pack(fill='both', expand=True, padx=5, pady=(0, 5))

        left = tk.Frame(body, bg=BG, width=240)
        left.pack(side='left', fill='y', padx=(0, 1))
        left.pack_propagate(False)
        tk.Label(left, text="📁 照片列表", bg=BG, fg=TITLE_FG, font=TITLE_FONT, anchor='w').pack(fill='x', pady=(0, 3))
        self.tree = ttk.Treeview(left, show='tree', selectmode='browse')
        self.tree.heading('#0', text='文件名', anchor='w')
        self.tree.column('#0', width=220, minwidth=160, anchor='w')
        fsb = ttk.Scrollbar(left, orient='vertical', command=self.tree.yview)
        self.tree.configure(yscrollcommand=fsb.set)
        self.tree.pack(side='left', fill='both', expand=True)
        fsb.pack(side='right', fill='y')
        self.tree.bind('<<TreeviewSelect>>', self._on_sel)

        tk.Frame(body, bg='#ccc', width=1).pack(side='left', fill='y')

        right = tk.Frame(body, bg=BG)
        right.pack(side='left', fill='both', expand=True, padx=(1, 0))
        right.grid_columnconfigure(0, weight=1, minsize=200)
        right.grid_columnconfigure(1, weight=2, minsize=240)
        right.grid_rowconfigure(0, weight=1)
        right.grid_rowconfigure(1, weight=0)
        right.grid_rowconfigure(2, weight=0)
        right.grid_rowconfigure(3, weight=2)

        info_area = tk.Frame(right, bg=BG)
        info_area.grid(row=0, column=0, columnspan=2, sticky='nsew', pady=(0, 3))
        info_area.grid_columnconfigure(0, weight=1, minsize=180)
        info_area.grid_columnconfigure(1, weight=2, minsize=220)
        info_area.grid_rowconfigure(1, weight=1)

        tk.Label(info_area, text="📋 照片信息", bg=BG, fg=TITLE_FG, font=TITLE_FONT).grid(
            row=0, column=0, columnspan=2, sticky='w', pady=(0, 3))

        tf = tk.Frame(info_area, bg=BG)
        tf.grid(row=1, column=0, sticky='nsew', padx=(0, 5))
        self.thumb = tk.Label(tf, text="未选择照片", bg='#e0e0e0', fg='#666', relief='solid', borderwidth=1,
                              font=StyleAdapter.get_font(10))
        self.thumb.pack(fill='both', expand=True)

        ef = tk.Frame(info_area, bg=BG)
        ef.grid(row=1, column=1, sticky='nsew')
        self.exif = tk.Text(ef, wrap='word', font=StyleAdapter.get_font(9), bg='#f8f8f8', fg='#333333',
                            relief='solid', borderwidth=1, highlightthickness=0, padx=8, pady=8, width=30)
        esb = ttk.Scrollbar(ef, orient='vertical', command=self.exif.yview)
        self.exif.configure(yscrollcommand=esb.set)
        self.exif.pack(side='left', fill='both', expand=True)
        esb.pack(side='right', fill='y')

        cf = tk.Frame(right, bg=BG)
        cf.grid(row=1, column=0, columnspan=2, sticky='ew', pady=(3, 3))
        self.lbl_wgs = ttk.Label(cf, text="GPS(WGS-84): --", style='Info.TLabel')
        self.lbl_wgs.pack(anchor='w')
        self.lbl_gcj = ttk.Label(cf, text="高德(GCJ-02): --", style='Info.TLabel')
        self.lbl_gcj.pack(anchor='w')
        self.lbl_addr = ttk.Label(cf, text="地址: --", wraplength=700, font=StyleAdapter.get_font(10))
        self.lbl_addr.pack(anchor='w')

        tk.Frame(right, bg='#ccc', height=1).grid(row=2, column=0, columnspan=2, sticky='ew', pady=0)

        ma = tk.Frame(right, bg=BG)
        ma.grid(row=3, column=0, columnspan=2, sticky='nsew', pady=(3, 0))
        ma.grid_columnconfigure(0, weight=1)
        ma.grid_columnconfigure(1, weight=0)
        ma.grid_rowconfigure(1, weight=1)

        tk.Label(ma, text="🗺️ 高德地图", bg=BG, fg=TITLE_FG, font=TITLE_FONT).grid(
            row=0, column=0, columnspan=2, sticky='w', pady=(0, 3))

        self.mc = MapCanvas(ma, width=500, height=350, click_cb=self._map_click)
        self.mc.grid(row=1, column=0, sticky='nsew', padx=(0, 8))

        act = tk.Frame(ma, bg=BG)
        act.grid(row=1, column=1, sticky='ns')

        tk.Label(act, text="🔍 地址搜索", bg=BG, fg=TITLE_FG, font=TITLE_FONT).pack(anchor='w', pady=(0, 3))
        sf = tk.Frame(act, bg=BG)
        sf.pack(fill='x', pady=(0, 5))
        self.e_search = ttk.Entry(sf, width=20, font=StyleAdapter.get_font(10))
        self.e_search.pack(side='left', fill='x', expand=True, padx=(0, 3))
        self.e_search.bind('<Return>', lambda e: self._search())
        ttk.Button(sf, text="搜索", style='Compact.TButton', command=self._search).pack(side='right')
        self.lbl_sr = tk.Label(act, text="", bg=BG, fg='#666', anchor='w', wraplength=280, justify='left',
                               font=StyleAdapter.get_font(9))
        self.lbl_sr.pack(anchor='w', pady=(0, 5))
        ttk.Separator(act, orient='horizontal').pack(fill='x', pady=3)

        tk.Label(act, text="🎯 选取坐标", bg=BG, fg=TITLE_FG, font=TITLE_FONT).pack(anchor='w', pady=(3, 3))
        self.lbl_pgcj = ttk.Label(act, text="高德: --", style='Info.TLabel', wraplength=280)
        self.lbl_pgcj.pack(anchor='w')
        self.lbl_pwgs = ttk.Label(act, text="GPS: --", style='Info.TLabel', wraplength=280)
        self.lbl_pwgs.pack(anchor='w')
        self.lbl_paddr = ttk.Label(act, text="地址: --", wraplength=280, font=StyleAdapter.get_font(10))
        self.lbl_paddr.pack(anchor='w', pady=(0, 5))
        ttk.Separator(act, orient='horizontal').pack(fill='x', pady=3)
        self.btn_gps = ttk.Button(act, text="💾 保存GPS", style='Action.TButton', command=self._save_gps,
                                  state='disabled')
        self.btn_gps.pack(fill='x', pady=3)
        ttk.Separator(act, orient='horizontal').pack(fill='x', pady=8)

        tk.Label(act, text="📅 添加拍摄日期", bg=BG, fg=TITLE_FG, font=TITLE_FONT).pack(anchor='w', pady=(0, 2))
        df = tk.Frame(act, bg=BG)
        df.pack(fill='x', pady=5)
        tk.Label(df, text="日期:", bg=BG, fg=TITLE_FG, font=StyleAdapter.get_font(10)).pack(side='left')
        self.e_date = ttk.Entry(df, width=20, font=StyleAdapter.get_font(10))
        self.e_date.pack(side='left', padx=5, fill='x', expand=True)
        self.e_date.insert(0, datetime.now().strftime("%Y:%m:%d %H:%M:%S"))
        self.btn_dt = ttk.Button(act, text="📝 写入日期", style='Action.TButton', command=self._write_dt,
                                 state='disabled')
        self.btn_dt.pack(fill='x', pady=3)

        sb = tk.Frame(self.root, bg='#e0e0e0', height=28)
        sb.pack(side='bottom', fill='x')
        self.lbl_st = tk.Label(sb, text=" 就绪 | 请选择目录并配置Key", bg='#e0e0e0', fg='#333', anchor='w',
                               font=StyleAdapter.get_font(9))
        self.lbl_st.pack(side='left', fill='x', expand=True, padx=5, pady=2)

    def _search(self):
        a = self.e_search.get().strip()
        if not a: return
        if not AMAP_KEY:
            self.lbl_sr.config(text="⚠️ 请先配置Key", fg='red');
            return
        self.lbl_sr.config(text="⏳ 搜索中...", fg='blue')

        def _d():
            lo, la, r = AmapAPI.geocode(a, AMAP_KEY)

            def _u():
                if lo:
                    self.lbl_sr.config(text=f"✅ {r}", fg='green')
                    self.mc.set_view(lo, la, zoom=16, marker=True)
                    self._map_click(lo, la)
                else:
                    self.lbl_sr.config(text=f"❌ {r}", fg='red')

            self.root.after(0, _u)

        threading.Thread(target=_d, daemon=True).start()

    def _sel_dir(self):
        d = filedialog.askdirectory(title="选择照片目录")
        if not d: return
        self.cur_dir = d
        self.lbl_dir.config(text=f" {d}")
        ExifTool.set_backup_dir(d)  # 备份目录 = 照片目录同级的 exif_backup/
        self._scan()

    def _scan(self):
        self.tree.delete(*self.tree.get_children())
        self.files = []
        if not self.cur_dir: return
        for fn in sorted(os.listdir(self.cur_dir)):
            if os.path.splitext(fn)[1].lower() in SUPPORTED_EXTENSIONS:
                fp = os.path.join(self.cur_dir, fn)
                self.files.append(fp)
                self.tree.insert('', 'end', text=f" {fn}", iid=fp)
        bak = BACKUP_DIR or "(未设置)"
        self.lbl_st.config(text=f" 已加载 {len(self.files)} 个文件 | 备份目录: {bak}")

    def _on_sel(self, e):
        s = self.tree.selection()
        if s: self._load(s[0])

    def _load(self, fp):
        self.cur_file = fp
        self.pgcj_lng = self.pgcj_lat = None
        self._thumb(fp)
        self.cur_exif = ExifTool.read_exif(fp)
        self._exif_show()
        lo, la = ExifTool.parse_gps(self.cur_exif)
        self.wgs_lng, self.wgs_lat = lo, la

        if lo is not None and la is not None:
            gl, ga = CoordTransform.wgs84_to_gcj02(lo, la)
            self.lbl_wgs.config(text=f"GPS(WGS-84): 经度{lo:.6f} 纬度{la:.6f}")
            self.lbl_gcj.config(text=f"高德(GCJ-02): 经度{gl:.6f} 纬度{ga:.6f}")
            self.mc.set_view(gl, ga, zoom=16, marker=True)
            if CoordTransform._out_of_china(lo, la):
                self._addr_async(lo, la, self.lbl_addr)
            else:
                self._addr_async(gl, ga, self.lbl_addr)
        else:
            self.lbl_wgs.config(text="GPS(WGS-84): 无GPS信息")
            self.lbl_gcj.config(text="高德(GCJ-02): --")
            self.lbl_addr.config(text="地址: --")
            self.mc.clear_marker()

        self.lbl_pgcj.config(text="高德: --")
        self.lbl_pwgs.config(text="GPS: --")
        self.lbl_paddr.config(text="地址: --")
        self.btn_gps.config(state='normal')
        self.btn_dt.config(state='normal')

    def _apply_orientation(self, img):
        """处理图片EXIF旋转标记"""
        try:
            ed = img._getexif()
            if ed:
                for t, v in ed.items():
                    if ExifTags.TAGS.get(t) == 'Orientation':
                        if v == 3:
                            img = img.rotate(180, expand=True)
                        elif v == 6:
                            img = img.rotate(270, expand=True)
                        elif v == 8:
                            img = img.rotate(90, expand=True)
                        break
        except Exception:
            pass
        return img

    def _set_thumb_image(self, img):
        """统一设置缩略图到界面"""
        if img.mode not in ('RGB', 'RGBA'):
            img = img.convert('RGB')
        img = self._apply_orientation(img)
        img.thumbnail((280, 280), Image.LANCZOS)
        photo = ImageTk.PhotoImage(img)
        self.thumb.config(image=photo, text="", bg='#ffffff')
        self.thumb.image = photo

    def _thumb(self, fp):
        ext = os.path.splitext(fp)[1].lower()

        # RAW格式优先使用ExifTool提取嵌入缩略图
        if ext in RAW_EXTENSIONS:
            raw_img = ExifTool.extract_thumbnail(fp)
            if raw_img:
                self._set_thumb_image(raw_img)
                return

        # Pillow常规读取（JPG/PNG/HEIC/WebP等）
        try:
            img = Image.open(fp)
            self._set_thumb_image(img)
        except Exception as e:
            # Pillow失败时，尝试ExifTool兜底（适用于部分特殊编码JPG/TIFF）
            fallback_img = ExifTool.extract_thumbnail(fp)
            if fallback_img:
                self._set_thumb_image(fallback_img)
                return

            err_msg = f"{type(e).__name__}: {str(e)[:80]}"
            hint = "需要: pip install pillow-heif" if 'heic' in fp.lower() else ""
            self.thumb.config(image='', text=f"缩略图加载失败\n{err_msg}\n{hint}", bg='#ffe0e0', fg='#c00')
            self._log(f"⚠️ 缩略图加载失败: {os.path.basename(fp)} - {err_msg}")

    def _exif_show(self):
        ex = self.cur_exif
        self.exif.config(state='normal')
        self.exif.delete('1.0', 'end')
        fn = os.path.basename(self.cur_file) if self.cur_file else ""
        ls = [
            f"═══ 文件 ═══", f"文件名: {fn}", f"路径: {self.cur_file or '--'}",
            f"尺寸: {ex.get('ImageWidth', '?')} × {ex.get('ImageHeight', '?')}", "",
            f"═══ 拍摄 ═══", f"日期: {ex.get('DateTimeOriginal', ex.get('CreateDate', ex.get('ModifyDate', '无')))}",
            "",
            f"═══ 设备 ═══", f"厂商: {ex.get('Make', '未知')}", f"型号: {ex.get('Model', '未知')}",
            f"镜头: {ex.get('LensModel', ex.get('LensInfo', '未知'))}", "",
            f"═══ 参数 ═══", f"焦距: {ex.get('FocalLength', '?')}", f"光圈: f/{ex.get('FNumber', '?')}",
            f"快门: {ex.get('ExposureTime', '?')}", f"ISO: {ex.get('ISO', '?')}", "", f"═══ GPS ═══"
        ]
        la = ex.get('GPSLatitude', '无')
        if la != '无':
            ls.extend([
                f"纬度: {la} {ex.get('GPSLatitudeRef', '')}",
                f"经度: {ex.get('GPSLongitude', '无')} {ex.get('GPSLongitudeRef', '')}"
            ])
        else:
            ls.append("无GPS坐标")
        self.exif.insert('1.0', '\n'.join(ls))
        self.exif.config(state='disabled')

    def _map_click(self, lng, lat):
        self.pgcj_lng, self.pgcj_lat = lng, lat
        wl, wla = CoordTransform.gcj02_to_wgs84(lng, lat)
        self.lbl_pgcj.config(text=f"高德: {lng:.6f},{lat:.6f}")
        self.lbl_pwgs.config(text=f"GPS: {wl:.6f},{wla:.6f}")
        self._addr_async(lng, lat, self.lbl_paddr)

    def _addr_async(self, gl, ga, w):
        w.config(text="地址: 获取中...")
        # 请求序号校验：只接受每个标签最新一次请求的结果，快速切换照片/选点时丢弃过期响应
        token = str(id(w))
        self._addr_seq[token] = self._addr_seq.get(token, 0) + 1
        seq = self._addr_seq[token]

        def _f():
            a = AmapAPI.reverse_geocode(gl, ga, AMAP_KEY)

            def _u():
                if self._addr_seq.get(token) != seq:
                    return  # 结果已过期，丢弃
                w.config(text=f"地址: {a}")

            self.root.after(0, _u)

        threading.Thread(target=_f, daemon=True).start()

    def _save_gps(self):
        if not self.cur_file: return messagebox.showwarning("提示", "请先选择照片")
        if self.pgcj_lng is None: return messagebox.showwarning("提示", "请先选取坐标")
        wl, wla = CoordTransform.gcj02_to_wgs84(self.pgcj_lng, self.pgcj_lat)
        bak = BACKUP_DIR or os.path.join(os.path.dirname(self.cur_file), 'exif_backup')
        if not messagebox.askyesno("确认",
                                   f"写入GPS:\n{os.path.basename(self.cur_file)}\n"
                                   f"WGS-84:{wl:.6f},{wla:.6f}\n"
                                   f"(写入前自动备份原文件到:\n{bak})\n继续？"): return
        ok, err = ExifTool.write_gps(self.cur_file, wl, wla)
        if ok:
            messagebox.showinfo("成功", "GPS已写入！")
            self.lbl_st.config(text=f" ✅ GPS已写入:{os.path.basename(self.cur_file)}")
            self._load(self.cur_file)
        else:
            messagebox.showerror("失败", err)

    def _write_dt(self):
        if not self.cur_file: return messagebox.showwarning("提示", "请先选择照片")
        ds = self.e_date.get().strip()
        if not re.match(r'^\d{4}[:\-/]\d{2}[:\-/]\d{2}\s+\d{2}:\d{2}:\d{2}$', ds):
            return messagebox.showwarning("格式错误", "请使用 YYYY:MM:DD HH:MM:SS")
        ds = re.sub(r'[\-/]', ':', ds[:10]) + ds[10:]
        bak = BACKUP_DIR or os.path.join(os.path.dirname(self.cur_file), 'exif_backup')
        if not messagebox.askyesno("确认", f"写入日期:\n{os.path.basename(self.cur_file)}\n{ds}\n"
                                          f"(写入前自动备份原文件到:\n{bak})\n继续？"): return
        ok, err = ExifTool.write_datetime(self.cur_file, ds)
        if ok:
            messagebox.showinfo("成功", f"日期已写入！\n{ds}")
            self.lbl_st.config(text=f" ✅ 日期已写入:{os.path.basename(self.cur_file)}")
            self._load(self.cur_file)
        else:
            messagebox.showerror("失败", err)

    def _key_dlg(self):
        dlg = tk.Toplevel(self.root)
        dlg.title("🔑 设置高德Key")
        dlg.geometry("480x200")
        dlg.resizable(False, False)
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.update_idletasks()
        x = self.root.winfo_x() + (self.root.winfo_width() - 480) // 2
        y = self.root.winfo_y() + (self.root.winfo_height() - 200) // 2
        dlg.geometry(f"+{x}+{y}")
        f = ttk.Frame(dlg, padding=20)
        f.pack(fill='both', expand=True)
        ttk.Label(f, text="请输入高德Web服务API Key:", font=StyleAdapter.get_font(11)).pack(anchor='w')
        ttk.Label(f, text="https://lbs.amap.com 申请", foreground='gray', font=StyleAdapter.get_font(9)).pack(
            anchor='w', pady=(0, 10))
        kv = tk.StringVar(value=AMAP_KEY)
        ttk.Entry(f, textvariable=kv, width=50, font=StyleAdapter.get_font(10)).pack(fill='x', pady=(0, 10))
        sl = ttk.Label(f, text="", font=StyleAdapter.get_font(10))
        sl.pack(anchor='w')
        bf = ttk.Frame(f)
        bf.pack(fill='x', pady=(10, 0))

        def _vs():
            k = kv.get().strip()
            if not k: return sl.config(text="⚠️ 请输入Key", foreground='orange')
            sl.config(text="⏳ 验证中...", foreground='blue')
            dlg.update()
            ok, msg = AmapAPI.validate_key(k)
            if ok:
                global AMAP_KEY
                AMAP_KEY = k
                ConfigManager.save()
                sl.config(text=f"✅ {msg} 已保存！", foreground='green')
                self._key_status()
                dlg.after(1500, dlg.destroy)
            else:
                sl.config(text=f"❌ {msg}", foreground='red')

        ttk.Button(bf, text="✅ 验证并保存", command=_vs).pack(side='left', padx=(0, 10))
        ttk.Button(bf, text="关闭", command=dlg.destroy).pack(side='right')

    def _key_status(self):
        if AMAP_KEY:
            m = AMAP_KEY[:6] + '****' + AMAP_KEY[-4:] if len(AMAP_KEY) > 10 else '****'
            self.lbl_key.config(text=f"✅ Key:{m}", style='KeyOK.TLabel')
        else:
            self.lbl_key.config(text="⚠️ 未配置Key", style='KeyMissing.TLabel')


def main():
    root = tk.Tk()
    if IS_WIN:
        try:
            from ctypes import windll
            windll.shcore.SetProcessDpiAwareness(2)
        except Exception:
            try:
                windll.shcore.SetProcessDpiAwareness(1)
            except Exception:
                pass
    else:
        # 按系统真实 DPI 计算 scaling，替代硬编码 2.0（72pt = 1 英寸）
        try:
            root.update_idletasks()
            dpi = root.winfo_fpixels('1i')
            if dpi and dpi > 0:
                root.tk.call('tk', 'scaling', dpi / 72.0)
        except Exception:
            pass
    PhotoGPSApp(root)
    root.mainloop()


if __name__ == '__main__':
    main()
