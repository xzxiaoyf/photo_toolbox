#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
android_photo_exporter.py — Android 手机照片/视频批量导出到电脑工具
====================================================================

通过 adb（Android 调试桥）读取手机上分散在多个目录的媒体文件
（相册、微信、QQ、视频监控下载等），增量拷贝到电脑指定目录。

跨平台：macOS / Windows 均可运行（依赖 adb 可执行文件）。

依赖：
  - adb：macOS   brew install android-platform-tools
         Windows 下载 Google platform-tools 解压，或将 adb.exe 加入 PATH
  - exiftool（可选）：按拍摄日期归档时读取 EXIF；缺失时回退文件 mtime

手机端准备：
  1. 设置 → 关于手机 → 连点「版本号」7 次开启开发者选项
  2. 开发者选项 → 打开「USB 调试」
  3. USB 连接电脑，弹窗点「允许 USB 调试」

目录说明：
  - 常见媒体目录已预置为可勾选清单（DCIM/Pictures/Movies/Download/
    微信/QQ 等），也可自定义添加。
  - 注意：Android 11+ 部分机型限制电脑访问 /sdcard/Android/data/，
    微信/QQ 新版目录若读取失败，日志会标注，可先在手机文件管理器
    中把需要的文件复制到普通目录（如 /sdcard/Download）再导出。

GUI 模式：   python3 android_photo_exporter.py
命令行模式： python3 android_photo_exporter.py --dest /path --mode by-date
"""

import os
import re
import shutil
import subprocess
import sys
import threading
import uuid
import warnings
from datetime import datetime

# 屏蔽第三方依赖版本不匹配的无害警告（如 requests vs chardet/urllib3）
warnings.filterwarnings("ignore", message=".*doesn't match a supported version.*")

# ---------------------------------------------------------------------------
# 常量
# ---------------------------------------------------------------------------
ADB_EXTRA_PATHS = [
    # macOS 常见
    "/opt/homebrew/bin", "/usr/local/bin",
    os.path.expanduser("~/Library/Android/sdk/platform-tools"),
    # Windows 常见
    os.path.expandvars(r"%LOCALAPPDATA%\Android\Sdk\platform-tools"),
    os.path.expandvars(r"%USERPROFILE%\AppData\Local\Android\Sdk\platform-tools"),
    r"C:\platform-tools",
]

PHOTO_EXTS = {".jpg", ".jpeg", ".png", ".gif", ".webp", ".bmp", ".heic",
              ".heif", ".dng", ".tif", ".tiff"}
VIDEO_EXTS = {".mp4", ".mov", ".avi", ".mkv", ".3gp", ".ts", ".flv", ".webm",
              ".m4v"}
DOC_EXTS = {".pdf", ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx",
            ".txt", ".csv", ".rtf", ".odt", ".ods", ".odp", ".md",
            ".epub", ".zip", ".rar", ".7z"}

# 预置目录清单（说明, 远程路径）
DEFAULT_DIRS = [
    ("相机照片/视频 (DCIM)", "/sdcard/DCIM"),
    ("截图与保存的图片 (Pictures)", "/sdcard/Pictures"),
    ("视频 (Movies)", "/sdcard/Movies"),
    ("下载 (Download)", "/sdcard/Download"),
    ("微信 (老版/导出目录)", "/sdcard/tencent/MicroMsg"),
    ("微信 (新版, Android11+ 可能受限)", "/sdcard/Android/data/com.tencent.mm"),
    ("QQ (新版, Android11+ 可能受限)", "/sdcard/Android/data/com.tencent.mobileqq"),
    ("QQ/微信文件 (tencent)", "/sdcard/tencent/QQfile_recv"),
]


# ---------------------------------------------------------------------------
# 基础工具
# ---------------------------------------------------------------------------
def find_adb() -> str | None:
    found = shutil.which("adb")
    if found:
        return found
    for p in ADB_EXTRA_PATHS:
        adb = os.path.join(p, "adb.exe" if sys.platform == "win32" else "adb")
        if os.path.isfile(adb) and os.access(adb, os.X_OK):
            return adb
    return None


def run_cmd(args: list[str], timeout: int = 60) -> tuple[int, str]:
    try:
        proc = subprocess.run(args, capture_output=True, text=True,
                              timeout=timeout, errors="replace")
        return proc.returncode, ((proc.stdout or "") + (proc.stderr or "")).strip()
    except FileNotFoundError:
        return 127, f"命令不存在: {args[0]}"
    except subprocess.TimeoutExpired:
        return 124, f"命令超时: {' '.join(args[:6])}…"


def human_size(n: float) -> str:
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if abs(n) < 1024 or unit == "TB":
            return f"{n:.1f}{unit}" if unit != "B" else f"{int(n)}B"
        n /= 1024.0


class FileLogger:
    """线程安全的文件日志：追加写入，每行带时间戳。"""

    def __init__(self, path: str):
        self.path = path
        self._lock = threading.Lock()
        self._fh = open(path, "a", encoding="utf-8")

    def write(self, msg: str):
        line = f"[{datetime.now():%Y-%m-%d %H:%M:%S}] {msg}\n"
        with self._lock:
            try:
                self._fh.write(line)
                self._fh.flush()
            except Exception:
                pass

    def close(self):
        with self._lock:
            try:
                self._fh.close()
            except Exception:
                pass


def log_path_in(dest_dir: str) -> str:
    """目标目录下当天的日志文件路径：YYYY-MM-DD_log.txt"""
    return os.path.join(dest_dir, f"{datetime.now():%Y-%m-%d}_log.txt")


# ---------------------------------------------------------------------------
# 设备检测
# ---------------------------------------------------------------------------
def list_devices(adb: str) -> list[tuple[str, str]]:
    """返回 [(serial, 状态), ...]，仅含 device/unauthorized 状态。"""
    rc, out = run_cmd([adb, "devices"])
    if rc != 0:
        return []
    devices = []
    for line in out.splitlines()[1:]:
        line = line.strip()
        if not line or line.startswith("*"):
            continue
        parts = line.split()
        if len(parts) >= 2:
            devices.append((parts[0], parts[1]))
    return devices


def device_model(adb: str, serial: str) -> str:
    rc, out = run_cmd([adb, "-s", serial, "shell",
                       "getprop ro.product.model"], timeout=10)
    return out.strip() if rc == 0 and out.strip() else serial


# ---------------------------------------------------------------------------
# 远程文件枚举
# ---------------------------------------------------------------------------
def _sh_quote(path: str) -> str:
    return "'" + path.replace("'", "'\\''") + "'"


def remote_list_files(adb: str, serial: str, dirs: list[str],
                      log=print) -> list[str]:
    """在手机上 find 指定目录，返回文件路径列表。"""
    if not dirs:
        return []
    quoted = " ".join(_sh_quote(d) for d in dirs)
    rc, out = run_cmd(
        [adb, "-s", serial, "shell",
         f"find {quoted} -type f 2>/dev/null"],
        timeout=120)
    if rc not in (0, 1):  # find 对个别无权限目录返回非 0 也算部分成功
        log(f"⚠ 目录枚举返回码 {rc}，结果可能不完整")
    files = []
    for line in out.splitlines():
        line = line.strip().replace("\r", "")
        if line and not line.startswith("find:"):
            files.append(line)
    return files


def remote_sizes(adb: str, serial: str, files: list[str],
                 chunk: int = 50) -> dict[str, int]:
    """分批 stat 获取远程文件大小，失败的文件无大小记录。"""
    sizes = {}
    for i in range(0, len(files), chunk):
        batch = files[i:i + chunk]
        quoted = " ".join(_sh_quote(f) for f in batch)
        rc, out = run_cmd(
            [adb, "-s", serial, "shell",
             f"stat -c '%s %n' {quoted} 2>/dev/null"],
            timeout=60)
        if rc != 0:
            continue
        for line in out.splitlines():
            line = line.strip().replace("\r", "")
            m = re.match(r"^(\d+)\s(.+)$", line)
            if m:
                sizes[m.group(2)] = int(m.group(1))
    return sizes


def remote_pull(adb: str, serial: str, remote: str, local: str) -> None:
    rc, out = run_cmd([adb, "-s", serial, "pull", "-a", remote, local],
                      timeout=1800)
    if rc != 0 or not os.path.isfile(local):
        raise RuntimeError(out.strip() or "adb pull 失败")


# ---------------------------------------------------------------------------
# 拍摄日期
# ---------------------------------------------------------------------------
def shot_date(local_path: str, use_exif: bool) -> datetime:
    if use_exif:
        exiftool = shutil.which("exiftool")
        if exiftool:
            rc, out = run_cmd(
                [exiftool, "-s3", "-d", "%Y-%m-%d", "-DateTimeOriginal",
                 "-T", "-n", local_path], timeout=15)
            if rc == 0:
                for part in (out.splitlines()[0] if out else "").split():
                    try:
                        return datetime.strptime(part, "%Y-%m-%d")
                    except ValueError:
                        continue
    try:
        return datetime.fromtimestamp(os.path.getmtime(local_path))
    except OSError:
        return datetime.now()


# ---------------------------------------------------------------------------
# 导出核心
# ---------------------------------------------------------------------------
class ExportStats:
    def __init__(self):
        self.total = 0
        self.copied = 0
        self.skipped = 0
        self.failed = 0
        self.bytes_copied = 0


def _finalize(tmp: str, origin: str, dest_root: str, mode: str, use_exif: bool,
              stats, log) -> None:
    """临时文件 → 最终位置（含日期归档与二次去重）。origin 为来源显示名。"""
    name = origin.rsplit("/", 1)[-1]
    if mode == "by-date":
        d = shot_date(tmp, use_exif)
        dst = os.path.join(dest_root, d.strftime("%Y-%m-%d"), name)
    else:
        dst = os.path.join(dest_root, name)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    if os.path.exists(dst):
        try:
            if os.path.getsize(dst) == os.path.getsize(tmp):
                stats.skipped += 1
                return
        except OSError:
            pass
    os.replace(tmp, dst)
    stats.copied += 1
    stats.bytes_copied += os.path.getsize(dst)
    log(f"✔ {origin} -> {os.path.relpath(dst, dest_root)} "
        f"({human_size(os.path.getsize(dst))})")


def run_export(adb: str, serial: str, dirs: list[str], dest_root: str,
               mode: str = "flat", use_exif: bool = True,
               media: str = "all",   # all / photo / video / doc
               log=print, progress=None,
               stop_flag: threading.Event | None = None) -> ExportStats:
    stats = ExportStats()
    os.makedirs(dest_root, exist_ok=True)

    log("正在扫描手机目录…")
    all_files = remote_list_files(adb, serial, dirs, log)
    # 按媒体类型过滤
    if media == "photo":
        keep = lambda p: os.path.splitext(p)[1].lower() in PHOTO_EXTS
    elif media == "video":
        keep = lambda p: os.path.splitext(p)[1].lower() in VIDEO_EXTS
    elif media == "doc":
        keep = lambda p: os.path.splitext(p)[1].lower() in DOC_EXTS
    else:  # all = 照片 + 视频 + 文档
        keep = lambda p: (os.path.splitext(p)[1].lower()
                          in (PHOTO_EXTS | VIDEO_EXTS | DOC_EXTS))
    files = [f for f in all_files if keep(f)]
    dropped = len(all_files) - len(files)
    if dropped:
        log(f"（按类型过滤掉 {dropped} 个文件）")
    stats.total = len(files)
    log(f"共发现 {len(files)} 个目标文件，开始导出…")

    def origin_display(remote: str) -> str:
        """来源显示名：去掉 /sdcard/ 前缀，保留原始目录层级。"""
        disp = remote.lstrip("/")
        for prefix in ("sdcard/", "storage/emulated/0/"):
            if disp.startswith(prefix):
                disp = disp[len(prefix):]
                break
        return disp

    # 增量跳过：先批量取远程大小
    sizes = remote_sizes(adb, serial, files)
    for i, remote in enumerate(files, 1):
        if stop_flag and stop_flag.is_set():
            log("⏹ 用户中止，已完成部分保留。")
            break
        name = remote.rsplit("/", 1)[-1] or remote
        origin = origin_display(remote)
        if progress:
            progress(i - 1, stats.total, origin)
        if mode == "flat":
            dst = os.path.join(dest_root, name)
            rsize = sizes.get(remote)
            if rsize is not None and os.path.exists(dst):
                try:
                    if os.path.getsize(dst) == rsize:
                        stats.skipped += 1
                        continue
                except OSError:
                    pass
        tmp = os.path.join(dest_root, f".tmp_{uuid.uuid4().hex}")
        try:
            remote_pull(adb, serial, remote, tmp)
            _finalize(tmp, origin, dest_root, mode, use_exif, stats, log)
        except Exception as e:  # noqa: BLE001
            stats.failed += 1
            log(f"✘ 失败: {remote}  ({e})")
        finally:
            if os.path.exists(tmp):
                try:
                    os.remove(tmp)
                except OSError:
                    pass
        if progress:
            progress(i, stats.total, origin)
    return stats


# ---------------------------------------------------------------------------
# GUI（ttk clam 风格）
# ---------------------------------------------------------------------------
def run_gui():
    import tkinter as tk
    from tkinter import filedialog, messagebox, scrolledtext, ttk

    root = tk.Tk()
    root.title("Android 照片/视频导出工具")
    root.geometry("780x640")
    root.minsize(700, 560)

    # ---------- ttk clam 主题 ----------
    style = ttk.Style(root)
    if "clam" in style.theme_names():
        style.theme_use("clam")
    BG = "#f2f2f0"
    ACCENT = "#2563a8"
    root.configure(background=BG)
    style.configure(".", background=BG, foreground="#1c1c1c",
                    font=("PingFang SC", 12))
    style.configure("TFrame", background=BG)
    style.configure("TLabelframe", background=BG, borderwidth=1, relief="solid")
    style.configure("TLabelframe.Label", background=BG, foreground=ACCENT,
                    font=("PingFang SC", 12, "bold"))
    style.configure("TLabel", background=BG)
    style.configure("TRadiobutton", background=BG)
    style.configure("TCheckbutton", background=BG)
    style.map("TRadiobutton", background=[("active", BG)])
    style.map("TCheckbutton", background=[("active", BG)])
    style.configure("TButton", padding=(12, 5), font=("PingFang SC", 12))
    style.map("TButton",
              background=[("pressed", "#1d4f85"), ("active", "#3a7bc4")],
              foreground=[("pressed", "#ffffff"), ("active", "#ffffff")])
    style.configure("Accent.TButton", background=ACCENT, foreground="#ffffff")
    style.map("Accent.TButton",
              background=[("disabled", "#a8c4de"), ("pressed", "#1d4f85"),
                          ("active", "#3a7bc4")],
              foreground=[("disabled", "#eeeeee")])
    style.configure("TEntry", fieldbackground="#ffffff", padding=4)
    style.configure("TProgressbar", troughcolor="#dcdcd8", background=ACCENT,
                    bordercolor=BG, lightcolor=ACCENT, darkcolor=ACCENT)

    adb = find_adb()
    stop_flag = threading.Event()
    exporting = {"on": False}
    dir_vars: list[tuple[str, tk.BooleanVar]] = []
    file_log: dict[str, FileLogger | None] = {"obj": None}

    # ---------- 顶部：设备区 ----------
    frm_dev = ttk.LabelFrame(root, text=" 1. 设备（需打开 USB 调试并在手机上点「允许」） ")
    frm_dev.pack(fill="x", padx=10, pady=(10, 5))
    lbl_dev = ttk.Label(frm_dev, text="未检测到设备")
    lbl_dev.pack(side="left", padx=10, pady=8)

    # ---------- 目录选择区 ----------
    frm_dirs = ttk.LabelFrame(root, text=" 2. 要导出的手机目录（可勾选 / 可自定义添加） ")
    frm_dirs.pack(fill="x", padx=10, pady=5)

    grid_holder = ttk.Frame(frm_dirs)
    grid_holder.pack(fill="x", padx=8, pady=(6, 0))

    def add_dir_checkbox(label: str, path: str, checked=True):
        var = tk.BooleanVar(value=checked)
        dir_vars.append((path, var))
        row, col = divmod(len(dir_vars) - 1, 2)
        ttk.Checkbutton(grid_holder, text=f"{label}  [{path}]",
                        variable=var).grid(row=row, column=col,
                                           sticky="w", padx=4, pady=1)

    for label, path in DEFAULT_DIRS:
        add_dir_checkbox(label, path)

    frm_custom = ttk.Frame(frm_dirs)
    frm_custom.pack(fill="x", padx=8, pady=(6, 8))
    var_custom = tk.StringVar()
    ttk.Label(frm_custom, text="自定义目录:").pack(side="left")

    def add_custom():
        p = var_custom.get().strip()
        if not p:
            return
        if not p.startswith("/"):
            p = "/sdcard/" + p.lstrip("/")
        if any(p == existing for existing, _ in dir_vars):
            messagebox.showinfo("提示", "该目录已在清单中。")
            return
        add_dir_checkbox("自定义", p)
        var_custom.set("")

    ttk.Entry(frm_custom, textvariable=var_custom).pack(
        side="left", fill="x", expand=True, padx=6)
    ttk.Button(frm_custom, text="添加", command=add_custom).pack(side="left")

    def selected_dirs() -> list[str]:
        return [p for p, v in dir_vars if v.get()]

    # ---------- 设置区 ----------
    frm_opt = ttk.LabelFrame(root, text=" 3. 导出设置 ")
    frm_opt.pack(fill="x", padx=10, pady=5)

    frm_dst = ttk.Frame(frm_opt)
    frm_dst.pack(fill="x", padx=10, pady=(8, 4))
    var_dest = tk.StringVar()
    ttk.Label(frm_dst, text="目标目录:").pack(side="left")
    ttk.Entry(frm_dst, textvariable=var_dest).pack(
        side="left", fill="x", expand=True, padx=6)

    def pick_dest():
        d = filedialog.askdirectory(title="选择导出目标目录")
        if d:
            var_dest.set(d)

    ttk.Button(frm_dst, text="浏览…", command=pick_dest).pack(side="left")

    frm_sw = ttk.Frame(frm_opt)
    frm_sw.pack(fill="x", padx=10, pady=(0, 8))
    var_mode = tk.StringVar(value="flat")
    ttk.Radiobutton(frm_sw, text="按原文件名平铺导出", value="flat",
                    variable=var_mode).pack(side="left")
    ttk.Radiobutton(frm_sw, text="按拍摄日期建子目录 (YYYY-MM-DD)",
                    value="by-date", variable=var_mode).pack(side="left",
                                                             padx=(16, 0))
    var_exif = tk.BooleanVar(value=True)
    ttk.Checkbutton(frm_sw, text="用 EXIF 拍摄时间归档", variable=var_exif)\
        .pack(side="left", padx=(16, 0))
    var_media = tk.StringVar(value="all")
    ttk.Radiobutton(frm_sw, text="全部", value="all",
                    variable=var_media).pack(side="left", padx=(16, 0))
    ttk.Radiobutton(frm_sw, text="仅照片", value="photo",
                    variable=var_media).pack(side="left")
    ttk.Radiobutton(frm_sw, text="仅视频", value="video",
                    variable=var_media).pack(side="left")
    ttk.Radiobutton(frm_sw, text="仅文档", value="doc",
                    variable=var_media).pack(side="left")

    # ---------- 按钮 + 进度 ----------
    frm_run = ttk.Frame(root)
    frm_run.pack(fill="x", padx=10, pady=5)
    btn_export = ttk.Button(frm_run, text="4. 开始导出", style="Accent.TButton",
                            state="disabled")
    btn_export.pack(side="left")
    pb = ttk.Progressbar(frm_run, mode="determinate")
    pb.pack(side="left", fill="x", expand=True, padx=8)
    lbl_prog = ttk.Label(frm_run, text="")
    lbl_prog.pack(side="left", padx=(0, 8))
    btn_quit = ttk.Button(frm_run, text="退出程序", command=root.destroy)
    btn_quit.pack(side="right")

    # ---------- 日志 ----------
    frm_log = ttk.LabelFrame(root, text=" 导出日志 ")
    frm_log.pack(fill="both", expand=True, padx=10, pady=(5, 10))
    txt = scrolledtext.ScrolledText(frm_log, height=12, state="disabled",
                                    font=("Menlo", 11),
                                    background="#ffffff", foreground="#1c1c1c",
                                    relief="flat", borderwidth=0,
                                    highlightthickness=1,
                                    highlightbackground="#c9c9c4")
    txt.pack(fill="both", expand=True, padx=6, pady=6)

    def log(msg: str):
        # 同时写入界面与目标目录下的日志文件
        fl = file_log["obj"]
        if fl:
            fl.write(str(msg))

        def _append():
            txt.configure(state="normal")
            txt.insert("end", str(msg) + "\n")
            txt.see("end")
            txt.configure(state="disabled")
        root.after(0, _append)

    def progress(done: int, total: int, name: str):
        def _upd():
            pb.configure(maximum=max(total, 1), value=done)
            lbl_prog.configure(text=f"{done}/{total}")
        root.after(0, _upd)

    def do_export():
        dest = var_dest.get().strip()
        if not dest:
            messagebox.showwarning("提示", "请先选择目标目录。")
            return
        dirs = selected_dirs()
        if not dirs:
            messagebox.showwarning("提示", "请至少勾选一个要导出的目录。")
            return
        serial = current_serial()
        if not serial:
            messagebox.showwarning("提示", "未检测到可用设备。")
            return
        stop_flag.clear()
        exporting["on"] = True
        btn_quit.configure(state="disabled")   # 导出期间禁止退出
        btn_export.configure(text="中止导出", command=do_stop)

        # 打开当天日志文件（追加模式）
        lp = log_path_in(dest)
        try:
            os.makedirs(dest, exist_ok=True)
            file_log["obj"] = FileLogger(lp)
            log("=" * 60)
            log(f"开始导出  设备: {serial}   模式: {var_mode.get()}   "
                f"类型: {var_media.get()}")
            log(f"目标目录: {dest}")
            log(f"扫描目录: {', '.join(dirs)}")
            log(f"日志文件: {lp}")
        except Exception as e:  # noqa: BLE001 日志文件失败不影响导出
            file_log["obj"] = None
            log(f"⚠ 无法创建日志文件（{e}），本次导出不记录文件日志")

        def worker():
            try:
                stats = run_export(
                    adb, serial, dirs, dest,
                    mode=var_mode.get(),
                    use_exif=var_exif.get(),
                    media=var_media.get(),
                    log=log, progress=progress, stop_flag=stop_flag,
                )
                log(f"\n===== 完成 =====\n"
                    f"总文件: {stats.total}   新拷贝: {stats.copied}"
                    f"   跳过: {stats.skipped}   失败: {stats.failed}\n"
                    f"拷贝数据量: {human_size(stats.bytes_copied)}\n"
                    f"目标目录: {dest}")
                root.after(0, lambda: messagebox.showinfo(
                    "导出完成",
                    f"新拷贝 {stats.copied} 个，跳过 {stats.skipped} 个，"
                    f"失败 {stats.failed} 个。\n目标目录：{dest}"))
            except Exception as e:  # noqa: BLE001
                err_msg = str(e)
                log(f"出错: {err_msg}")
                root.after(0, lambda msg=err_msg: messagebox.showerror(
                    "出错", msg))
            finally:
                if file_log["obj"]:
                    file_log["obj"].close()
                    file_log["obj"] = None
                root.after(0, _reset_btn)

        threading.Thread(target=worker, daemon=True).start()

    def do_stop():
        stop_flag.set()

    def _reset_btn():
        exporting["on"] = False
        btn_export.configure(text="4. 开始导出", command=do_export)
        btn_quit.configure(state="normal")     # 导出结束恢复可退出

    def on_close():
        if exporting["on"]:
            messagebox.showwarning("导出进行中",
                                   "正在导出，请先点「中止导出」再退出。")
            return
        root.destroy()

    btn_export.configure(command=do_export)
    root.protocol("WM_DELETE_WINDOW", on_close)

    # ---------- 依赖提示 ----------
    if adb is None:
        log("⚠ 未找到 adb。请安装：\n"
            "   macOS:  brew install android-platform-tools\n"
            "   Windows: 下载 Google platform-tools 解压并加入 PATH\n"
            "   （https://developer.android.com/tools/releases/platform-tools）")
    else:
        log(f"✔ adb: {adb}")

    # ---------- 设备检测 ----------
    current = {"serial": None}

    def current_serial() -> str | None:
        return current["serial"]

    def refresh_devices():
        ok_serial = None
        if adb:
            for serial, state in list_devices(adb):
                if state == "device":
                    ok_serial = serial
                elif state == "unauthorized" and not current["serial"]:
                    lbl_dev.configure(
                        text=f"设备 {serial} 待授权：请在手机上点「允许 USB 调试」",
                        foreground="#b03030")
            if ok_serial:
                model = device_model(adb, ok_serial)
                lbl_dev.configure(text=f"已连接: {model} ({ok_serial})",
                                  foreground="#1c1c1c")
                btn_export.configure(state="normal")
            elif not any(s == "unauthorized" for _, s in list_devices(adb)):
                lbl_dev.configure(
                    text="未检测到设备（请 USB 连接、开启 USB 调试并点「允许」）",
                    foreground="#b03030")
                btn_export.configure(state="disabled")
        else:
            lbl_dev.configure(text="未找到 adb，无法检测设备", foreground="#b03030")
        current["serial"] = ok_serial
        root.after(3000, refresh_devices)

    refresh_devices()
    root.mainloop()


# ---------------------------------------------------------------------------
# 命令行模式
# ---------------------------------------------------------------------------
def run_cli(args) -> int:
    adb = find_adb()
    if not adb:
        print("错误: 未找到 adb。macOS: brew install android-platform-tools；"
              "Windows: 下载 platform-tools 并加入 PATH", file=sys.stderr)
        return 1
    devices = [(s, st) for s, st in list_devices(adb) if st == "device"]
    if not devices:
        print("未检测到可用设备。请 USB 连接、开启 USB 调试并在手机上点「允许」。",
              file=sys.stderr)
        return 1
    serial = devices[0][0]
    print(f"检测到设备: {device_model(adb, serial)} ({serial})")
    dirs = [d for d in args.dirs] or [p for _, p in DEFAULT_DIRS]

    # 文件日志
    try:
        os.makedirs(args.dest, exist_ok=True)
        fl = FileLogger(log_path_in(args.dest))
    except Exception:
        fl = None

    def _log(msg: str):
        print(msg)
        if fl:
            fl.write(str(msg))

    _log("=" * 60)
    _log(f"开始导出  设备: {serial}   模式: {args.mode}   类型: {args.media}")
    _log(f"目标目录: {args.dest}")
    _log(f"扫描目录: {', '.join(dirs)}")
    if fl:
        _log(f"日志文件: {fl.path}")
    try:
        stats = run_export(adb, serial, dirs, args.dest, mode=args.mode,
                           use_exif=not args.no_exif, media=args.media,
                           log=_log)
    finally:
        if fl:
            fl.close()
    print(f"\n总文件 {stats.total} | 新拷贝 {stats.copied} | 跳过 {stats.skipped}"
          f" | 失败 {stats.failed} | 数据量 {human_size(stats.bytes_copied)}")
    return 0 if stats.failed == 0 else 2


def main():
    if len(sys.argv) > 1:
        import argparse
        parser = argparse.ArgumentParser(
            description="Android 照片/视频导出到电脑（adb）")
        parser.add_argument("--dest", required=True, help="目标目录")
        parser.add_argument("--mode", choices=["flat", "by-date"], default="flat")
        parser.add_argument("--media", choices=["all", "photo", "video", "doc"],
                            default="all")
        parser.add_argument("--no-exif", action="store_true",
                            help="不使用 EXIF，按文件修改时间归档")
        parser.add_argument("--dirs", nargs="*", default=None,
                            help="要扫描的手机目录（默认全部预置目录）")
        sys.exit(run_cli(parser.parse_args()))
    else:
        run_gui()


if __name__ == "__main__":
    main()
