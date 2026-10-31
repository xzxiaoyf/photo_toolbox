#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
iphone_photo_exporter.py — iPhone/iPad 照片批量导出到 Mac 工具 v3
==================================================================

连接方式（自动选择）：
  1. pymobiledevice3（推荐，纯 Python，无需任何 brew 依赖）
     通过 iOS AFC 协议直接读取设备媒体区，无需挂载、无需 FUSE。
     新版库为 asyncio API，程序已适配（内部事件循环驱动）。
     安装：pip install pymobiledevice3
  2. ifuse（兜底，可选）：brew install ifuse，走挂载方式。

功能：
  - 检测 USB / Wi-Fi 连接的 iPhone/iPad（兼容新旧版 pymobiledevice3）
  - 扫描设备 DCIM 目录全部照片/视频（Live Photo 配对文件成对存在）
  - 增量拷贝：目标已存在且大小一致的文件自动跳过
  - 可选按拍摄日期（EXIF DateTimeOriginal，回退设备 mtime）建 YYYY-MM-DD 子目录
  - GUI（ttk clam 主题）+ 命令行两种模式
"""

import asyncio
import inspect
import os
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
# 让脚本可直接用系统 python3 运行：自动加载同目录 .venv 的 site-packages
# ---------------------------------------------------------------------------
def _bootstrap_venv():
    here = os.path.dirname(os.path.abspath(__file__))
    venv_lib = os.path.join(here, ".venv", "lib")
    if os.path.isdir(venv_lib):
        for sub in os.listdir(venv_lib):
            sp = os.path.join(venv_lib, sub, "site-packages")
            if os.path.isdir(sp) and sp not in sys.path:
                sys.path.insert(0, sp)


_bootstrap_venv()

# ---------------------------------------------------------------------------
# 常量
# ---------------------------------------------------------------------------
BREW_PATHS = ["/opt/homebrew/bin", "/usr/local/bin", "/usr/bin", "/bin"]
VIDEO_EXTS = {".mov", ".mp4"}
DCIM_ROOT = "/DCIM"


def find_tool(name: str) -> str | None:
    found = shutil.which(name)
    if found:
        return found
    for d in BREW_PATHS:
        p = os.path.join(d, name)
        if os.path.isfile(p) and os.access(p, os.X_OK):
            return p
    return None


def run_cmd(args: list[str], timeout: int = 60) -> tuple[int, str]:
    try:
        proc = subprocess.run(args, capture_output=True, text=True, timeout=timeout)
        return proc.returncode, ((proc.stdout or "") + (proc.stderr or "")).strip()
    except FileNotFoundError:
        return 127, f"命令不存在: {args[0]}"
    except subprocess.TimeoutExpired:
        return 124, f"命令超时: {' '.join(args)}"


def human_size(n: float) -> str:
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if abs(n) < 1024 or unit == "TB":
            return f"{n:.1f}{unit}" if unit != "B" else f"{int(n)}B"
        n /= 1024.0


def _has_pmd3() -> bool:
    try:
        import pymobiledevice3  # noqa: F401
        return True
    except ImportError:
        return False


def _run_maybe_async(fn, *args, **kwargs):
    """兼容新旧版 pymobiledevice3：协程则用 asyncio.run 执行。"""
    res = fn(*args, **kwargs)
    if inspect.iscoroutine(res):
        res = asyncio.run(res)
    return res


# ---------------------------------------------------------------------------
# 设备检测
# ---------------------------------------------------------------------------
def list_devices() -> list[tuple[str, str]]:
    """返回 [(udid, 说明), ...]，优先 pymobiledevice3，回退 idevice_id。"""
    if _has_pmd3():
        try:
            from pymobiledevice3.usbmux import list_devices
            devs = _run_maybe_async(list_devices)
            return [(d.serial, d.serial) for d in devs]
        except Exception:
            pass
    idevice_id = find_tool("idevice_id")
    if not idevice_id:
        return []
    rc, out = run_cmd([idevice_id, "-l"])
    if rc != 0:
        return []
    return [(ln.strip(), ln.strip()) for ln in out.splitlines() if ln.strip()]


# ---------------------------------------------------------------------------
# 友好错误转换
# ---------------------------------------------------------------------------
def _friendly_error(e: Exception) -> str:
    name = type(e).__name__
    if name in ("NotPairedError",) or "pair" in str(e).lower():
        return ("设备尚未与本机配对。\n"
                "请解锁 iPhone/iPad，在弹窗中点「信任此电脑」并输入密码，然后重试。")
    if name in ("PasswordRequiredError",):
        return ("设备已锁定（有密码）。\n"
                "请解锁 iPhone/iPad 屏幕后重试。")
    return f"{name}: {e}"


# ---------------------------------------------------------------------------
# 拍摄日期
# ---------------------------------------------------------------------------
def shot_date(local_path: str, use_exif: bool) -> datetime:
    """优先 EXIF DateTimeOriginal（exiftool），失败回退文件修改时间。"""
    if use_exif:
        exiftool = find_tool("exiftool")
        if exiftool:
            rc, out = run_cmd(
                [exiftool, "-s3", "-d", "%Y-%m-%d", "-DateTimeOriginal", "-T", "-n",
                 local_path],
                timeout=15,
            )
            if rc == 0:
                for part in (out.splitlines()[0] if out else "").split():
                    try:
                        return datetime.strptime(part, "%Y-%m-%d")
                    except ValueError:
                        continue
    try:
        return datetime.fromtimestamp(os.path.getsize(local_path) and
                                      os.path.getmtime(local_path))
    except OSError:
        return datetime.now()


# ---------------------------------------------------------------------------
# 通用收尾逻辑：临时文件 → 最终位置（含日期归档与二次去重）
# ---------------------------------------------------------------------------
def _finalize(tmp: str, name: str, dest_root: str, mode: str, use_exif: bool,
              stats, log) -> None:
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
    log(f"✔ {name} -> {os.path.relpath(dst, dest_root)} "
        f"({human_size(os.path.getsize(dst))})")


class ExportStats:
    def __init__(self):
        self.total = 0
        self.copied = 0
        self.skipped = 0
        self.failed = 0
        self.bytes_copied = 0


# ---------------------------------------------------------------------------
# 后端一：pymobiledevice3 AFC（async API，整个会话在一个事件循环里完成）
# ---------------------------------------------------------------------------
def afc_available() -> bool:
    return _has_pmd3()


def run_afc_export(udid: str | None, dest_root: str, mode: str = "flat",
                   use_exif: bool = True, skip_videos: bool = False,
                   log=print, progress=None,
                   stop_flag: threading.Event | None = None) -> ExportStats:
    """同步入口：内部用 asyncio.run 驱动整个 AFC 会话。"""

    async def _flow() -> ExportStats:
        from pymobiledevice3.lockdown import create_using_usbmux
        from pymobiledevice3.services.afc import AfcService

        stats = ExportStats()
        lockdown = await (create_using_usbmux(serial=udid) if udid
                          else create_using_usbmux())
        try:
            afc = AfcService(lockdown=lockdown)
            async with afc:
                # 枚举 DCIM 全部文件
                try:
                    await afc.listdir(DCIM_ROOT)
                except Exception:
                    raise RuntimeError(
                        "已连接但设备媒体区没有 DCIM 目录"
                        "（设备上可能没有照片，或照片被隐藏）。")
                files = []
                async for dirpath, _dirs, filenames in afc.walk(DCIM_ROOT):
                    for fn in sorted(filenames):
                        if fn.startswith("."):
                            continue
                        files.append(f"{dirpath.rstrip('/')}/{fn}")
                stats.total = len(files)
                log(f"设备上共发现 {len(files)} 个媒体文件，开始导出…")

                for i, remote in enumerate(files, 1):
                    if stop_flag and stop_flag.is_set():
                        log("⏹ 用户中止，已完成部分保留。")
                        break
                    name = remote.rsplit("/", 1)[-1]
                    ext = os.path.splitext(name)[1].lower()
                    if progress:
                        progress(i - 1, stats.total, name)
                    if skip_videos and ext in VIDEO_EXTS:
                        log(f"⏭ 跳过视频: {name}")
                        stats.skipped += 1
                        continue
                    # flat 模式先按大小做增量跳过
                    if mode == "flat":
                        dst = os.path.join(dest_root, name)
                        if os.path.exists(dst):
                            try:
                                st = await afc.stat(remote)
                                if os.path.getsize(dst) == int(st.get("st_size", 0)):
                                    stats.skipped += 1
                                    continue
                            except OSError:
                                pass
                    tmp = os.path.join(dest_root, f".tmp_{uuid.uuid4().hex}")
                    try:
                        os.makedirs(dest_root, exist_ok=True)
                        # pull 会流式下载大文件，并回写设备 mtime
                        await afc.pull(remote, tmp, progress_bar=False)
                        _finalize(tmp, name, dest_root, mode, use_exif,
                                  stats, log)
                    except Exception as e:  # noqa: BLE001 单个失败不中断
                        stats.failed += 1
                        log(f"✘ 失败: {name}  ({e})")
                    finally:
                        if os.path.exists(tmp):
                            try:
                                os.remove(tmp)
                            except OSError:
                                pass
                    if progress:
                        progress(i, stats.total, name)
        finally:
            try:
                await lockdown.close()
            except Exception:
                pass
        return stats

    try:
        return asyncio.run(_flow())
    except Exception as e:  # noqa: BLE001
        raise RuntimeError(_friendly_error(e)) from e


# ---------------------------------------------------------------------------
# 后端二：ifuse 挂载（兜底）
# ---------------------------------------------------------------------------
class LocalFileEntry:
    """ifuse 挂载后的本地文件。"""

    def __init__(self, path: str):
        self.path = path
        self.name = os.path.basename(path)

    def size(self) -> int | None:
        try:
            return os.path.getsize(self.path)
        except OSError:
            return None

    def fetch_to(self, tmp_path: str):
        shutil.copyfile(self.path, tmp_path)


class DeviceMounter:
    def __init__(self):
        self.ifuse = find_tool("ifuse")
        self.mountpoint: str | None = None

    @property
    def available(self) -> bool:
        return self.ifuse is not None

    def mount(self) -> str:
        if not self.available:
            raise RuntimeError(
                "未找到 ifuse，且 pymobiledevice3 也不可用。\n"
                "推荐方案：pip install pymobiledevice3\n"
                "备选方案：brew install ifuse（macOS 新版本可能无预编译包）"
            )
        if self.mountpoint and os.path.ismount(self.mountpoint):
            return self.mountpoint
        import tempfile
        mp = tempfile.mkdtemp(prefix="iphone_export_")
        rc, out = run_cmd([self.ifuse, mp], timeout=30)
        if rc != 0 or not os.path.ismount(mp):
            shutil.rmtree(mp, ignore_errors=True)
            raise RuntimeError(_friendly_error(RuntimeError(out)))
        self.mountpoint = mp
        return mp

    def unmount(self):
        if not self.mountpoint:
            return
        mp = self.mountpoint
        rc, _ = run_cmd(["umount", mp], timeout=30)
        if rc != 0:
            run_cmd(["diskutil", "unmount", "force", mp], timeout=30)
        shutil.rmtree(mp, ignore_errors=True)
        self.mountpoint = None


def run_ifuse_export(dest_root: str, mode: str = "flat", use_exif: bool = True,
                     skip_videos: bool = False, log=print, progress=None,
                     stop_flag: threading.Event | None = None) -> ExportStats:
    """ifuse 兜底路径：挂载 → 枚举 → 导出 → 卸载。"""
    mounter = DeviceMounter()
    mp = mounter.mount()
    try:
        dcim = os.path.join(mp, "DCIM")
        if not os.path.isdir(dcim):
            raise RuntimeError("挂载成功但未找到 DCIM 目录（设备上可能没有照片）。")
        entries = []
        for root, _dirs, names in os.walk(dcim):
            for name in sorted(names):
                if name.startswith("."):
                    continue
                entries.append(LocalFileEntry(os.path.join(root, name)))
        stats = ExportStats()
        stats.total = len(entries)
        os.makedirs(dest_root, exist_ok=True)
        log(f"设备上共发现 {len(entries)} 个媒体文件，开始导出…")
        for i, entry in enumerate(entries, 1):
            if stop_flag and stop_flag.is_set():
                log("⏹ 用户中止，已完成部分保留。")
                break
            name = entry.name
            ext = os.path.splitext(name)[1].lower()
            if progress:
                progress(i - 1, stats.total, name)
            if skip_videos and ext in VIDEO_EXTS:
                log(f"⏭ 跳过视频: {name}")
                stats.skipped += 1
                continue
            if mode == "flat":
                dst = os.path.join(dest_root, name)
                if entry.size() is not None and os.path.exists(dst):
                    try:
                        if os.path.getsize(dst) == entry.size():
                            stats.skipped += 1
                            continue
                    except OSError:
                        pass
            tmp = os.path.join(dest_root, f".tmp_{uuid.uuid4().hex}")
            try:
                entry.fetch_to(tmp)
                _finalize(tmp, name, dest_root, mode, use_exif, stats, log)
            except Exception as e:  # noqa: BLE001
                stats.failed += 1
                log(f"✘ 失败: {name}  ({e})")
            finally:
                if os.path.exists(tmp):
                    try:
                        os.remove(tmp)
                    except OSError:
                        pass
            if progress:
                progress(i, stats.total, name)
        return stats
    finally:
        mounter.unmount()


# ---------------------------------------------------------------------------
# 统一导出入口
# ---------------------------------------------------------------------------
def run_export(dest_root: str, mode: str = "flat", use_exif: bool = True,
               skip_videos: bool = False, log=print, progress=None,
               stop_flag: threading.Event | None = None) -> ExportStats:
    if afc_available():
        return run_afc_export(None, dest_root, mode, use_exif, skip_videos,
                              log, progress, stop_flag)
    return run_ifuse_export(dest_root, mode, use_exif, skip_videos,
                            log, progress, stop_flag)


# ---------------------------------------------------------------------------
# GUI（ttk clam 风格）
# ---------------------------------------------------------------------------
def run_gui():
    import tkinter as tk
    from tkinter import filedialog, messagebox, scrolledtext, ttk

    root = tk.Tk()
    root.title("iPhone/iPad 照片导出工具")
    root.geometry("760x560")
    root.minsize(680, 480)

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

    stop_flag = threading.Event()
    exporting = {"on": False}

    # ---------- 顶部：设备区 ----------
    frm_dev = ttk.LabelFrame(root, text=" 1. 设备（USB 连接，手机上点「信任此电脑」） ")
    frm_dev.pack(fill="x", padx=10, pady=(10, 5))
    lbl_dev = ttk.Label(frm_dev, text="未检测到设备")
    lbl_dev.pack(side="left", padx=10, pady=8)

    # ---------- 设置区 ----------
    frm_opt = ttk.LabelFrame(root, text=" 2. 导出设置 ")
    frm_opt.pack(fill="x", padx=10, pady=5)

    frm_dst = ttk.Frame(frm_opt)
    frm_dst.pack(fill="x", padx=10, pady=(8, 4))
    var_dest = tk.StringVar()
    ttk.Label(frm_dst, text="目标目录:").pack(side="left")
    ttk.Entry(frm_dst, textvariable=var_dest).pack(
        side="left", fill="x", expand=True, padx=6)

    def pick_dest():
        d = filedialog.askdirectory(title="选择照片导出目标目录")
        if d:
            var_dest.set(d)

    ttk.Button(frm_dst, text="浏览…", command=pick_dest).pack(side="left")

    frm_sw = ttk.Frame(frm_opt)
    frm_sw.pack(fill="x", padx=10, pady=(0, 8))
    var_mode = tk.StringVar(value="flat")
    ttk.Radiobutton(frm_sw, text="按原文件名平铺导出", value="flat",
                    variable=var_mode).pack(side="left")
    ttk.Radiobutton(frm_sw, text="按拍摄日期建子目录 (YYYY-MM-DD)", value="by-date",
                    variable=var_mode).pack(side="left", padx=(16, 0))
    var_exif = tk.BooleanVar(value=True)
    ttk.Checkbutton(frm_sw, text="用 EXIF 拍摄时间归档", variable=var_exif)\
        .pack(side="left", padx=(16, 0))
    var_skipvideo = tk.BooleanVar(value=False)
    ttk.Checkbutton(frm_sw, text="跳过视频", variable=var_skipvideo)\
        .pack(side="left", padx=(16, 0))

    # ---------- 按钮 + 进度 ----------
    frm_run = ttk.Frame(root)
    frm_run.pack(fill="x", padx=10, pady=5)
    btn_export = ttk.Button(frm_run, text="3. 开始导出", style="Accent.TButton",
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
        stop_flag.clear()
        exporting["on"] = True
        btn_quit.configure(state="disabled")   # 导出期间禁止退出
        btn_export.configure(text="中止导出", command=do_stop)

        def worker():
            try:
                log("正在连接设备并读取照片列表…")
                stats = run_export(
                    dest,
                    mode=var_mode.get(),
                    use_exif=var_exif.get(),
                    skip_videos=var_skipvideo.get(),
                    log=log, progress=progress, stop_flag=stop_flag,
                )
                summary = (f"\n===== 完成 =====\n"
                           f"总文件: {stats.total}   新拷贝: {stats.copied}"
                           f"   跳过: {stats.skipped}   失败: {stats.failed}\n"
                           f"拷贝数据量: {human_size(stats.bytes_copied)}\n"
                           f"目标目录: {dest}")
                log(summary)
                root.after(0, lambda: messagebox.showinfo(
                    "导出完成",
                    f"新拷贝 {stats.copied} 个，跳过 {stats.skipped} 个，"
                    f"失败 {stats.failed} 个。\n目标目录：{dest}"))
            except Exception as e:  # noqa: BLE001
                # 注意：except 块结束后 e 会被删除，必须先取出字符串
                err_msg = str(e)
                log(f"出错: {err_msg}")
                root.after(0, lambda msg=err_msg: messagebox.showerror(
                    "出错", msg))
            finally:
                root.after(0, _reset_btn)

        threading.Thread(target=worker, daemon=True).start()

    def do_stop():
        stop_flag.set()

    def _reset_btn():
        exporting["on"] = False
        btn_export.configure(text="3. 开始导出", command=do_export)
        btn_quit.configure(state="normal")     # 导出结束恢复可退出

    btn_export.configure(command=do_export)

    def on_close():
        if exporting["on"]:
            messagebox.showwarning("导出进行中",
                                   "正在导出照片，请先点「中止导出」再退出。")
            return
        root.destroy()

    root.protocol("WM_DELETE_WINDOW", on_close)

    # ---------- 依赖提示 ----------
    if sys.platform == "win32":
        _pip_cmd = "pip install pymobiledevice3"
        _usbmux_hint = ("Windows 需先安装苹果设备服务：微软商店安装「Apple Devices」"
                        "应用或 iTunes（提供 usbmuxd 驱动），装好后插手机点「信任」。")
    else:
        _pip_cmd = "pip install pymobiledevice3"
        _usbmux_hint = ""
    if not afc_available() and not DeviceMounter().available:
        log(f"⚠ 缺少连接方式。请执行:  {_pip_cmd}\n{_usbmux_hint}")
    elif not afc_available():
        log(f"提示: 未安装 pymobiledevice3，当前走 ifuse 挂载模式。\n"
            f"   建议执行:  {_pip_cmd}")
    else:
        log("✔ 连接方式: pymobiledevice3（AFC 协议，无需挂载）")
    if not find_tool("exiftool"):
        log("提示: 未安装 exiftool，按日期归档将回退为设备时间戳。"
            "可执行: brew install exiftool")

    # ---------- 设备检测 ----------
    def refresh_devices():
        devices = list_devices()
        if devices:
            lbl_dev.configure(text=f"已连接 {len(devices)} 台: "
                                   + "；".join(d for _, d in devices),
                              foreground="#1c1c1c")
            btn_export.configure(state="normal")
        else:
            lbl_dev.configure(text="未检测到设备（请 USB 连接并解锁手机点「信任」）",
                              foreground="#b03030")
            btn_export.configure(state="disabled")
        root.after(3000, refresh_devices)

    refresh_devices()
    root.mainloop()


# ---------------------------------------------------------------------------
# 命令行模式
# ---------------------------------------------------------------------------
def run_cli(args) -> int:
    if not afc_available() and not find_tool("ifuse"):
        print("错误: 缺少连接方式。请执行  pip install pymobiledevice3"
              "（推荐）或 brew install ifuse", file=sys.stderr)
        return 1
    devices = list_devices()
    if not devices:
        print("未检测到设备，请 USB 连接 iPhone/iPad 并点「信任此电脑」。",
              file=sys.stderr)
        return 1
    print(f"检测到设备: {devices[0][0]}")
    stats = run_export(args.dest, mode=args.mode, use_exif=not args.no_exif,
                       skip_videos=args.skip_videos)
    print(f"\n总文件 {stats.total} | 新拷贝 {stats.copied} | 跳过 {stats.skipped}"
          f" | 失败 {stats.failed} | 数据量 {human_size(stats.bytes_copied)}")
    return 0 if stats.failed == 0 else 2


def main():
    if len(sys.argv) > 1:
        import argparse
        parser = argparse.ArgumentParser(description="iPhone/iPad 照片导出到 Mac")
        parser.add_argument("--dest", required=True, help="目标目录")
        parser.add_argument("--mode", choices=["flat", "by-date"], default="flat")
        parser.add_argument("--no-exif", action="store_true",
                            help="不使用 EXIF，按设备时间戳归档")
        parser.add_argument("--skip-videos", action="store_true")
        sys.exit(run_cli(parser.parse_args()))
    else:
        run_gui()


if __name__ == "__main__":
    main()
