#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
照片/视频按拍摄日期分类工具 v2 (统一灰色背景 + ttk clam 风格)
支持按【年月】或【年月日】两种模式分类存放，使用 exiftool 读取元数据。

【v2 修复清单】
 1. [P1] 日期解析重写：修正紧凑格式(20240315)切口错位、0000:00:00 垃圾目录、
        月份 13 等非法值照算的问题，全部改为 strptime 严格校验
 2. [P1] 视频时间改由 exiftool -api QuickTimeUTC 在读取端换算本地时间，
        不再把 UTC 值直接当本地时间（跨日/跨月归类错误）
 3. [P1] 扫描时排除目标目录，避免把上次分类产物再次分类、无限增殖
 4. [P1] process_files 顶层 try/except/finally 兜底，异常不再导致按钮永久禁用
 5. [P2] exiftool 改分批读取（每批 500 个文件）+ 单批 600s 超时，
        一批失败不影响其余；读取阶段进度条也实时推进
 6. [P2] 新增"跳过已存在文件"选项（同名同大小视为已存在），不再只生成 _1/_2
 7. [P2] 路径索引键改用 normcase+normpath，修 Windows 大小写失配
 8. [P2] 新增"取消处理"按钮；退出时安全中止后台线程，UI 回调统一防 TclError
 9. [P2] 界面新增实时日志区，可看到逐文件处理进度与失败原因
10. [P2] 未处理原因分类统计（不支持格式/无日期/复制失败/已跳过）
11. [P2] 消除 from tkinter import * 通配导入；跨平台字体适配
12. [P2] .svg 移出照片扩展名；日期非法值统一拦截（年份 <1970 或 >2100 视为无效）
"""
# pyinstaller -F photo_classifier_v2.py

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import traceback
from datetime import datetime

import tkinter as tk
from tkinter import filedialog, messagebox, ttk
from tkinter import scrolledtext

IS_WIN = sys.platform == "win32"

# 统一灰色背景色常量
BG_COLOR = "#D9D9D9"


# ─────────────── 跨平台字体适配 ───────────────
class StyleAdapter:
    @staticmethod
    def get_font(size=11, bold=False):
        if IS_WIN:
            return ("Microsoft YaHei", max(9, size), "bold" if bold else "normal")
        return ("PingFang SC", size, "bold" if bold else "normal")

    @staticmethod
    def get_mono(size=10):
        return (("Consolas", size, "normal") if IS_WIN else ("Menlo", size, "normal"))


class PhotoClassifierApp:
    # 媒体扩展名（.svg 已剔除：矢量图无拍摄元数据）
    PHOTO_EXTS = {
        '.jpg', '.jpeg', '.png', '.gif', '.bmp', '.tiff', '.tif',
        '.raw', '.cr2', '.cr3', '.nef', '.arw', '.orf', '.rw2',
        '.heic', '.heif','.hif', '.webp', '.dng', '.pef', '.srw',
        '.raf', '.x3f', '.3fr', '.iiq', '.mrw', '.dcr'
    }
    VIDEO_EXTS = {
        '.mp4', '.avi', '.mov', '.mkv', '.wmv', '.flv', '.webm',
        '.m4v', '.mpg', '.mpeg', '.3gp', '.ts', '.mts', '.m2ts',
        '.vob', '.rm', '.rmvb', '.asf', '.divx'
    }

    # 日期字段回退链（视频 TrackCreateDate 一并纳入）
    DATE_FIELDS = ('DateTimeOriginal', 'CreateDate', 'MediaCreateDate',
                   'TrackCreateDate', 'FileCreateDate', 'FileModifyDate')

    BATCH_SIZE = 500          # exiftool 每批读取的文件数
    BATCH_TIMEOUT = 600       # 单批超时（秒）

    def __init__(self, root):
        self.root = root
        self.root.title("照片/视频按日期分类工具 v2")
        self.root.geometry("760x620")
        self.root.resizable(True, True)
        self.root.configure(bg=BG_COLOR)

        self._apply_styles()

        # 变量
        self.source_dir = tk.StringVar()
        self.target_dir = tk.StringVar()
        self.classify_mode = tk.StringVar(value="ym")
        self.skip_existing = tk.BooleanVar(value=True)
        self.progress_value = tk.DoubleVar(value=0)
        self.is_processing = False
        self.cancel_event = threading.Event()
        self._window_alive = True

        self._build_ui()
        self.root.protocol("WM_DELETE_WINDOW", self.exit_app)

    # ──────────────────────────────────────
    #  样式
    # ──────────────────────────────────────
    def _apply_styles(self):
        style = ttk.Style()
        style.theme_use("clam")

        style.configure(".", background=BG_COLOR, font=StyleAdapter.get_font(11))
        style.configure("TFrame", background=BG_COLOR)
        style.configure("TLabel", background=BG_COLOR)
        style.configure("TButton", background=BG_COLOR)
        style.configure("TRadiobutton", background=BG_COLOR)
        style.configure("TCheckbutton", background=BG_COLOR)
        style.configure("TLabelframe", background=BG_COLOR)
        style.configure("TLabelframe.Label", background=BG_COLOR)
        style.configure("TEntry", fieldbackground=BG_COLOR, background=BG_COLOR)
        style.configure("Status.TLabel", background=BG_COLOR,
                        font=StyleAdapter.get_font(10), foreground="#555555")
        style.configure("Horizontal.TProgressbar",
                        troughcolor=BG_COLOR, background="#6C9E6C")

    # ──────────────────────────────────────
    #  界面
    # ──────────────────────────────────────
    def _build_ui(self):
        # === 第一行：选择原目录 ===
        frame1 = ttk.Frame(self.root, padding=10)
        frame1.pack(fill=tk.X)
        ttk.Label(frame1, text="原照片目录:", width=12, anchor='e').pack(side=tk.LEFT)
        ttk.Entry(frame1, textvariable=self.source_dir, width=48).pack(side=tk.LEFT, padx=5)
        ttk.Button(frame1, text="选择原目录", command=self.select_source,
                   padding=(12, 4)).pack(side=tk.LEFT)

        # === 第二行：选择目标目录 ===
        frame2 = ttk.Frame(self.root, padding=10)
        frame2.pack(fill=tk.X)
        ttk.Label(frame2, text="目标目录:", width=12, anchor='e').pack(side=tk.LEFT)
        ttk.Entry(frame2, textvariable=self.target_dir, width=48).pack(side=tk.LEFT, padx=5)
        ttk.Button(frame2, text="选择目标目录", command=self.select_target,
                   padding=(12, 4)).pack(side=tk.LEFT)

        # === 第三行：分类模式 + 选项 ===
        mode_frame = ttk.LabelFrame(self.root, text="分类方式", padding=10)
        mode_frame.pack(fill=tk.X, padx=10, pady=(6, 2))

        ttk.Radiobutton(
            mode_frame, text="按 年-月 分类 (例: 202403)",
            variable=self.classify_mode, value="ym"
        ).pack(side=tk.LEFT, padx=(20, 10))

        ttk.Radiobutton(
            mode_frame, text="按 年-月-日 分类 (例: 20240315)",
            variable=self.classify_mode, value="ymd"
        ).pack(side=tk.LEFT, padx=10)

        ttk.Checkbutton(
            mode_frame, text="跳过已存在文件（同名同大小）",
            variable=self.skip_existing
        ).pack(side=tk.LEFT, padx=20)

        # === 第四行：进度条 ===
        frame3 = ttk.Frame(self.root, padding=10)
        frame3.pack(fill=tk.X)
        self.progress = ttk.Progressbar(
            frame3, variable=self.progress_value, maximum=100
        )
        self.progress.pack(fill=tk.X, expand=True)

        # === 第五行：操作按钮 ===
        frame4 = ttk.Frame(self.root, padding=(10, 8))
        frame4.pack(fill=tk.X)

        self.btn_start = ttk.Button(
            frame4, text="开始处理", command=self.start_process, padding=(20, 7)
        )
        self.btn_start.pack(side=tk.LEFT, padx=(40, 10))

        self.btn_cancel = ttk.Button(
            frame4, text="取消处理", command=self.cancel_process, padding=(20, 7),
            state=tk.DISABLED
        )
        self.btn_cancel.pack(side=tk.LEFT, padx=10)

        self.btn_exit = ttk.Button(
            frame4, text="退出程序", command=self.exit_app, padding=(20, 7)
        )
        self.btn_exit.pack(side=tk.RIGHT, padx=40)

        # === 第六行：实时日志 ===
        log_frame = ttk.LabelFrame(self.root, text="实时处理日志", padding=5)
        log_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))
        self.log_text = scrolledtext.ScrolledText(
            log_frame, height=12, font=StyleAdapter.get_mono(10),
            bg="#F5F5F5", fg="#333333", insertbackground="black", state=tk.DISABLED
        )
        self.log_text.pack(fill=tk.BOTH, expand=True)

        # === 状态行 ===
        self.lbl_status = ttk.Label(self.root, text="就绪", style="Status.TLabel",
                                    anchor='w', padding=(12, 0, 12, 6))
        self.lbl_status.pack(fill=tk.X)

    # ──────────────────────────────────────
    #  UI 线程安全辅助
    # ──────────────────────────────────────
    def _ui(self, fn, *args):
        """线程安全地把调用调度到主线程；窗口已销毁时静默忽略"""
        try:
            self.root.after(0, lambda: self._ui_run(fn, args))
        except (tk.TclError, RuntimeError):
            pass

    def _ui_run(self, fn, args):
        if not self._window_alive:
            return
        try:
            fn(*args)
        except tk.TclError:
            pass

    def gui_log(self, msg):
        def _append():
            self.log_text.configure(state=tk.NORMAL)
            self.log_text.insert(tk.END, msg + "\n")
            self.log_text.see(tk.END)
            self.log_text.configure(state=tk.DISABLED)
        self._ui(_append)

    def set_status(self, text):
        self._ui(lambda: self.lbl_status.configure(text=text))

    def update_progress(self, value):
        self._ui(lambda: self.progress_value.set(value))

    # ──────────────────────────────────────
    #  事件回调
    # ──────────────────────────────────────
    def select_source(self):
        directory = filedialog.askdirectory(title="选择原照片目录")
        if directory:
            self.source_dir.set(directory)

    def select_target(self):
        directory = filedialog.askdirectory(title="选择保存分类照片的目标目录")
        if directory:
            self.target_dir.set(directory)

    def start_process(self):
        if self.is_processing:
            messagebox.showwarning("提示", "正在处理中，请稍候...")
            return

        source = self.source_dir.get().strip()
        target = self.target_dir.get().strip()

        if not source:
            messagebox.showwarning("警告", "请先选择原照片目录！")
            return
        if not target:
            messagebox.showwarning("警告", "请先选择目标目录！")
            return
        if not os.path.isdir(source):
            messagebox.showerror("错误", "原照片目录不存在！")
            return

        src_real = os.path.realpath(source)
        tgt_real = os.path.realpath(target)

        if src_real == tgt_real:
            messagebox.showerror(
                "错误",
                "目标目录不能与原目录相同！\n否则分类结果会被再次分类。\n请选择另一个目录。"
            )
            return

        # 目标目录可用性检查
        try:
            os.makedirs(target, exist_ok=True)
            probe = os.path.join(target, ".write_test.tmp")
            with open(probe, "w", encoding="utf-8") as f:
                f.write("ok")
            os.remove(probe)
        except Exception as e:
            messagebox.showerror("错误", f"目标目录不可写：\n{target}\n\n{e}")
            return

        self.is_processing = True
        self.cancel_event.clear()
        self._set_running(True)
        self.progress_value.set(0)

        # 清空日志
        self.log_text.configure(state=tk.NORMAL)
        self.log_text.delete("1.0", tk.END)
        self.log_text.configure(state=tk.DISABLED)

        threading.Thread(target=self.process_files, daemon=True).start()

    def cancel_process(self):
        if self.is_processing:
            self.cancel_event.set()
            self.set_status("正在取消…（当前文件处理完后中止）")
            self.gui_log("⏹ 用户请求取消，正在安全中止…")

    def exit_app(self):
        if self.is_processing:
            if not messagebox.askyesno("确认", "正在处理中，确定要退出吗？\n（后台任务将被中止）"):
                return
            self.cancel_event.set()
        self._window_alive = False
        try:
            self.root.destroy()
        except tk.TclError:
            pass

    def _set_running(self, running):
        def _apply():
            self.btn_start.configure(state=tk.DISABLED if running else tk.NORMAL)
            self.btn_cancel.configure(state=tk.NORMAL if running else tk.DISABLED)
        self._ui(_apply)

    # ──────────────────────────────────────
    #  日期解析（严格校验版）
    # ──────────────────────────────────────
    @staticmethod
    def parse_date_folder(date_str, mode='ym'):
        """
        将日期字符串解析为文件夹名。
        mode='ym'  -> '202403'
        mode='ymd' -> '20240315'
        非法/缺失返回 None（不再产出 000000 / 202431 / 20241301 之类垃圾目录）
        """
        if not date_str:
            return None
        s = str(date_str).strip()
        if not s:
            return None

        # 去掉时区后缀（+08:00 / +0800 / Z）与毫秒
        s = re.sub(r'([+-]\d{2}:?\d{2}|Z)$', '', s).strip()
        s = re.sub(r'\.\d+$', '', s).strip()

        # 明确排除全零伪日期
        if re.match(r'^0{2,4}[:/\-]?0{0,2}[:/\-]?0{0,2}', s):
            return None

        dt = None
        # (格式, 需要的最小长度) —— 长度按格式实际字符数精确给出，避免切口错位
        candidates = (
            ('%Y:%m:%d %H:%M:%S', 19),
            ('%Y-%m-%d %H:%M:%S', 19),
            ('%Y:%m:%d %H:%M', 16),
            ('%Y-%m-%d %H:%M', 16),
            ('%Y:%m:%d', 10),
            ('%Y-%m-%d', 10),
            ('%Y%m%d', 8),
            ('%Y%m', 6),
        )
        for fmt, need in candidates:
            if len(s) < need:
                continue
            try:
                dt = datetime.strptime(s[:need], fmt)
                break
            except ValueError:
                continue

        if dt is None:
            return None

        # 年份合法性校验
        if not (1970 <= dt.year <= 2100):
            return None

        if mode == 'ymd':
            return dt.strftime('%Y%m%d')
        return dt.strftime('%Y%m')

    # ──────────────────────────────────────
    #  核心处理
    # ──────────────────────────────────────
    def process_files(self):
        log_lines = []
        try:
            self._process_files_inner(log_lines)
        except Exception:
            tb = traceback.format_exc()
            msg = f"❌ 处理过程中发生未捕获异常:\n{tb}"
            print(msg, flush=True)
            log_lines.append(msg)
            self.gui_log("❌ 发生未捕获异常，详见控制台")
            self._ui(lambda: messagebox.showerror("异常", f"处理中断：\n{tb.splitlines()[-1]}"))
        finally:
            self.is_processing = False
            self._set_running(False)
            self.update_progress(100 if not self.cancel_event.is_set() else self.progress_value.get())

    def _process_files_inner(self, log_lines):
        source = self.source_dir.get()
        target = self.target_dir.get()
        mode = self.classify_mode.get()
        skip_existing = self.skip_existing.get()
        mode_desc = "年-月" if mode == "ym" else "年-月-日"

        media_exts = self.PHOTO_EXTS | self.VIDEO_EXTS
        tgt_real = os.path.realpath(target)

        # ── 1. 扫描文件（排除目标目录本身，避免重复分类自己的产物） ──
        self.set_status("正在扫描文件…")
        self.gui_log("正在扫描文件…")
        all_files = []
        pruned_dirs = 0
        for dirpath, dirnames, filenames in os.walk(source):
            # 剪掉目标目录分支
            keep = []
            for d in dirnames:
                if os.path.realpath(os.path.join(dirpath, d)) == tgt_real:
                    pruned_dirs += 1
                    continue
                keep.append(d)
            dirnames[:] = keep
            if os.path.realpath(dirpath) == tgt_real:
                continue
            for fname in filenames:
                all_files.append(os.path.join(dirpath, fname))

        total_files = len(all_files)
        if total_files == 0:
            self.gui_log("源目录中没有文件！")
            self._ui(lambda: messagebox.showinfo("提示", "源目录中没有文件！"))
            return

        media_files = [f for f in all_files
                       if os.path.splitext(f)[1].lower() in media_exts]
        unsupported = [f for f in all_files if f not in media_files]

        self.gui_log(f"共发现 {total_files} 个文件，其中媒体文件 {len(media_files)} 个"
                     f"（跳过 {len(unsupported)} 个非媒体文件）")
        if pruned_dirs:
            self.gui_log(f"ℹ 已排除目标目录分支 {pruned_dirs} 处，避免重复处理分类产物")

        if not media_files:
            self.gui_log("没有可处理的媒体文件。")
            self._ui(lambda: messagebox.showinfo("提示", "源目录中没有可处理的照片/视频！"))
            return

        # ── 2. 分批读取元数据（0% ~ 35% 进度） ──
        self.set_status("正在读取元数据…")
        self.gui_log(f"分类模式: {mode_desc}，开始分批读取元数据"
                     f"（每批 {self.BATCH_SIZE} 个）…")
        exif_map, failed_batches = self._read_metadata_batched(media_files)
        if self.cancel_event.is_set():
            self.gui_log("⏹ 已取消（元数据读取阶段）")
            return
        if failed_batches:
            self.gui_log(f"⚠ 有 {failed_batches} 个批次读取失败，"
                         f"相关文件将退回文件修改时间兜底")

        # ── 3. 准备日志 ──
        now = datetime.now()
        log_filename = now.strftime("%Y%m%d_%H%M%S") + "_log.txt"
        log_path = os.path.join(target, log_filename)

        def log(msg):
            print(msg, flush=True)
            log_lines.append(msg)
            self.gui_log(msg)

        log("=" * 70)
        log("照片/视频分类处理日志 (v2)")
        log(f"处理时间: {now.strftime('%Y-%m-%d %H:%M:%S')}")
        log(f"源目录:   {source}")
        log(f"目标目录: {target}")
        log(f"分类模式: {mode_desc}")
        log(f"跳过已存在: {'是' if skip_existing else '否'}")
        log(f"文件总数: {total_files}（媒体 {len(media_files)}）")
        log("=" * 70)

        # ── 4. 逐文件处理（35% ~ 100% 进度） ──
        processed = 0
        skipped_exists = 0
        failed = []
        unsupported_cnt = len(unsupported)
        no_date = []
        mtime_fallback = 0

        total = len(media_files)
        for idx, filepath in enumerate(media_files, 1):
            if self.cancel_event.is_set():
                log("\n⏹ 用户取消，已中止后续处理。")
                break

            self.update_progress(35 + (idx / total) * 65)

            filename = os.path.basename(filepath)
            meta = exif_map.get(self._key(filepath))

            # 多级回退取日期，并记录日期来源
            shoot_date, date_source = self._pick_date(meta)

            if not shoot_date:
                try:
                    shoot_date = datetime.fromtimestamp(
                        os.path.getmtime(filepath)).strftime('%Y:%m:%d %H:%M:%S')
                    date_source = "mtime兜底"
                    mtime_fallback += 1
                except Exception:
                    no_date.append(filename)
                    log(f"[{idx:>5}] ✖ {filename} - 无法获取任何日期信息")
                    continue

            date_folder = self.parse_date_folder(shoot_date, mode)
            if not date_folder:
                try:
                    mtime = datetime.fromtimestamp(os.path.getmtime(filepath))
                    if not (1970 <= mtime.year <= 2100):
                        raise ValueError("mtime 越界")
                    date_folder = mtime.strftime('%Y%m') if mode == 'ym' else mtime.strftime('%Y%m%d')
                    date_source = "mtime兜底"
                    mtime_fallback += 1
                except Exception:
                    no_date.append(filename)
                    log(f"[{idx:>5}] ✖ {filename} - 日期解析失败 (原始值: {shoot_date!r})")
                    continue

            target_subdir = os.path.join(target, date_folder)
            os.makedirs(target_subdir, exist_ok=True)
            plain_dest = os.path.join(target_subdir, filename)

            # 已存在判断：同名 + 同大小 视为同一文件
            if os.path.exists(plain_dest) and skip_existing:
                try:
                    if os.path.getsize(plain_dest) == os.path.getsize(filepath):
                        skipped_exists += 1
                        log(f"[{idx:>5}] ⏭ {filename} - 已存在同名同大小文件，跳过")
                        continue
                except OSError:
                    pass

            dest_path = self.get_unique_path(plain_dest)

            try:
                shutil.copy2(filepath, dest_path)
                processed += 1
                dest_display = os.path.relpath(dest_path, target)
                warn = " ⚠日期来自mtime" if date_source == "mtime兜底" else ""
                log(f"[{idx:>5}] ✔ {filename}")
                log(f"        日期: {shoot_date} (来源: {date_source}){warn}")
                log(f"        拷贝到: {dest_display}")
            except Exception as e:
                failed.append((filename, f"复制失败: {e}"))
                log(f"[{idx:>5}] ✖ {filename} - 复制失败: {e}")

        # ── 5. 统计与日志落盘 ──
        cancelled = self.cancel_event.is_set()
        log("\n" + "=" * 70)
        log("处理完成统计:" + ("（用户已取消）" if cancelled else ""))
        log(f"  分类模式:     {mode_desc}")
        log(f"  文件总数:     {total_files}")
        log(f"  媒体文件:     {total}")
        log(f"  已处理:       {processed}")
        log(f"  已跳过(存在): {skipped_exists}")
        log(f"  非媒体文件:   {unsupported_cnt}")
        log(f"  无日期信息:   {len(no_date)}")
        log(f"  复制失败:     {len(failed)}")
        if mtime_fallback:
            log(f"  ⚠ mtime兜底:  {mtime_fallback}（日期来自文件修改时间，可能不准）")
        log("=" * 70)

        if failed:
            log(f"\n复制失败明细 ({len(failed)} 个):")
            log("-" * 50)
            for i, (fname, reason) in enumerate(failed, 1):
                log(f"  {i:>4}. {fname} | {reason}")
            log("-" * 50)

        if no_date:
            log(f"\n无日期信息明细 ({len(no_date)} 个):")
            log("-" * 50)
            for i, fname in enumerate(no_date, 1):
                log(f"  {i:>4}. {fname}")
            log("-" * 50)

        log(f"\n日志文件: {log_path}")
        log(f"处理结束时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")

        log_ok = True
        try:
            with open(log_path, 'w', encoding='utf-8') as f:
                f.write('\n'.join(log_lines))
        except Exception as e:
            log_ok = False
            self.gui_log(f"⚠ 写入日志文件失败: {e}")

        self.update_progress(0 if cancelled else 100)
        self.set_status("已取消" if cancelled else "处理完成")

        summary = (
            f"{'处理已取消' if cancelled else '处理完成'}！\n\n"
            f"分类模式: {mode_desc}\n"
            f"文件总数: {total_files}\n"
            f"已处理:   {processed}\n"
            f"已跳过:   {skipped_exists}\n"
            f"复制失败: {len(failed)}\n"
            f"无日期:   {len(no_date)}\n\n"
            f"日志已保存至:\n{log_path if log_ok else '（写入失败，见界面日志）'}"
        )
        self._ui(lambda: messagebox.showinfo("处理结果", summary))

    # ──────────────────────────────────────
    #  元数据读取
    # ──────────────────────────────────────
    @staticmethod
    def _key(path):
        """统一索引键：修正分隔符与大小写（Windows 大小写不敏感）"""
        return os.path.normcase(os.path.normpath(os.path.abspath(path)))

    def _pick_date(self, meta):
        """从元数据按回退链取拍摄日期，返回 (日期字符串, 来源字段)"""
        if not meta:
            return None, None
        for field in self.DATE_FIELDS:
            val = (meta.get(field) or '')
            val = str(val).strip()
            if val and val != '0000:00:00 00:00:00':
                return val, field
        return None, None

    def _read_metadata_batched(self, media_files):
        """分批调用 exiftool，单批失败不拖垮整体。返回 (exif_map, failed_batch_count)"""
        exif_map = {}
        failed = 0
        total = len(media_files)
        for start in range(0, total, self.BATCH_SIZE):
            if self.cancel_event.is_set():
                break
            chunk = media_files[start:start + self.BATCH_SIZE]
            data = self._run_exiftool(chunk)
            if data:
                for item in data:
                    src = item.get('SourceFile', '')
                    if src:
                        exif_map[self._key(src)] = item
            else:
                failed += 1
                self.gui_log(f"⚠ 第 {start // self.BATCH_SIZE + 1} 批元数据读取失败"
                             f"（{len(chunk)} 个文件），这批将使用文件时间兜底")
            done = min(start + len(chunk), total)
            # 读取阶段映射到 0% ~ 35%
            self.update_progress(done / total * 35)
            self.set_status(f"读取元数据 {done}/{total}…")
        return exif_map, failed

    def _run_exiftool(self, files):
        """读取一批文件的元数据；-api QuickTimeUTC 让视频时间以本地时间返回"""
        if not files:
            return None

        args = [
            'exiftool', '-json', '-charset', 'filename=utf8',
            '-api', 'QuickTimeUTC',
            '-d', '%Y:%m:%d %H:%M:%S',
            '-DateTimeOriginal', '-CreateDate', '-MediaCreateDate',
            '-TrackCreateDate', '-FileCreateDate', '-FileModifyDate', '-FileType',
        ]

        # 参数过长（Windows 命令行上限）或文件过多时用 -@ 参数文件
        argfile = None
        joined_len = sum(len(f) + 1 for f in files) + 200
        use_argfile = IS_WIN or joined_len > 20000 or any(
            os.path.basename(f).startswith(('#', '-')) for f in files
        )
        try:
            if use_argfile:
                fd, argfile = tempfile.mkstemp(suffix=".txt", prefix="exifargs_")
                with os.fdopen(fd, 'w', encoding='utf-8', newline='\n') as f:
                    for path in files:
                        f.write(path.replace('\n', ' ') + '\n')
                cmd = args + ['-@', argfile]
            else:
                cmd = args + list(files)

            result = subprocess.run(
                cmd, capture_output=True, timeout=self.BATCH_TIMEOUT,
                encoding='utf-8', errors='replace',
                creationflags=subprocess.CREATE_NO_WINDOW if IS_WIN else 0,
            )
            if result.returncode == 0 or result.stdout.strip():
                try:
                    return json.loads(result.stdout)
                except json.JSONDecodeError as e:
                    self.gui_log(f"⚠ exiftool 输出解析失败: {e}")
                    return None
            self.gui_log(f"⚠ exiftool 返回错误: {result.stderr.strip()[:200]}")
            return None
        except FileNotFoundError:
            self.gui_log("❌ 未找到 exiftool，请确保已安装并添加到 PATH")
            self._ui(lambda: messagebox.showerror(
                "错误", "exiftool 未安装或调用失败！\n请确保 exiftool 在系统 PATH 中。"))
            self.cancel_event.set()
            return None
        except subprocess.TimeoutExpired:
            self.gui_log(f"⚠ exiftool 读取超时（>{self.BATCH_TIMEOUT}s）")
            return None
        except Exception as e:
            self.gui_log(f"⚠ 调用 exiftool 失败: {e}")
            return None
        finally:
            if argfile and os.path.exists(argfile):
                try:
                    os.remove(argfile)
                except OSError:
                    pass

    # ──────────────────────────────────────
    #  工具方法
    # ──────────────────────────────────────
    @staticmethod
    def get_unique_path(filepath):
        if not os.path.exists(filepath):
            return filepath
        base, ext = os.path.splitext(filepath)
        counter = 1
        while os.path.exists(f"{base}_{counter}{ext}"):
            counter += 1
        return f"{base}_{counter}{ext}"


def main():
    root = tk.Tk()
    if IS_WIN:
        try:
            from ctypes import windll
            windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
    PhotoClassifierApp(root)
    root.mainloop()


if __name__ == '__main__':
    main()
