#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
照片/视频按 GPS地点+日期 分类工具 (ttk + clam 风格) - 修复版 v2
目录结构：国家/城市/年月日 (无GPS则放入 其他/年月日)
支持视频 GPS 提取 (GPSCoordinates) 及 UTC 时间自动校正
仅中国大陆转GCJ-02；港澳台及海外保持WGS-84；增强行政区划兜底

【本版修复项（设计报告评审 P1/P2，P1-5 Key明文存储按要求保留）】
  1. [P1-1] 视频时间校正改由 exiftool -api QuickTimeUTC 在源头完成，
            删除"一律按UTC+本机偏移"的错误假设（iPhone等设备视频多为本地时间，
            且 now()-utcnow() 在夏令时区会错1小时）
  2. [P1-2] GPSCoordinates 经纬序判别：按 XMP 规范默认"纬度 经度"，
            仅在该顺序值域校验失败时才对调，消除赤道/子午线附近的误判带
  3. [P1-3] process_files 增加顶层异常兜底，任何未捕获异常都会写日志并恢复UI，
            不再出现"按钮永久禁用只能重启"
  4. [P1-4] 新增"取消处理"按钮，工作线程循环每步检查取消标志，可安全中止
  5. [P1-6] exiftool 超时由 600s 放宽到 1800s；超时/报错时保留已捕获的部分结果
  6. [P2]   消除 from tkinter import * 通配导入，改为显式 tk.* 引用
  7. [P2]   跨平台字体适配（Windows: 微软雅黑/Consolas；macOS: PingFang SC/Menlo）
  8. [P2]   进度条改为按文件字节量加权，大小文件混布时节奏真实
  9. [P2]   regeo 增加重试（2次，0.5s退避）
 10. [P2]   exif_map 键改用 normcase+normpath，修复 Windows 大小写路径失配
 11. [P2]   新增"跳过已存在文件"选项，勾选后目标已有同名文件时跳过而非生成 _1/_2
 12. [P2]   日志标注每个文件的日期来源（DateTimeOriginal/mtime 等），弱来源可溯源
 13. [P2]   日志写盘失败不再静默，输出警告
"""
# pyinstaller -F photo_gps_classifier5.py

import os
import sys
import subprocess
import json
import shutil
import math
import re
import platform
import traceback
import requests
from datetime import datetime
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog
from tkinter import ttk
from tkinter import scrolledtext
import threading

def _config_path():
    if getattr(sys, "frozen", False):          # pyinstaller
        base = os.path.dirname(os.path.abspath(sys.executable))
    else:
        base = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base, "exif_viewer_config.json")

# 统一灰色背景色常量
BG_COLOR = "#D9D9D9"
# CONFIG_FILE = "exif_viewer_config.json"
# CONFIG_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "exif_viewer_config.json")
CONFIG_FILE = _config_path()
#print(CONFIG_FILE)

IS_WIN = platform.system() == "Windows"
IS_MAC = platform.system() == "Darwin"
# 跨平台字体：Windows 用微软雅黑/Consolas，macOS 用苹方/Menlo，Linux 回退 sans-serif
UI_FONT = "Microsoft YaHei" if IS_WIN else ("PingFang SC" if IS_MAC else "Sans")
LOG_FONT = "Consolas" if IS_WIN else ("Menlo" if IS_MAC else "Monospace")

# ===================== 坐标转换算法 (WGS-84 转 GCJ-02) =====================
PI = math.pi
A = 6378245.0
EE = 0.00669342162296594323


def _transform_lat(lng, lat):
    ret = -100.0 + 2.0 * lng + 3.0 * lat + 0.2 * lat * lat + 0.1 * lng * lat + 0.2 * math.sqrt(abs(lng))
    ret += (20.0 * math.sin(6.0 * lng * PI) + 20.0 * math.sin(2.0 * lng * PI)) * 2.0 / 3.0
    ret += (20.0 * math.sin(lat * PI) + 40.0 * math.sin(lat / 3.0 * PI)) * 2.0 / 3.0
    ret += (160.0 * math.sin(lat / 12.0 * PI) + 320 * math.sin(lat * PI / 30.0)) * 2.0 / 3.0
    return ret


def _transform_lng(lng, lat):
    ret = 300.0 + lng + 2.0 * lat + 0.1 * lng * lng + 0.1 * lng * lat + 0.1 * math.sqrt(abs(lng))
    ret += (20.0 * math.sin(6.0 * lng * PI) + 20.0 * math.sin(2.0 * lng * PI)) * 2.0 / 3.0
    ret += (20.0 * math.sin(lng * PI) + 40.0 * math.sin(lng / 3.0 * PI)) * 2.0 / 3.0
    ret += (150.0 * math.sin(lng / 12.0 * PI) + 300.0 * math.sin(lng / 30.0 * PI)) * 2.0 / 3.0
    return ret


def wgs84_to_gcj02(lng, lat):
    dlat = _transform_lat(lng - 105.0, lat - 35.0)
    dlng = _transform_lng(lng - 105.0, lat - 35.0)
    radlat = lat / 180.0 * PI
    magic = math.sin(radlat)
    magic = 1 - EE * magic * magic
    sqrtmagic = math.sqrt(magic)
    dlat = (dlat * 180.0) / ((A * (1 - EE)) / (magic * sqrtmagic) * PI)
    dlng = (dlng * 180.0) / (A / sqrtmagic * math.cos(radlat) * PI)
    return lng + dlng, lat + dlat


def _is_in_china_mainland(lng, lat):
    """
    粗略判断坐标是否在中国大陆境内（不含港澳台）
    仅大陆需要 WGS84->GCJ02 转换，港澳台及海外保持 WGS84
    """
    if not (73.66 < lng < 135.05 and 3.86 < lat < 53.55):
        return False
    # 排除港澳区域
    if 113.5 <= lng <= 114.5 and 22.0 <= lat <= 22.7:
        return False
    # 排除台湾区域
    if 119.5 <= lng <= 122.5 and 21.5 <= lat <= 25.5:
        return False
    return True


# ===========================================================================


class PhotoClassifierApp:
    def __init__(self, root):
        self.root = root
        self.root.title("照片/视频按 GPS地点+日期 分类工具")
        self.root.geometry("720x680")
        self.root.resizable(True, True)
        self.root.configure(bg=BG_COLOR)

        style = ttk.Style()
        style.theme_use("clam")
        style.configure(".", background=BG_COLOR, font=(UI_FONT, 11))
        style.configure("TFrame", background=BG_COLOR)
        style.configure("TLabel", background=BG_COLOR)
        style.configure("TButton", background=BG_COLOR)
        style.configure("TRadiobutton", background=BG_COLOR)
        style.configure("TCheckbutton", background=BG_COLOR)
        style.configure("TLabelframe", background=BG_COLOR)
        style.configure("TLabelframe.Label", background=BG_COLOR)
        style.configure("TEntry", fieldbackground=BG_COLOR, background=BG_COLOR)
        style.configure("Horizontal.TProgressbar", troughcolor=BG_COLOR, background="#6C9E6C")

        self.source_dir = tk.StringVar()
        self.target_dir = tk.StringVar()
        self.amap_key = tk.StringVar()
        self.key_status_var = tk.StringVar(value="⚠️ 未配置高德Key")
        self.classify_mode = tk.StringVar(value="ymd")
        # 新增：跳过已存在文件选项（勾选后目标目录已有同名文件时跳过，不生成 _1/_2）
        self.skip_existing = tk.BooleanVar(value=False)
        self.progress_value = tk.DoubleVar(value=0)
        self.is_processing = False
        self.location_cache = {}
        # 新增：任务取消标志，工作线程循环中检查
        self.cancel_flag = threading.Event()

        self._load_config()
        self._build_ui()

    def _load_config(self):
        if os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, 'r', encoding='utf-8') as f:
                    cfg = json.load(f)
                    self.amap_key.set(cfg.get("amap_key", ""))
            except Exception:
                pass
        self._update_key_status()

    def _save_config(self):
        config_data = {"amap_key": self.amap_key.get()}
        try:
            with open(CONFIG_FILE, 'w', encoding='utf-8') as f:
                json.dump(config_data, f, indent=2, ensure_ascii=False)
        except Exception as e:
            messagebox.showerror("保存失败", f"无法写入配置文件:\n{e}")

    def _update_key_status(self):
        key = self.amap_key.get()
        if key:
            masked = f"{key[:4]}...{key[-4:]}" if len(key) > 8 else "***"
            self.key_status_var.set(f"✅ 已配置 ({masked})")
        else:
            self.key_status_var.set("⚠️ 未配置高德Key (请点击右侧按钮设置)")

    def _set_amap_key(self):
        current_key = self.amap_key.get()
        new_key = simpledialog.askstring(
            "设置高德 Web服务 API Key",
            "请输入新的高德 API Key:\n(留空并确定则清除现有 Key)",
            parent=self.root,
            initialvalue=current_key
        )
        if new_key is None:
            return
        new_key = new_key.strip()

        if new_key:
            self.root.config(cursor="watch")
            self.root.update_idletasks()
            try:
                test_url = "https://restapi.amap.com/v3/geocode/regeo"
                params = {"key": new_key, "location": "116.397428,39.90923", "extensions": "base"}
                resp = requests.get(test_url, params=params, timeout=5)
                data = resp.json()
                if data.get("status") != "1":
                    info = data.get("info", "未知错误")
                    infocode = data.get("infocode", "")
                    messagebox.showerror("Key 验证失败",
                                         f"高德 API 返回错误：\n{info} (代码: {infocode})\n\n请检查 Key 是否正确，或是否绑定了 Web服务。")
                    self.root.config(cursor="")
                    return
            except Exception as e:
                messagebox.showerror("网络错误", f"无法连接高德服务器验证 Key:\n{e}")
                self.root.config(cursor="")
                return
            finally:
                self.root.config(cursor="")

        self.amap_key.set(new_key)
        self._save_config()
        self._update_key_status()

        if new_key:
            messagebox.showinfo("成功", "✅ 高德 API Key 已保存并验证通过！")
        else:
            messagebox.showwarning("提示", "⚠️ 高德 API Key 已清除。")

    def _build_ui(self):
        frame1 = ttk.Frame(self.root, padding=10)
        frame1.pack(fill="x")
        ttk.Label(frame1, text="原照片目录:", width=12, anchor='e').pack(side="left")
        ttk.Entry(frame1, textvariable=self.source_dir, width=48).pack(side="left", padx=5)
        ttk.Button(frame1, text="选择原目录", command=self.select_source, padding=(12, 4)).pack(side="left")

        frame2 = ttk.Frame(self.root, padding=10)
        frame2.pack(fill="x")
        ttk.Label(frame2, text="目标目录:", width=12, anchor='e').pack(side="left")
        ttk.Entry(frame2, textvariable=self.target_dir, width=48).pack(side="left", padx=5)
        ttk.Button(frame2, text="选择目标目录", command=self.select_target, padding=(12, 4)).pack(side="left")

        frame_key = ttk.Frame(self.root, padding=10)
        frame_key.pack(fill="x")
        ttk.Label(frame_key, text="高德API Key:", width=12, anchor='e').pack(side="left")
        self.key_status_label = ttk.Label(frame_key, textvariable=self.key_status_var, foreground="#006600", width=35, anchor='w')
        self.key_status_label.pack(side="left", padx=5)
        ttk.Button(frame_key, text="🔑 设置高德Key", command=self._set_amap_key, padding=(12, 4)).pack(side="left")

        mode_frame = ttk.LabelFrame(self.root, text="日期文件夹格式 (地点目录自动为: 国家/城市/)", padding=10)
        mode_frame.pack(fill="x", padx=10, pady=(6, 2))
        ttk.Radiobutton(mode_frame, text="按 年-月 分类 (例: 202403)", variable=self.classify_mode, value="ym").pack(side="left", padx=20)
        ttk.Radiobutton(mode_frame, text="按 年-月-日 分类 (例: 20240315)", variable=self.classify_mode, value="ymd").pack(side="left", padx=20)
        # 新增：跳过已存在文件
        ttk.Checkbutton(mode_frame, text="跳过已存在文件", variable=self.skip_existing).pack(side="left", padx=20)

        frame3 = ttk.Frame(self.root, padding=10)
        frame3.pack(fill="x")
        self.progress = ttk.Progressbar(frame3, variable=self.progress_value, maximum=100)
        self.progress.pack(fill="x", expand=True)

        frame4 = ttk.Frame(self.root, padding=(10, 5))
        frame4.pack(fill="x")
        self.btn_start = ttk.Button(frame4, text="开始处理", command=self.start_process, padding=(20, 7))
        self.btn_start.pack(side="left", padx=40)
        # 新增：取消处理按钮
        self.btn_cancel = ttk.Button(frame4, text="取消处理", command=self.cancel_process, padding=(20, 7), state="disabled")
        self.btn_cancel.pack(side="left", padx=0)
        self.btn_exit = ttk.Button(frame4, text="退出程序", command=self.exit_app, padding=(20, 7))
        self.btn_exit.pack(side="right", padx=40)

        log_frame = ttk.LabelFrame(self.root, text="实时处理日志", padding=5)
        log_frame.pack(fill="both", expand=True, padx=10, pady=5)
        self.log_text = scrolledtext.ScrolledText(
            log_frame, height=10, font=(LOG_FONT, 10),
            bg="#F5F5F5", fg="#333333", insertbackground="black", state=tk.DISABLED
        )
        self.log_text.pack(fill="both", expand=True)

    def gui_log(self, msg):
        def _append():
            self.log_text.config(state=tk.NORMAL)
            self.log_text.insert(tk.END, msg + "\n")
            self.log_text.see(tk.END)
            self.log_text.config(state=tk.DISABLED)
        self.root.after(0, _append)

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
        if not self.source_dir.get() or not os.path.isdir(self.source_dir.get()):
            messagebox.showerror("错误", "请选择有效的原照片目录！")
            return
        if not self.target_dir.get():
            messagebox.showerror("错误", "请选择目标目录！")
            return
        if not self.amap_key.get().strip():
            messagebox.showerror("错误", "未配置高德 API Key！\n请点击 [🔑 设置高德Key] 进行配置。")
            return

        self.is_processing = True
        self.cancel_flag.clear()
        self.btn_start.config(state="disabled")
        self.btn_cancel.config(state="normal")
        self.progress_value.set(0)
        self.location_cache.clear()

        self.log_text.config(state=tk.NORMAL)
        self.log_text.delete(1.0, tk.END)
        self.log_text.config(state=tk.DISABLED)

        threading.Thread(target=self.process_files, daemon=True).start()

    def cancel_process(self):
        """设置取消标志，工作线程在下一个文件处安全中止"""
        if self.is_processing:
            self.cancel_flag.set()
            self.btn_cancel.config(state="disabled")
            self.gui_log("⏹ 已请求取消，正在等待当前文件处理完成...")

    def exit_app(self):
        if self.is_processing:
            if not messagebox.askyesno("确认", "正在处理中，确定要退出吗？"):
                return
        self.root.destroy()

    def process_files(self):
        """工作线程入口：带顶层异常兜底，任何错误都会写日志并恢复 UI"""
        try:
            self._process_files_inner()
        except Exception as e:
            traceback.print_exc()
            self.gui_log(f"✖ 发生未预期的错误，任务终止: {type(e).__name__}: {e}")
        finally:
            self.root.after(0, self.reset_ui)

    def _process_files_inner(self):
        source = self.source_dir.get()
        target = self.target_dir.get()
        mode = self.classify_mode.get()
        api_key = self.amap_key.get().strip()
        skip_existing = self.skip_existing.get()

        photo_exts = {'.jpg', '.jpeg', '.png', '.gif', '.bmp', '.tiff', '.tif', '.raw',
                      '.cr2', '.cr3', '.nef', '.arw', '.orf', '.rw2', '.heic', '.heif','.hif',
                      '.webp', '.dng', '.pef', '.srw', '.raf', '.dcr'}
        video_exts = {'.mp4', '.avi', '.mov', '.mkv', '.wmv', '.flv', '.webm', '.m4v',
                      '.mpg', '.mpeg', '.3gp', '.ts', '.mts', '.m2ts', '.vob'}
        media_exts = photo_exts | video_exts

        self.gui_log("正在扫描文件...")

        all_files = []
        total_size = 0  # 按字节量加权计算进度
        for dirpath, _, filenames in os.walk(source):
            for fname in filenames:
                fp = os.path.join(dirpath, fname)
                all_files.append(fp)
                try:
                    total_size += os.path.getsize(fp)
                except Exception:
                    pass

        total_files = len(all_files)
        if total_files == 0:
            self.gui_log("源目录中没有文件！")
            return
        if total_size == 0:
            total_size = 1  # 防止除零

        self.gui_log(f"共发现 {total_files} 个文件，正在调用 exiftool 读取照片及视频数据...")

        exif_data = self.run_exiftool(source)
        if exif_data is None:
            self.root.after(0, lambda: messagebox.showerror("错误",
                                                            "exiftool 调用失败！请确保已安装 exiftool 并加入环境变量。"))
            return

        # 键使用 normcase+normpath：修复 Windows 下大小写不同的路径失配问题
        exif_map = {os.path.normcase(os.path.normpath(item.get('SourceFile', ''))): item for item in exif_data}

        now = datetime.now()
        log_filename = now.strftime("%Y%m%d_%H%M%S") + "_log.txt"
        log_path = os.path.join(target, log_filename)
        os.makedirs(target, exist_ok=True)

        processed_count = 0
        skipped_existing_count = 0
        unprocessed_list = []
        log_lines = []

        def log(msg):
            print(msg, flush=True)
            log_lines.append(msg)
            self.gui_log(msg)

        log(f"{'=' * 50}")
        log(f"处理时间: {now.strftime('%Y-%m-%d %H:%M:%S')}")
        log(f"源目录: {source}")
        log(f"目标目录: {target}")
        log(f"跳过已存在: {'是' if skip_existing else '否'}")
        log(f"{'=' * 50}")

        last_progress_print = 0
        processed_size = 0  # 累计已处理字节数
        cancelled = False

        for idx, filepath in enumerate(all_files, 1):
            # 取消检查：每个文件处理前检查一次
            if self.cancel_flag.is_set():
                cancelled = True
                log(f"⏹ 任务已取消（已完成 {idx - 1}/{total_files} 个文件）")
                break

            try:
                processed_size += os.path.getsize(filepath)
            except Exception:
                pass
            current_progress = (processed_size / total_size) * 100
            self.update_progress(min(current_progress, 100.0))

            if current_progress - last_progress_print >= 5:
                print(f"--> 处理进度: {current_progress:.1f}% ({idx}/{total_files})", flush=True)
                last_progress_print = current_progress

            filename = os.path.basename(filepath)
            ext = os.path.splitext(filename)[1].lower()

            if ext not in media_exts:
                unprocessed_list.append((filename, "非支持的媒体格式"))
                log(f"[{idx:>5}] ⚠ 跳过 {filename} (非支持的媒体格式)")
                continue

            meta = exif_map.get(os.path.normcase(os.path.normpath(filepath)))
            is_video = ext in video_exts

            # 1. 解析日期（记录来源，便于溯源弱来源日期）
            shoot_date = None
            date_source = None
            if meta:
                date_fields = ('DateTimeOriginal', 'CreateDate', 'MediaCreateDate', 'TrackCreateDate', 'FileModifyDate')
                for field in date_fields:
                    val = (meta.get(field) or '').strip()
                    if val and val != '0000:00:00 00:00:00':
                        shoot_date = val
                        date_source = field
                        break

            if not shoot_date:
                try:
                    shoot_date = datetime.fromtimestamp(os.path.getmtime(filepath)).strftime('%Y:%m:%d %H:%M:%S')
                    date_source = '文件修改时间(mtime)'
                except Exception:
                    unprocessed_list.append((filename, "无法获取任何日期信息"))
                    log(f"[{idx:>5}] ✖ 失败 {filename} (无法获取任何日期信息)")
                    continue

            # 视频时间校正已由 exiftool -api QuickTimeUTC 在读取阶段完成（见 run_exiftool），
            # 此处不再做"一律按UTC+本机偏移"的人工偏移

            date_folder = self.parse_date_folder(shoot_date, mode)
            if not date_folder:
                try:
                    mtime = datetime.fromtimestamp(os.path.getmtime(filepath))
                    date_folder = mtime.strftime('%Y%m') if mode == 'ym' else mtime.strftime('%Y%m%d')
                    date_source += '→mtime兜底'
                except Exception:
                    unprocessed_list.append((filename, "日期解析失败"))
                    log(f"[{idx:>5}] ✖ 失败 {filename} (日期解析失败)")
                    continue

            # 2. 解析 GPS
            country, city = "其他", "其他"
            if meta:
                lat, lon = self.extract_gps(meta)
                if lat is not None and lon is not None:
                    c, ci = self.get_location_from_amap(lon, lat, api_key)
                    if c and ci:
                        country, city = c, ci

            country = self.sanitize_dir_name(country)
            city = self.sanitize_dir_name(city)

            if country == "其他" and city == "其他":
                target_subdir = os.path.join(target, "其他", date_folder)
            else:
                target_subdir = os.path.join(target, country, city, date_folder)

            try:
                os.makedirs(target_subdir, exist_ok=True)
                dest_path = os.path.join(target_subdir, filename)

                # 跳过已存在选项
                if skip_existing and os.path.exists(dest_path):
                    skipped_existing_count += 1
                    log(f"[{idx:>5}] ⇢ 跳过 {filename} (目标已存在)")
                    continue

                dest_path = self.get_unique_path(dest_path)
                shutil.copy2(filepath, dest_path)
                processed_count += 1
                dest_display = os.path.relpath(dest_path, target)
                log(f"[{idx:>5}] ✔ {filename} -> {dest_display} (日期来源: {date_source})")
            except Exception as e:
                unprocessed_list.append((filename, f"复制失败: {e}"))
                log(f"[{idx:>5}] ✖ 失败 {filename} (复制失败: {e})")

        log(f"\n{'=' * 50}")
        log("处理完成统计:")
        log(f"  文件总数:   {total_files}")
        log(f"  成功处理:   {processed_count}")
        if skip_existing:
            log(f"  跳过已存在: {skipped_existing_count}")
        log(f"  未处理数:   {len(unprocessed_list)}")
        if cancelled:
            log(f"  ⏹ 状态: 已被用户取消")
        log(f"{'=' * 50}")

        if unprocessed_list:
            log(f"\n⚠ 未处理文件详细列表 ({len(unprocessed_list)} 个):")
            log(f"{'-' * 40}")
            for i, (fname, reason) in enumerate(unprocessed_list, 1):
                log(f"  {i:>4}. {fname} | 原因: {reason}")
            log(f"{'-' * 40}")

        try:
            with open(log_path, 'w', encoding='utf-8') as f:
                f.write('\n'.join(log_lines))
        except Exception as e:
            # 日志写盘失败不再静默
            log(f"⚠ 警告: 日志文件写入失败 ({e})，以上内容仅保存在界面日志中")

        self.update_progress(100)
        print("=== 全部任务执行完毕 ===", flush=True)

        title = "处理完成" if not cancelled else "任务已取消"
        summary_parts = [
            f"{'任务已被取消，以下为已完成部分！' if cancelled else '处理完成！'}", f"",
            f"文件总数: {total_files}",
            f"成功处理: {processed_count}",
        ]
        if skip_existing:
            summary_parts.append(f"跳过已存在: {skipped_existing_count}")
        summary_parts.append(f"未处理数: {len(unprocessed_list)}")
        if unprocessed_list:
            summary_parts.extend([
                f"",
                f"⚠ 有 {len(unprocessed_list)} 个文件未处理，",
                f"请查看界面日志框或控制台获取详情。"
            ])
        summary_parts.extend([f"", f"日志已保存至:", f"{log_path}"])

        self.root.after(0, lambda: messagebox.showinfo(title, "\n".join(summary_parts)))

    # ------------------------------------------------------------------ #
    def extract_gps(self, meta):
        """提取 GPS，兼容照片标准标签和视频 GPSCoordinates 标签。
        经纬序按 XMP 规范默认"纬度 经度"，仅在该顺序值域校验失败时才对调，
        消除赤道/本初子午线附近（lat≈0 或 lon≈0）的误判。"""
        try:
            gps_coords = meta.get('GPSCoordinates') or meta.get('GPSPosition')
            if gps_coords:
                nums = re.findall(r'[-+]?\d*\.?\d+', str(gps_coords))
                if len(nums) >= 2:
                    a = float(nums[0])
                    b = float(nums[1])
                    # 首选规范顺序 (纬度, 经度)
                    if -90 <= a <= 90 and -180 <= b <= 180:
                        return a, b
                    # 规范顺序不成立才对调
                    if -90 <= b <= 90 and -180 <= a <= 180:
                        return b, a
                    # 两个顺序都不成立（如含异常值），交由后续标签兜底

            lat_str = meta.get('GPSLatitude')
            lon_str = meta.get('GPSLongitude')
            if lat_str is not None and lon_str is not None and str(lat_str).strip() and str(lon_str).strip():
                lat = float(lat_str)
                lon = float(lon_str)
                if meta.get('GPSLatitudeRef', 'N') == 'S' and lat > 0:
                    lat = -lat
                if meta.get('GPSLongitudeRef', 'E') == 'W' and lon > 0:
                    lon = -lon
                if -90 <= lat <= 90 and -180 <= lon <= 180:
                    return lat, lon

            return None, None
        except Exception:
            return None, None

    def get_location_from_amap(self, wgs_lon, wgs_lat, api_key):
        """
        通过高德逆地理编码获取国家/城市
        【核心逻辑】仅中国大陆转GCJ-02，港澳台及海外保持WGS-84
        【增强兜底】安全提取字段 + 港澳台特殊处理 + 三级补位链
        【注意】缓存粒度为 0.01°（约 1km），海岸线/边境约 1km 范围内可能归错城市，
               这是性能与精度的折衷
        """
        cache_key = f"{round(wgs_lat, 2)},{round(wgs_lon, 2)}"
        if cache_key in self.location_cache:
            return self.location_cache[cache_key]

        try:
            # 仅中国大陆需要坐标转换
            if _is_in_china_mainland(wgs_lon, wgs_lat):
                query_lon, query_lat = wgs84_to_gcj02(wgs_lon, wgs_lat)
            else:
                query_lon, query_lat = wgs_lon, wgs_lat

            url = "https://restapi.amap.com/v3/geocode/regeo"
            params = {
                "key": api_key,
                "location": f"{query_lon:.6f},{query_lat:.6f}",
                "radius": 1000,
                "extensions": "base"
            }

            data = None
            last_err = None
            # 重试 2 次，0.5s 退避，缓解偶发网络抖动 / QPS 限流
            for attempt in range(3):
                try:
                    response = requests.get(url, params=params, timeout=5)
                    data = response.json()
                    break
                except Exception as e:
                    last_err = e
                    if attempt < 2:
                        import time
                        time.sleep(0.5 * (attempt + 1))
            if data is None:
                print(f"高德API请求失败(已重试): {last_err}", flush=True)
                self.location_cache[cache_key] = ("其他", "其他")
                return "其他", "其他"

            if data.get('status') == '1' and data.get('regeocode'):
                addr_comp = data['regeocode'].get('addressComponent', {})

                # 安全提取：统一处理 None / 空字符串 / 空列表
                def _safe_get(field, default='其他'):
                    val = addr_comp.get(field)
                    if val is None or val == '' or val == [] or val == '[]':
                        return default
                    result = str(val).strip()
                    return result if result else default

                country = _safe_get('country')
                province = _safe_get('province')
                city = _safe_get('city')
                district = _safe_get('district')

                # 港澳台特殊处理
                hk_mo_tw_keywords = ['香港', '澳门', '台湾']
                is_special_region = any(kw in province for kw in hk_mo_tw_keywords)

                if is_special_region:
                    # 简化名称："香港特别行政区" -> "香港"
                    for kw in hk_mo_tw_keywords:
                        if kw in province:
                            province = kw
                            break
                    # city 为空时用 province 补位
                    if city == '其他' or city == '市辖区':
                        city = province
                    # 仍无效则用 district 补位
                    if city == '其他' and district != '其他':
                        city = district
                else:
                    # 大陆及海外通用逻辑
                    if city == '其他' or city == '市辖区':
                        city = province

                self.location_cache[cache_key] = (country, city)
                return country, city

        except Exception as e:
            print(f"高德API请求失败: {e}", flush=True)

        self.location_cache[cache_key] = ("其他", "其他")
        return "其他", "其他"

    def run_exiftool(self, source_dir):
        """批量读取元数据。
        -api QuickTimeUTC：让 exiftool 在源头把视频 QuickTime 日期按 UTC 正确换算为本地时间，
        替代原先在 Python 侧"一律按UTC+本机偏移"的错误做法。
        超时放宽到 1800s，且超时/报错时尽量保留已捕获的部分结果。"""
        cmd = [
            'exiftool', '-json', '-charset', 'filename=utf8', '-n',
            '-api', 'QuickTimeUTC',
            '-DateTimeOriginal', '-CreateDate', '-MediaCreateDate', '-TrackCreateDate', '-FileModifyDate',
            '-GPSLatitude', '-GPSLongitude', '-GPSLatitudeRef', '-GPSLongitudeRef',
            '-GPSCoordinates', '-GPSPosition',
            '-c', '%.8f', '-r', source_dir
        ]
        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=1800,
                                    encoding='utf-8', errors='replace')
            if result.returncode == 0 or result.stdout.strip():
                return json.loads(result.stdout)
            return None
        except subprocess.TimeoutExpired as e:
            # 超时：尝试使用已捕获的部分输出
            partial = (e.stdout or b'')
            if isinstance(partial, bytes):
                partial = partial.decode('utf-8', errors='replace')
            if partial.strip():
                try:
                    self.gui_log(f"⚠ exiftool 超时(1800s)，将使用已读取到的部分结果继续")
                    return json.loads(partial)
                except Exception:
                    pass
            print(f"exiftool 超时: 1800s", flush=True)
            return None
        except Exception as e:
            print(f"exiftool 错误: {e}", flush=True)
            return None

    @staticmethod
    def parse_date_folder(date_str, mode='ym'):
        if not date_str:
            return None
        dt = None
        fmts = ('%Y:%m:%d %H:%M:%S', '%Y-%m-%d %H:%M:%S', '%Y:%m:%d %H:%M',
                '%Y-%m-%d %H:%M', '%Y:%m:%d', '%Y-%m-%d', '%Y%m%d')
        # 依次尝试完整串及常见截断长度（修复原版对紧凑格式 20240315 的前缀截断 bug）
        for sub in (date_str, date_str[:19], date_str[:16], date_str[:10], date_str[:8]):
            if not sub:
                continue
            for fmt in fmts:
                try:
                    dt = datetime.strptime(sub, fmt)
                    break
                except ValueError:
                    continue
            if dt:
                break

        if dt is None:
            try:
                y, m, d = date_str[:4], date_str[5:7], date_str[8:10]
                # 增加年月合法性校验，防止 0000:00:00 之类的无效值被切片兜底放行
                if (y.isdigit() and 1 <= int(y) <= 9999 and m.isdigit() and 1 <= int(m) <= 12):
                    if mode == 'ymd' and d.isdigit() and 1 <= int(d) <= 31:
                        return f"{y}{m}{d}"
                    elif mode == 'ym':
                        return f"{y}{m}"
            except Exception:
                pass
            return None
        return dt.strftime('%Y%m%d') if mode == 'ymd' else dt.strftime('%Y%m')

    @staticmethod
    def sanitize_dir_name(name):
        invalid_chars = '<>:"/\\|?*'
        for char in invalid_chars:
            name = name.replace(char, '')
        return name.strip() or "其他"

    @staticmethod
    def get_unique_path(filepath):
        if not os.path.exists(filepath):
            return filepath
        base, ext = os.path.splitext(filepath)
        counter = 1
        while os.path.exists(f"{base}_{counter}{ext}"):
            counter += 1
        return f"{base}_{counter}{ext}"

    def update_progress(self, value):
        self.root.after(0, lambda: self.progress_value.set(value))

    def reset_ui(self):
        self.is_processing = False
        self.cancel_flag.clear()
        self.root.after(0, lambda: self.btn_start.config(state=tk.NORMAL))
        self.root.after(0, lambda: self.btn_cancel.config(state=tk.DISABLED))


def main():
    root = tk.Tk()
    PhotoClassifierApp(root)
    root.mainloop()


if __name__ == '__main__':
    main()
