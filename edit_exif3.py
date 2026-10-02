#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
EXIF 编辑器 v2 — 支持照片和视频文件的 EXIF 信息查看与编辑
依赖: 系统需安装 exiftool (https://exiftool.org/)

【v2 修复清单】
 1. [P1] DMS 换算秒数四舍五入到 60 的进位 bug（39 deg 59' 60.0" 非法值）
 2. [P1] 只读标签（Composite/File 组）禁止编辑，避免必然失败的写入
 3. [P1] 视频添加 GPS 改写 Keys:GPSCoordinates + XMP，Apple/QuickTime 可识别
 4. [P1] 保存前自动备份原文件到同级可见 exif_backup/ 目录
 5. [P1] 保存后解析 exiftool 的 Warning/Sorry，"0 files updated" 视为失败
 6. [P2] 文件类型过滤器切片错位（rw2 曾混入视频过滤器）改为列表构建
 7. [P2] 读取/保存改到后台线程执行，界面不再冻结
 8. [P2] 跨平台字体适配（macOS 苹方/Menlo，Windows 微软雅黑/Consolas）
 9. [P2] subprocess 显式 encoding='utf-8'，修复 Windows 中文乱码
10. [P2] GPS 检测改为按关键词匹配，覆盖 QuickTime:GPSCoordinates 等全部变体
"""

import json
import os
import shutil
import subprocess
import sys
import threading
import tkinter as tk
from tkinter import filedialog, messagebox, ttk

IS_WIN = sys.platform == "win32"


# ─────────────── 跨平台字体适配 ───────────────
class StyleAdapter:
    @staticmethod
    def get_font(size=10, bold=False):
        if IS_WIN:
            return ("Microsoft YaHei", max(9, size), "bold" if bold else "normal")
        return ("PingFang SC", size, "bold" if bold else "normal")

    @staticmethod
    def get_mono(size=10):
        return (("Consolas", size, "normal") if IS_WIN else ("Menlo", size, "normal"))


class ExifEditorApp:
    """主应用程序类"""

    # 图片/视频扩展名（过滤器与判断均由此构建，避免切片错位）
    IMAGE_EXTS = [".jpg", ".jpeg", ".png", ".tiff", ".tif", ".bmp",
                  ".gif", ".webp", ".heic", ".heif",".hif", ".raw",
                  ".cr2", ".cr3", ".nef", ".arw", ".dng", ".orf", ".rw2"]
    VIDEO_EXTS = [".mp4", ".mov", ".avi", ".mkv", ".wmv", ".flv",
                  ".webm", ".m4v", ".3gp", ".mts", ".m2ts"]

    # 不可写的 exiftool 组（读取展示可以，编辑写入必失败）
    READONLY_GROUPS = {"Composite", "File"}

    # 原始值文本框颜色常量
    _ORIG_BG = "#f0f0f0"
    _ORIG_FG = "#333333"

    def __init__(self, root):
        self.root = root
        self.root.title("EXIF 编辑器 — 照片/视频元数据查看与修改")
        self.root.geometry("1100x820")
        self.root.minsize(900, 650)

        self.style = ttk.Style()
        self.style.theme_use("clam")

        self.style.configure("Title.TLabel", font=StyleAdapter.get_font(11, bold=True))
        self.style.configure("Path.TLabel", font=StyleAdapter.get_mono(10), foreground="#2a6")
        self.style.configure("Status.TLabel", font=StyleAdapter.get_font(10), foreground="#666")
        self.style.configure("Action.TButton", font=StyleAdapter.get_font(10))
        self.style.configure("Treeview", rowheight=24, font=StyleAdapter.get_mono(11))
        self.style.configure("Treeview.Heading", font=StyleAdapter.get_font(11, bold=True))

        self.file_path = None
        self.exif_data = {}
        self.modified_data = {}
        self.current_editing_tag = None
        self.is_busy = False

        self._build_ui()

    # ──────────────────────────────────────
    #  界面构建
    # ──────────────────────────────────────
    def _build_ui(self):
        main = ttk.Frame(self.root, padding=10)
        main.pack(fill=tk.BOTH, expand=True)

        # ── 顶部: 文件选择区 ──
        top = ttk.LabelFrame(main, text="📁 文件选择", padding=8)
        top.pack(fill=tk.X, pady=(0, 8))

        self.btn_select = ttk.Button(top, text="选择文件…", command=self._select_file, width=12)
        self.btn_select.pack(side=tk.LEFT, padx=(0, 10))

        self.lbl_path = ttk.Label(top, text="（未选择文件）", style="Path.TLabel")
        self.lbl_path.pack(side=tk.LEFT, fill=tk.X, expand=True)

        # ── 中部: EXIF 数据展示 + 编辑区 ──
        mid = ttk.Frame(main)
        mid.pack(fill=tk.BOTH, expand=True, pady=(0, 8))

        # 左侧: Treeview
        left = ttk.Frame(mid)
        left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        tree_header = ttk.Frame(left)
        tree_header.pack(fill=tk.X, pady=(0, 4))
        ttk.Label(tree_header, text="EXIF 属性列表", style="Title.TLabel").pack(side=tk.LEFT)
        self.lbl_count = ttk.Label(tree_header, text="", style="Status.TLabel")
        self.lbl_count.pack(side=tk.RIGHT)

        tree_frame = ttk.Frame(left)
        tree_frame.pack(fill=tk.BOTH, expand=True)

        self.tree = ttk.Treeview(
            tree_frame, columns=("tag", "value"), show="headings", selectmode="browse"
        )
        self.tree.heading("tag", text="属性名称 (Tag)")
        self.tree.heading("value", text="属性值 (Value)")
        self.tree.column("tag", width=260, minwidth=150, anchor=tk.W)
        self.tree.column("value", width=520, minwidth=200, anchor=tk.W)

        vsb = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=self.tree.yview)
        hsb = ttk.Scrollbar(tree_frame, orient=tk.HORIZONTAL, command=self.tree.xview)
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)

        self.tree.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")
        tree_frame.rowconfigure(0, weight=1)
        tree_frame.columnconfigure(0, weight=1)

        self.tree.tag_configure("odd", background="#f4f4f4")
        self.tree.tag_configure("even", background="#ffffff")
        self.tree.tag_configure("modified", background="#fff3cd", foreground="#856404")
        self.tree.tag_configure("readonly", background="#e8e8e8", foreground="#999999")
        self.tree.bind("<Double-1>", self._on_double_click)

        # 右侧: 编辑面板 + GPS面板
        right = ttk.Frame(mid, width=300)
        right.pack(side=tk.RIGHT, fill=tk.Y, padx=(10, 0))
        right.pack_propagate(False)

        # -- 通用编辑面板 --
        edit_panel = ttk.LabelFrame(right, text="✏️ 编辑面板", padding=10)
        edit_panel.pack(fill=tk.X, pady=(0, 8))

        ttk.Label(edit_panel, text="标签名:").pack(anchor=tk.W, pady=(4, 0))
        self.entry_tag = ttk.Entry(edit_panel, state="readonly", width=34,
                                   font=StyleAdapter.get_mono(10))
        self.entry_tag.pack(fill=tk.X, pady=(2, 8))

        ttk.Label(edit_panel, text="原始值:").pack(anchor=tk.W, pady=(4, 0))
        self.txt_orig = tk.Text(
            edit_panel, height=3, width=34, wrap=tk.WORD,
            state="disabled", bg=self._ORIG_BG, fg=self._ORIG_FG,
            font=StyleAdapter.get_mono(9), relief="sunken", bd=1
        )
        self.txt_orig.pack(fill=tk.X, pady=(2, 8))

        ttk.Label(edit_panel, text="新值:").pack(anchor=tk.W, pady=(4, 0))
        self.txt_new = tk.Text(
            edit_panel, height=3, width=34, wrap=tk.WORD,
            font=StyleAdapter.get_mono(9), relief="sunken", bd=1
        )
        self.txt_new.pack(fill=tk.X, pady=(2, 12))

        btn_edit_frame = ttk.Frame(edit_panel)
        btn_edit_frame.pack(fill=tk.X)

        self.btn_apply_edit = ttk.Button(btn_edit_frame, text="✔ 应用修改", command=self._apply_edit)
        self.btn_apply_edit.pack(fill=tk.X, pady=2)
        self.btn_revert_edit = ttk.Button(btn_edit_frame, text="↩ 恢复原始值", command=self._revert_edit)
        self.btn_revert_edit.pack(fill=tk.X, pady=2)

        # -- 📍 GPS 信息添加面板 --
        self.gps_panel = ttk.LabelFrame(right, text="📍 GPS 信息添加", padding=10)
        self.gps_panel.pack(fill=tk.X, pady=(0, 8))

        ttk.Label(self.gps_panel, text="纬度 (十进制度数):").pack(anchor=tk.W, pady=(2, 0))
        self.entry_lat = ttk.Entry(self.gps_panel, width=34, font=StyleAdapter.get_mono(10))
        self.entry_lat.pack(fill=tk.X, pady=(2, 6))
        ttk.Label(self.gps_panel, text="例: 39.9042 (北纬为正，南纬为负)", style="Status.TLabel").pack(anchor=tk.W)

        ttk.Label(self.gps_panel, text="经度 (十进制度数):").pack(anchor=tk.W, pady=(6, 0))
        self.entry_lon = ttk.Entry(self.gps_panel, width=34, font=StyleAdapter.get_mono(10))
        self.entry_lon.pack(fill=tk.X, pady=(2, 6))
        ttk.Label(self.gps_panel, text="例: 116.4074 (东经为正，西经为负)", style="Status.TLabel").pack(anchor=tk.W)

        self.btn_add_gps = ttk.Button(self.gps_panel, text="➕ 添加 GPS 到修改列表", command=self._add_gps)
        self.btn_add_gps.pack(fill=tk.X, pady=(10, 4))

        self.lbl_gps_status = ttk.Label(self.gps_panel, text="", style="Status.TLabel", wraplength=260)
        self.lbl_gps_status.pack(anchor=tk.W, pady=(4, 0))

        # 初始状态禁用 GPS 面板
        self._set_gps_panel_disabled()

        # -- 提示 --
        ttk.Separator(right, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=8)
        ttk.Label(
            right,
            text="💡 提示:\n• 双击表格行可快速编辑\n• 黄色行表示已修改\n• 灰色行为只读标签不可编辑\n• 清空值将删除该标签\n• GPS 仅当原文件无坐标时可添加\n• 保存前自动备份到同级 exif_backup/",
            style="Status.TLabel", wraplength=260, justify=tk.LEFT,
        ).pack(anchor=tk.W, pady=(4, 0))

        # ── 底部: 操作按钮区 ──
        bot = ttk.Frame(main)
        bot.pack(fill=tk.X)

        self.lbl_status = ttk.Label(bot, text="就绪", style="Status.TLabel")
        self.lbl_status.pack(side=tk.LEFT)

        btn_frame = ttk.Frame(bot)
        btn_frame.pack(side=tk.RIGHT)

        self.btn_submit = ttk.Button(
            btn_frame, text="🔍 读取 EXIF", command=self._read_exif,
            style="Action.TButton", width=14
        )
        self.btn_submit.pack(side=tk.LEFT, padx=4)

        self.btn_save = ttk.Button(
            btn_frame, text="💾 保存到文件", command=self._save_exif,
            style="Action.TButton", width=14
        )
        self.btn_save.pack(side=tk.LEFT, padx=4)
        self.btn_save.configure(state=tk.DISABLED)

        self.btn_discard = ttk.Button(
            btn_frame, text="🗑 放弃修改", command=self._discard_changes,
            style="Action.TButton", width=14
        )
        self.btn_discard.pack(side=tk.LEFT, padx=4)
        self.btn_discard.configure(state=tk.DISABLED)

        self.btn_exit = ttk.Button(
            btn_frame, text="❌ 退出", command=self._exit_app,
            style="Action.TButton", width=10
        )
        self.btn_exit.pack(side=tk.LEFT, padx=4)

    # ──────────────────────────────────────
    #  工具方法
    # ──────────────────────────────────────
    @staticmethod
    def _is_video(fp):
        return os.path.splitext(fp or "")[1].lower() in ExifEditorApp.VIDEO_EXTS

    @classmethod
    def _is_writable_tag(cls, tag):
        """判断标签所在组是否可写（Composite/File 组为只读展示）"""
        if ":" not in tag:
            return False
        return tag.split(":", 1)[0] not in cls.READONLY_GROUPS

    @staticmethod
    def _has_gps(exif_data):
        """按关键词检测 GPS，覆盖 EXIF/XMP/QuickTime/Keys/GPS 等全部组变体"""
        for tag in exif_data:
            base = tag.split(":", 1)[-1]
            if base in ("GPSLatitude", "GPSLongitude", "GPSCoordinates", "GPSPosition"):
                return True
        return False

    @staticmethod
    def _backup_path(fp):
        """备份路径：文件所在目录的同级 exif_backup/（可见目录）"""
        file_dir = os.path.dirname(os.path.abspath(fp))
        parent = os.path.dirname(file_dir)
        if parent and parent != file_dir:
            return os.path.join(parent, "exif_backup", os.path.basename(fp))
        return os.path.join(file_dir, "exif_backup", os.path.basename(fp))

    @staticmethod
    def _decimal_to_exif_gps(decimal_deg: float, is_lat: bool) -> tuple:
        """
        将十进制度数转换为 exiftool 写入格式。
        返回 (ref, dms_string)。秒数四舍五入后向分/度进位，避免 60.0" 非法值。
        """
        if is_lat:
            ref = "N" if decimal_deg >= 0 else "S"
        else:
            ref = "E" if decimal_deg >= 0 else "W"

        abs_deg = abs(decimal_deg)
        degrees = int(abs_deg)
        minutes_full = (abs_deg - degrees) * 60
        minutes = int(minutes_full)
        seconds = round((minutes_full - minutes) * 60, 4)

        if seconds >= 60:
            seconds = 0.0
            minutes += 1
        if minutes >= 60:
            minutes = 0
            degrees += 1

        seconds_str = f"{seconds:.4f}".rstrip("0").rstrip(".")
        dms = f"{degrees} deg {minutes}' {seconds_str}\""
        return ref, dms

    # ──────────────────────────────────────
    #  GPS 状态检测与控制
    # ──────────────────────────────────────
    def _check_gps_status(self):
        """检测当前 EXIF 数据中是否已包含 GPS 信息，并更新 GPS 面板状态"""
        if self._has_gps(self.exif_data):
            self.entry_lat.configure(state="disabled")
            self.entry_lon.configure(state="disabled")
            self.btn_add_gps.configure(state="disabled")
            self.lbl_gps_status.configure(
                text="⚠️ 文件已包含 GPS 信息，如需修改请在上方表格中直接编辑对应标签。",
                foreground="#c66"
            )
        else:
            self.entry_lat.configure(state="normal")
            self.entry_lon.configure(state="normal")
            self.btn_add_gps.configure(state="normal")
            self.lbl_gps_status.configure(
                text="✅ 文件无 GPS 信息，可在此添加。",
                foreground="#2a6"
            )

    def _set_gps_panel_disabled(self):
        """在未选择文件或未读取时禁用 GPS 面板"""
        self.entry_lat.configure(state="disabled")
        self.entry_lon.configure(state="disabled")
        self.btn_add_gps.configure(state="disabled")
        self.lbl_gps_status.configure(text="请先读取文件", foreground="#999")

    # ──────────────────────────────────────
    #  GPS 添加逻辑
    # ──────────────────────────────────────
    def _add_gps(self):
        """验证输入并将 GPS 数据加入 modified_data（按文件类型选择写入位置）"""
        lat_str = self.entry_lat.get().strip()
        lon_str = self.entry_lon.get().strip()

        if not lat_str or not lon_str:
            messagebox.showwarning("提示", "请同时输入纬度和经度！")
            return

        try:
            lat = float(lat_str)
            lon = float(lon_str)
        except ValueError:
            messagebox.showerror("格式错误", "纬度和经度必须是数字！\n例: 39.9042 / 116.4074")
            return

        if not (-90 <= lat <= 90):
            messagebox.showerror("范围错误", f"纬度必须在 -90 ~ 90 之间，当前值: {lat}")
            return
        if not (-180 <= lon <= 180):
            messagebox.showerror("范围错误", f"经度必须在 -180 ~ 180 之间，当前值: {lon}")
            return

        # 清掉之前可能存在的 GPS 新增项，避免混写
        for k in list(self.modified_data.keys()):
            if "GPS" in k.split(":", 1)[-1]:
                del self.modified_data[k]

        if self._is_video(self.file_path):
            # 视频 (MP4/MOV/QuickTime)：Apple/QuickTime 读取 Keys:GPSCoordinates，
            # 同时写 XMP GPS 作为通用兜底（带符号十进制格式）
            sign = lambda v: "+" if v >= 0 else "-"
            coord = f"{sign(lat)}{abs(lat):.6f} {sign(lon)}{abs(lon):.6f}"
            self.modified_data["Keys:GPSCoordinates"] = coord
            self.modified_data["XMP:GPSLatitude"] = f"{sign(lat)}{abs(lat):.6f}"
            self.modified_data["XMP:GPSLongitude"] = f"{sign(lon)}{abs(lon):.6f}"
            dest_hint = "Keys:GPSCoordinates + XMP:GPS*（视频格式）"
        else:
            # 照片：标准 EXIF GPS 标签（度分秒 + 半球引用）
            lat_ref, lat_dms = self._decimal_to_exif_gps(lat, is_lat=True)
            lon_ref, lon_dms = self._decimal_to_exif_gps(lon, is_lat=False)
            self.modified_data["EXIF:GPSLatitude"] = lat_dms
            self.modified_data["EXIF:GPSLatitudeRef"] = lat_ref
            self.modified_data["EXIF:GPSLongitude"] = lon_dms
            self.modified_data["EXIF:GPSLongitudeRef"] = lon_ref
            dest_hint = "EXIF:GPS*（照片格式）"

        self._populate_tree()
        self._update_buttons()
        self._set_status(f"已添加 GPS: ({lat}, {lon}) -> {dest_hint}")
        messagebox.showinfo(
            "成功",
            f"GPS 信息已添加到修改列表！\n\n"
            f"纬度: {lat}\n经度: {lon}\n"
            f"写入位置: {dest_hint}\n\n"
            f"点击「💾 保存到文件」写入磁盘。"
        )

    # ──────────────────────────────────────
    #  原始值文本框辅助方法
    # ──────────────────────────────────────
    def _set_orig_text(self, content: str):
        """安全地写入原始值文本框并设为禁用态"""
        self.txt_orig.configure(state="normal", fg=self._ORIG_FG, bg=self._ORIG_BG)
        self.txt_orig.delete("1.0", tk.END)
        self.txt_orig.insert("1.0", content)
        self.txt_orig.configure(state="disabled")

    def _clear_orig_text(self):
        """清空原始值文本框并保持禁用态"""
        self.txt_orig.configure(state="normal", fg=self._ORIG_FG, bg=self._ORIG_BG)
        self.txt_orig.delete("1.0", tk.END)
        self.txt_orig.configure(state="disabled")

    # ──────────────────────────────────────
    #  文件选择
    # ──────────────────────────────────────
    def _select_file(self):
        img_patterns = " ".join(f"*{e}" for e in self.IMAGE_EXTS)
        vid_patterns = " ".join(f"*{e}" for e in self.VIDEO_EXTS)
        filetypes = [
            ("所有支持的文件", f"{img_patterns} {vid_patterns}"),
            ("图片文件", img_patterns),
            ("视频文件", vid_patterns),
            ("所有文件", "*.*"),
        ]
        path = filedialog.askopenfilename(title="选择照片或视频文件", filetypes=filetypes)
        if path:
            self.file_path = path
            self.lbl_path.configure(text=path)
            self._set_status(f"已选择: {os.path.basename(path)}")
            self._clear_tree()
            self.exif_data.clear()
            self.modified_data.clear()
            self._update_buttons()
            self._set_gps_panel_disabled()

    # ──────────────────────────────────────
    #  EXIF 读取（后台线程）
    # ──────────────────────────────────────
    def _read_exif(self):
        if self.is_busy:
            return
        if not self.file_path:
            messagebox.showwarning("提示", "请先选择一个文件！")
            return
        if not os.path.isfile(self.file_path):
            messagebox.showerror("错误", f"文件不存在:\n{self.file_path}")
            return

        self._set_busy(True, "正在读取 EXIF 信息…")
        fp = self.file_path

        def _worker():
            out, err, rc = self._run_exiftool(["-json", "-G0", "-s", fp], timeout=30)
            self.root.after(0, lambda: self._read_exif_done(fp, out, err, rc))

        threading.Thread(target=_worker, daemon=True).start()

    def _read_exif_done(self, fp, out, err, rc):
        try:
            if rc == -1:  # FileNotFoundError
                messagebox.showerror(
                    "错误",
                    "未找到 exiftool！\n请安装并确保其在 PATH 中。\nhttps://exiftool.org/"
                )
                self._set_status("错误: exiftool 未安装")
                return
            if rc == -2:  # TimeoutExpired
                messagebox.showerror("错误", "exiftool 执行超时！")
                self._set_status("错误: 超时")
                return
            if rc != 0:
                messagebox.showerror("错误", f"exiftool 返回错误:\n{err}")
                self._set_status("读取失败")
                return

            try:
                data = json.loads(out)
            except json.JSONDecodeError:
                messagebox.showerror("错误", "无法解析 exiftool 输出！")
                self._set_status("解析失败")
                return

            if not data:
                messagebox.showinfo("提示", "未读取到任何 EXIF 信息。")
                self._set_status("无数据")
                self._check_gps_status()
                return

            raw = data[0]
            skip_keys = {
                "SourceFile", "FileName", "Directory", "FileSize",
                "FileModifyDate", "FileAccessDate", "FileInodeChangeDate",
                "FilePermissions", "FileType", "FileTypeExtension", "MIMEType"
            }

            self.exif_data.clear()
            self.modified_data.clear()

            for key, val in sorted(raw.items()):
                if key not in skip_keys:
                    self.exif_data[key] = str(val) if val is not None else ""

            self._populate_tree()
            self._update_buttons()
            self._check_gps_status()  # 读取完成后检测 GPS 状态
            self._set_status(f"已读取 {len(self.exif_data)} 个 EXIF 属性")
        finally:
            self._set_busy(False)

    def _populate_tree(self):
        self._clear_tree()

        # 合并显示 exif_data 和 modified_data 中的新增项（如新添加的 GPS）
        all_tags = set(self.exif_data.keys()) | set(self.modified_data.keys())

        for i, tag in enumerate(sorted(all_tags)):
            orig_value = self.exif_data.get(tag, "")
            display_value = self.modified_data.get(tag, orig_value)
            if tag in self.modified_data:
                row_tag = "modified"
            elif not self._is_writable_tag(tag):
                row_tag = "readonly"
            else:
                row_tag = "odd" if i % 2 else "even"
            self.tree.insert("", tk.END, iid=tag, values=(tag, display_value), tags=(row_tag,))

        self.lbl_count.configure(text=f"共 {len(all_tags)} 项")

    def _clear_tree(self):
        self.tree.delete(*self.tree.get_children())
        self.lbl_count.configure(text="")
        self._clear_edit_panel()

    # ──────────────────────────────────────
    #  编辑功能
    # ──────────────────────────────────────
    def _on_double_click(self, event):
        item = self.tree.identify_row(event.y)
        column = self.tree.identify_column(event.x)
        if not item or column != "#2":
            return
        if not self._is_writable_tag(item):
            self._set_status(f"⚠ {item.split(':', 1)[0]} 组为只读标签，不可编辑")
            messagebox.showwarning(
                "只读标签",
                f"「{item}」属于只读组，由 exiftool 自动计算生成，无法直接写入。\n\n"
                f"如需修改，请编辑其对应的源标签（如 EXIF: 组标签）。"
            )
            return
        self._load_to_edit_panel(item)

    def _load_to_edit_panel(self, tag):
        self.current_editing_tag = tag
        orig_value = self.exif_data.get(tag, "")
        current_value = self.modified_data.get(tag, orig_value)

        self.entry_tag.configure(state="normal")
        self.entry_tag.delete(0, tk.END)
        self.entry_tag.insert(0, tag)
        self.entry_tag.configure(state="readonly")

        self._set_orig_text(orig_value)

        self.txt_new.delete("1.0", tk.END)
        self.txt_new.insert("1.0", current_value)
        self.txt_new.focus_set()

    def _apply_edit(self):
        tag = self.current_editing_tag
        if not tag:
            messagebox.showinfo("提示", "请先双击选择一个要编辑的属性！")
            return
        if not self._is_writable_tag(tag):
            messagebox.showwarning("只读标签", f"「{tag}」为只读标签，不能应用修改。")
            return

        new_value = self.txt_new.get("1.0", tk.END).strip()
        orig_value = self.exif_data.get(tag, "")

        if new_value == orig_value:
            self.modified_data.pop(tag, None)
        else:
            self.modified_data[tag] = new_value

        self._populate_tree()
        self._update_buttons()
        if self.tree.exists(tag):
            self.tree.selection_set(tag)
            self.tree.see(tag)
        self._set_status(f"已修改: {tag}")

    def _revert_edit(self):
        tag = self.current_editing_tag
        if not tag:
            return
        self.modified_data.pop(tag, None)
        self._populate_tree()
        self._update_buttons()

        orig_value = self.exif_data.get(tag, "")
        self.txt_new.delete("1.0", tk.END)
        self.txt_new.insert("1.0", orig_value)
        self._set_status(f"已恢复: {tag}")

    def _clear_edit_panel(self):
        self.current_editing_tag = None
        self.entry_tag.configure(state="normal")
        self.entry_tag.delete(0, tk.END)
        self.entry_tag.configure(state="readonly")

        self._clear_orig_text()
        self.txt_new.delete("1.0", tk.END)

    # ──────────────────────────────────────
    #  exiftool 执行（含编码/超时统一处理）
    # ──────────────────────────────────────
    @staticmethod
    def _run_exiftool(args, timeout):
        """返回 (stdout, stderr, rc)；rc=-1 未安装，rc=-2 超时"""
        cmd = ["exiftool"] + args
        try:
            result = subprocess.run(
                cmd, capture_output=True, timeout=timeout,
                encoding="utf-8", errors="replace",
            )
            return result.stdout, result.stderr, result.returncode
        except FileNotFoundError:
            return "", "", -1
        except subprocess.TimeoutExpired:
            return "", "", -2

    # ──────────────────────────────────────
    #  保存 / 放弃（后台线程 + 自动备份）
    # ──────────────────────────────────────
    def _save_exif(self):
        if self.is_busy:
            return
        if not self.modified_data:
            messagebox.showinfo("提示", "没有需要保存的修改。")
            return
        if not self.file_path:
            messagebox.showerror("错误", "未选择文件！")
            return

        # 1. 写前备份到同级 exif_backup/，失败则中止写入
        backup_path = self._backup_path(self.file_path)
        try:
            os.makedirs(os.path.dirname(backup_path), exist_ok=True)
            if not os.path.exists(backup_path):
                shutil.copy2(self.file_path, backup_path)
        except Exception as e:
            messagebox.showerror(
                "备份失败，已取消写入",
                f"无法创建备份文件:\n{backup_path}\n\n{e}\n\n"
                f"为保护原文件，本次修改未写入。"
            )
            return

        # 2. 构建 exiftool 命令
        cmd = ["-overwrite_original"]
        for tag, value in self.modified_data.items():
            if value == "":
                cmd.append(f"-{tag}=")
            else:
                cmd.append(f"-{tag}={value}")
        cmd.append(self.file_path)

        self._set_busy(True, "正在保存…")
        n = len(self.modified_data)

        def _worker():
            out, err, rc = self._run_exiftool(cmd, timeout=60)
            self.root.after(0, lambda: self._save_done(out, err, rc, n, backup_path))

        threading.Thread(target=_worker, daemon=True).start()

    def _save_done(self, out, err, rc, n, backup_path):
        try:
            combined = (err or "") + (out or "")
            warnings = [ln for ln in combined.splitlines()
                        if "Warning" in ln or "Sorry" in ln or "Error" in ln]
            updated = "1 image files updated" in combined or "1 image files created" in combined

            if rc != 0 or not updated:
                messagebox.showerror(
                    "保存失败",
                    f"exiftool 未能写入任何修改 (rc={rc})。\n\n"
                    f"{(err or out or '无详细信息')}\n\n"
                    f"原文件已备份于:\n{backup_path}"
                )
                self._set_status("保存失败")
                return

            if warnings:
                show = "\n".join(warnings[:10])
                more = f"\n…(共 {len(warnings)} 条)" if len(warnings) > 10 else ""
                messagebox.showwarning(
                    "保存完成（部分警告）",
                    f"已写入 {n} 项修改，但 exiftool 报告以下警告，"
                    f"部分标签可能未实际写入:\n\n{show}{more}\n\n"
                    f"建议重新读取核对。\n备份位于:\n{backup_path}"
                )
            else:
                messagebox.showinfo(
                    "成功",
                    f"已成功保存 {n} 个修改！\n\n备份文件:\n{backup_path}"
                )

            self.modified_data.clear()
            self._set_busy(False)
            self._read_exif()  # 重新读取会自行处理 busy 状态
            self._set_status("保存成功")
            return
        finally:
            if not self.is_busy:
                self._set_busy(False)
            # 重新读取路径中 _read_exif 会接管 busy 状态

    def _discard_changes(self):
        if not self.modified_data:
            messagebox.showinfo("提示", "没有未保存的修改。")
            return
        if messagebox.askyesno("确认", "确定放弃所有未保存的修改？"):
            self.modified_data.clear()
            self._populate_tree()
            self._update_buttons()
            self._clear_edit_panel()
            self._check_gps_status()  # 放弃修改后重新检测 GPS 状态
            self._set_status("已放弃所有修改")

    # ──────────────────────────────────────
    #  辅助方法
    # ──────────────────────────────────────
    def _set_busy(self, busy, status_text=None):
        self.is_busy = busy
        if status_text:
            self._set_status(status_text)
        state = tk.DISABLED if busy else tk.NORMAL
        self.btn_submit.configure(state=state)
        self.btn_select.configure(state=state)
        if not busy:
            self._update_buttons()

    def _update_buttons(self):
        has_modifications = bool(self.modified_data)
        self.btn_save.configure(state=tk.NORMAL if has_modifications else tk.DISABLED)
        self.btn_discard.configure(state=tk.NORMAL if has_modifications else tk.DISABLED)

    def _set_status(self, text):
        self.lbl_status.configure(text=text)

    def _exit_app(self):
        if self.modified_data:
            if not messagebox.askyesno("确认退出", "有未保存的修改，确定退出？"):
                return
        self.root.destroy()


def main():
    root = tk.Tk()
    if IS_WIN:
        from ctypes import windll
        try:
            windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
    app = ExifEditorApp(root)
    root.protocol("WM_DELETE_WINDOW", app._exit_app)
    root.mainloop()


if __name__ == "__main__":
    main()
