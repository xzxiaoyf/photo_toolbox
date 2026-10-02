#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Sony 照片 EXIF 全量信息诊断工具 v2（ttk / clam 风格）

功能：
- 选择任意照片 / 视频（jpg、jpeg、arw、png、tif、heic、mp4、mov …），
  以格式化 JSON 输出该文件的全部标签（EXIF / MakerNotes / Composite / File …）
- 读取在后台线程执行，窗口不卡；读取中按钮自动禁用，避免重复点击
- 结果可一键复制到剪贴板，或保存为 .json / .txt
- 状态栏显示标签数量、耗时；底部常驻显示 exiftool 实际路径

依赖：仅 Python 标准库 + 系统 exiftool 命令行。
（原版 `import exiftool` 用的是 pyexiftool 第三方包，机器上没装就跑不起来，
  换成命令行后源码运行与编译分发都不需要额外装包。）
"""

import json
import os
import queue
import shutil
import subprocess
import sys
import threading
import time
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

APP_TITLE = "Sony 照片 EXIF 全量信息诊断工具 v2"
READ_TIMEOUT = 180          # 秒，大文件（ARW / 长视频）放宽

FILE_TYPES = [
    ("照片 / 视频", "*.jpg *.jpeg *.JPG *.JPEG *.arw *.ARW *.png *.PNG "
                    "*.tif *.tiff *.heic *.HEIC *.heif *.hif *.mp4 *.MP4 *.mov *.MOV *.avi *.mts"),
    ("所有文件", "*.*"),
]


# ============================================================
# exiftool 定位：编译版 / Finder 双击启动时 PATH 常缺
# /opt/homebrew/bin 等目录，PATH 找不到就按常见安装位置兜底
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
        try:   # 最后兜底：问登录 shell（会读到你 .zprofile 里的 PATH）
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
# 读取全部 EXIF 标签
# ============================================================
def read_all_exif(path, timeout=READ_TIMEOUT):
    """返回 (标签字典, 警告文本, 耗时秒)。

    用 `exiftool -j -G -a -s` 读：
      -j  JSON 输出；-G  键名带组名前缀（EXIF:Model、Composite:GPSLatitude）；
      -a  保留同名重复标签；-s  标签名不拆词，与 pyexiftool 的键名完全一致。
    """
    if not os.path.isfile(path):
        raise RuntimeError("文件不存在或不可读：\n%s" % path)

    cmd = [EXIFTOOL, "-j", "-G", "-a", "-s", "-charset", "filename=utf8", path]
    t0 = time.time()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              encoding="utf-8", errors="replace", timeout=timeout)
    except FileNotFoundError:
        raise RuntimeError("找不到 exiftool 命令，请先安装 exiftool。")
    except subprocess.TimeoutExpired:
        raise RuntimeError("读取超时（超过 %d 秒），文件可能过大或已损坏。" % timeout)
    cost = time.time() - t0

    # exiftool 返回码：0 正常；1 有警告但结果可用；>=2 出错
    if proc.returncode >= 2 and not (proc.stdout or "").strip():
        raise RuntimeError((proc.stderr or "").strip() or
                           "exiftool 返回码 %d" % proc.returncode)

    try:
        data = json.loads(proc.stdout)
    except Exception:
        raise RuntimeError("无法解析 exiftool 输出：\n%s"
                           % ((proc.stderr or proc.stdout or "")[:600]))
    if not data:
        raise RuntimeError("exiftool 未返回任何标签。")

    warn = (proc.stderr or "").strip() if proc.returncode == 1 else ""
    return data[0], warn, cost


def format_json(meta, source_path, warn=""):
    """格式化输出：文件头注释 + 原始 JSON（键序与 exiftool 一致）。"""
    head = "// " + os.path.basename(source_path)
    if warn:
        head += "\n// ⚠ exiftool 警告：" + warn.replace("\n", " ")[:200]
    return head + "\n" + json.dumps(meta, indent=4, ensure_ascii=False)


# ============================================================
# 主界面（ttk / clam）
# ============================================================
class SonyExifDiagnosticsGUI:
    def __init__(self, root):
        self.root = root
        self.root.title(APP_TITLE)
        self.root.geometry("900x680")
        self.root.minsize(700, 520)

        self.current_path = None
        self.result_text = ""
        self.busy = False
        self.q = queue.Queue()

        self._setup_style()
        self._build_ui()
        self.root.after(80, self._poll)
        self.root.after(300, self._check_exiftool)

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
        style.configure("Warn.TLabel", font=(UI_FONT, 10), foreground="#c0392b")
        style.configure("Card.TLabelframe", background="#ffffff")
        style.configure("Card.TLabelframe.Label", background=bg,
                        font=(UI_FONT, 11, "bold"))

        style.configure("TButton", font=(UI_FONT, 11), padding=(10, 6))
        style.map("TButton",
                  background=[("active", "#e0e0e0"), ("disabled", "#ededed")])
        style.configure("Accent.TButton", font=(UI_FONT, 11, "bold"),
                        foreground="#ffffff", background="#2196F3",
                        padding=(12, 7))
        style.map("Accent.TButton",
                  background=[("active", "#1976d2"), ("disabled", "#a8cdf0")])
        style.configure("Save.TButton", font=(UI_FONT, 11, "bold"),
                        foreground="#ffffff", background="#4CAF50",
                        padding=(12, 7))
        style.map("Save.TButton",
                  background=[("active", "#45a049"), ("disabled", "#a5d6a7")])
        style.configure("Danger.TButton", font=(UI_FONT, 11, "bold"),
                        foreground="#ffffff", background="#e74c3c",
                        padding=(12, 7))
        style.map("Danger.TButton",
                  background=[("active", "#c0392b"), ("disabled", "#f0a49c")])

    # ---------------------------------------------------------- 布局
    def _build_ui(self):
        outer = ttk.Frame(self.root, padding=(16, 14, 16, 10))
        outer.pack(fill="both", expand=True)

        ttk.Label(outer, text="📷 Sony 照片 EXIF 全量信息诊断工具",
                  style="Title.TLabel").pack(pady=(0, 4))
        ttk.Label(outer, text="选择照片或视频，输出该文件的全部标签（JSON 格式）",
                  style="Hint.TLabel").pack(pady=(0, 12))

        bar = ttk.Frame(outer)
        bar.pack(fill="x", pady=(0, 10))

        self.btn_select = ttk.Button(bar, text="📂 选择照片并查看所有 EXIF 信息",
                                     style="Accent.TButton",
                                     command=self.select_file)
        self.btn_select.pack(side="left")

        self.btn_copy = ttk.Button(bar, text="📋 复制全部",
                                   command=self.copy_all, state="disabled")
        self.btn_copy.pack(side="left", padx=(8, 0))

        self.btn_save = ttk.Button(bar, text="💾 保存为文件", style="Save.TButton",
                                   command=self.save_result, state="disabled")
        self.btn_save.pack(side="left", padx=(8, 0))

        self.btn_exit = ttk.Button(bar, text="❌ 退出程序", style="Danger.TButton",
                                   command=self.on_exit)
        self.btn_exit.pack(side="right")

        card = ttk.Labelframe(outer, text=" EXIF 标签（JSON） ", style="Card.TLabelframe",
                              padding=(8, 6, 8, 8))
        card.pack(fill="both", expand=True)

        self.text = tk.Text(card, wrap="none", font=(MONO_FONT, 13),
                            bg="#ffffff", fg="#2c3e50", relief="flat",
                            padx=10, pady=8, state="disabled",
                            insertbackground="#2c3e50",
                            selectbackground="#bcd7f5")
        vbar = ttk.Scrollbar(card, orient="vertical", command=self.text.yview)
        hbar = ttk.Scrollbar(card, orient="horizontal", command=self.text.xview)
        self.text.configure(yscrollcommand=vbar.set, xscrollcommand=hbar.set)

        self.text.grid(row=0, column=0, sticky="nsew")
        vbar.grid(row=0, column=1, sticky="ns")
        hbar.grid(row=1, column=0, sticky="ew")
        card.rowconfigure(0, weight=1)
        card.columnconfigure(0, weight=1)

        self._show_placeholder()

        bottom = ttk.Frame(outer)
        bottom.pack(fill="x", pady=(8, 0))
        self.status_var = tk.StringVar(value="就绪 — 请选择一张照片或视频")
        ttk.Label(bottom, textvariable=self.status_var,
                  style="Info.TLabel", anchor="w").pack(side="left", fill="x",
                                                        expand=True)
        self.tool_var = tk.StringVar(value="exiftool：%s" % EXIFTOOL)
        ttk.Label(bottom, textvariable=self.tool_var, style="Hint.TLabel",
                  anchor="e").pack(side="right")

    def _show_placeholder(self):
        self._set_text("// 未选择文件。\n"
                       "// 点击左上角「📂 选择照片并查看所有 EXIF 信息」开始。")

    # ---------------------------------------------------------- 文本区
    def _set_text(self, content):
        self.text.configure(state="normal")
        self.text.delete("1.0", tk.END)
        self.text.insert(tk.END, content)
        self.text.configure(state="disabled")

    # ---------------------------------------------------------- 启动检查
    def _check_exiftool(self):
        if EXIFTOOL and os.path.isfile(EXIFTOOL):
            return
        if shutil.which("exiftool"):
            return
        self.tool_var.set("exiftool：未找到 ⚠")
        messagebox.showwarning(
            "未找到 exiftool",
            "本工具需要系统命令行程序 exiftool 才能读取 EXIF。\n\n"
            "macOS  ：brew install exiftool\n"
            "Windows：下载 exiftool.org 的 zip，解压后把 exiftool.exe 加到 PATH\n\n"
            "安装后重新启动本程序即可。")

    # ---------------------------------------------------------- 选择文件
    def select_file(self):
        if self.busy:
            return
        path = filedialog.askopenfilename(title="选择一张照片或视频",
                                          filetypes=FILE_TYPES)
        if not path:
            return
        self.start_read(path)

    # ---------------------------------------------------------- 读取（后台线程）
    def start_read(self, path):
        if self.busy:
            return
        self.busy = True
        self.current_path = path
        self.result_text = ""
        self._set_enabled(False)
        self._set_text("// 正在读取 %s …" % os.path.basename(path))
        self.status_var.set("读取中：%s" % os.path.basename(path))

        t = threading.Thread(target=self._worker, args=(path,), daemon=True)
        t.start()

    def _worker(self, path):
        try:
            meta, warn, cost = read_all_exif(path)
            text = format_json(meta, path, warn)
            self.q.put(("ok", text, len(meta), cost, warn))
        except Exception as e:
            self.q.put(("err", str(e), 0, 0.0, ""))

    def _poll(self):
        try:
            kind, payload, count, cost, warn = self.q.get_nowait()
        except queue.Empty:
            self.root.after(80, self._poll)
            return

        self.busy = False
        self._set_enabled(True)

        if kind == "ok":
            self.result_text = payload
            self._set_text(payload)
            self.btn_copy.configure(state="normal")
            self.btn_save.configure(state="normal")
            msg = "✅ %s — 共 %d 个标签，耗时 %.2f 秒" % (
                os.path.basename(self.current_path), count, cost)
            if warn:
                msg += "（有警告）"
            self.status_var.set(msg)
        else:
            self.result_text = ""
            self.btn_copy.configure(state="disabled")
            self.btn_save.configure(state="disabled")
            self._set_text("// ❌ 读取失败：\n// %s" % payload.replace("\n", "\n// "))
            self.status_var.set("❌ 读取失败：%s" % os.path.basename(self.current_path))
            messagebox.showerror("读取错误",
                                 "无法读取该文件的 EXIF 信息：\n\n%s" % payload)

        self.root.after(80, self._poll)

    def _set_enabled(self, on):
        state = "normal" if on else "disabled"
        self.btn_select.configure(state=state)
        if not on:
            # 读取中：复制/保存先禁用，读完再看结果启用
            self.btn_copy.configure(state="disabled")
            self.btn_save.configure(state="disabled")

    # ---------------------------------------------------------- 复制 / 保存
    def copy_all(self):
        if not self.result_text:
            return
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(self.result_text)
            self.root.update_idletasks()
            self.status_var.set("📋 已复制全部内容到剪贴板（%d 字符）"
                                % len(self.result_text))
        except Exception as e:
            messagebox.showerror("复制失败", str(e))

    def save_result(self):
        if not self.result_text or not self.current_path:
            return
        stem = os.path.splitext(os.path.basename(self.current_path))[0]
        out = filedialog.asksaveasfilename(
            title="保存 EXIF 信息",
            defaultextension=".json",
            initialfile="%s_EXIF.json" % (stem or "exif"),
            filetypes=[("JSON 文件", "*.json"), ("文本文件", "*.txt")])
        if not out:
            return
        try:
            with open(out, "w", encoding="utf-8") as f:
                f.write(self.result_text)
            self.status_var.set("💾 已保存：%s" % out)
        except Exception as e:
            messagebox.showerror("保存失败", "无法写入文件：\n%s\n\n%s" % (out, e))

    # ---------------------------------------------------------- 退出
    def on_exit(self):
        if self.busy and not messagebox.askyesno(
                "正在读取", "EXIF 还在读取中，确定要退出吗？"):
            return
        self.root.destroy()


# ============================================================
if __name__ == "__main__":
    root = tk.Tk()
    SonyExifDiagnosticsGUI(root)
    root.mainloop()
