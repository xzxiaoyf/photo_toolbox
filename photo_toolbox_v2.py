#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
摄影工具箱 - 主程序 v2
通过菜单栏和按钮调用各子工具程序。

两种运行方式：
1. 直接执行 py：       python3 photo_toolbox_v2.py
   子程序 .py 与本文件放同一目录，用当前解释器启动。

2. PyInstaller 编译后：子程序也各自编译成可执行文件，
   与主程序放同一目录（或 tools/ 子目录），主程序直接启动它们：
     Windows:  gps_write_photo_v2.exe
     macOS:    gps_write_photo_v2（Unix 可执行）
               或 gps_write_photo_v2.app/Contents/MacOS/gps_write_photo_v2
   一键编译脚本见 build_toolbox_mac.sh / build_toolbox_win.bat
"""
# 每个子工具（Windows 加 --windowed 去黑窗）
# pyinstaller --onefile -n gps_write_photo_v2 gps_write_photo_v2.py
# 主程序
# pyinstaller --onefile --windowed -n PhotoToolbox photo_toolbox_v2.py


import tkinter as tk
from tkinter import messagebox
import subprocess
import sys
import os

# ============================================================
# 目录解析：直接跑 .py 用脚本目录；编译后用 exe/.app 所在目录
# （PyInstaller 下 __file__ 指向临时解包目录，不可用于找子程序）
# ============================================================
def get_base_dir():
    if getattr(sys, "frozen", False):
        exe = os.path.abspath(sys.executable)
        d = os.path.dirname(exe)              # .../Xxx.app/Contents/MacOS 或 exe 目录
        bundle = os.path.dirname(os.path.dirname(d))
        if sys.platform == "darwin" and bundle.endswith(".app"):
            return os.path.dirname(bundle)    # .app 包所在目录
        return d
    return os.path.dirname(os.path.abspath(__file__))


# ============================================================
# 工具定义：(菜单/按钮名称, 脚本文件名, 说明文字)
# 如需新增工具，在此列表追加一行即可
# ============================================================
TOOLS = [
    ("📍 GPS轨迹写入照片",        "gps_write_photo_v2.py",
     "GPX/TCX/FIT轨迹GPS信息写入照片"),
    ("🗺️ 高德地图显示拍摄位置",    "photo_exif_viewer_v2.py",
     "在高德地图上查看照片拍摄位置"),
    ("🗺️ 在地图上显示运动轨迹及拍摄位置", "photo_track_map_v3.py",
     "在地图上显示运动轨迹及拍摄位置"),
    ("📷 Sony快门数查询",          "sony_exif_shutter_v2.py",
     "读取Sony相机实际拍摄快门数"),
    ("📋 相机EXIF信息读取",        "sony_exif_reader_v2.py",
     "读取相机照片的全部EXIF信息"),
    ("⏱️ GPX时间修正(UTC+8→UTC)", "xiaomi_time_corrector_v2.py",
     "小米GPS轨迹时间修正工具"),
    ("⏱️ GPX/TCX 轨迹插值补全工具", "gpx_track_interpolator_v2.py",
     "小米GPS轨迹插值补全工具"),
    ("⏱️ GPX 轨迹方向反转工具", "gpx_reverser2.py",
     "GPX 轨迹方向反转工具"),
    ("⏱️ 照片按拍摄年月分类存放", "photo_classifier3.py",
     "照片按拍摄年月分类存放"),
    ("⏱️ 照片按 GPS地点+日期 分类工具", "photo_gps_classifier5.py",
     "照片按 GPS地点+日期 分类工具"),
    ("⏱️ 修改照片的EXIF信息", "edit_exif3.py",
     "修改照片的EXIF信息"),
    ("⏱️ 照片 GPS 坐标管理工具", "photo_gps_manager4.py",
     "照片 GPS 坐标管理工具"),
    ("⏱️ HEIC/HEIF/HIF → JPG 批量转换器", "heic_to_jpg_converter_gui.py",
     "HEIC/HEIF/HIF → JPG 批量转换器"),
    ("⏱️ 鸟类照片批量识别", "bird_scanner.py",
     "鸟类照片批量识别"),
    ("⏱️ 运动轨迹格式互转工具", "track_converter.py",
     "GPX / TCX / FIT 三种格式任意互转"),
    ("iPhone/iPad 照片批量导出到 Mac 工具 v3", "iphone_photo_exporter.py",
     "iPhone/iPad 照片批量导出到 Mac 工具 v3"),
    ("Android 手机照片/视频批量导出到电脑工具", "android_photo_exporter.py",
     "Android 手机照片/视频批量导出到电脑工具"),
]


def _tool_stem(script):
    """'gps_write_photo_v2.py' → 'gps_write_photo_v2'（编译产物名）。"""
    return script[:-3] if script.endswith(".py") else script


def child_env():
    """子进程环境：补上 Finder/GUI 启动时丢失的常见可执行目录，
    保证子工具里的 exiftool 等裸命令能找到。"""
    env = os.environ.copy()
    if sys.platform == "darwin":
        extra = "/opt/homebrew/bin:/usr/local/bin:/opt/local/bin:"
        if extra not in env.get("PATH", ""):
            env["PATH"] = extra + env.get("PATH", "")
    elif sys.platform == "win32":
        extra = r"C:\Program Files\exiftool;"
        if extra not in env.get("PATH", ""):
            env["PATH"] = extra + env.get("PATH", "")
    return env


def find_frozen_tool(script, base_dir=None):
    """编译模式下定位子工具可执行文件，找到返回完整路径，否则 None。
    搜索顺序：主程序目录 → tools/ 子目录。
    支持：xxx.exe(Windows) / xxx(Unix可执行) / xxx.app 包(macOS)。"""
    stem = _tool_stem(script)
    base = base_dir if base_dir is not None else get_base_dir()
    search = [base, os.path.join(base, "tools")]
    names = [stem + ".exe", stem] if sys.platform == "win32" \
        else [stem, stem + ".exe"]
    cands = [os.path.join(d, n) for d in search for n in names]
    if sys.platform == "darwin":
        cands += [os.path.join(d, stem + ".app", "Contents", "MacOS", stem)
                  for d in search]
    for p in cands:
        if os.path.isfile(p) and os.access(p, os.X_OK):
            return p
    return None


class MainApp:
    def __init__(self, root):
        self.root = root
        self.root.title("🧰 摄影工具箱")
        self.root.geometry("560x770")
        self.root.resizable(False, False)

        self.frozen = bool(getattr(sys, "frozen", False))

        # 记录已启动的子进程 {脚本名: Popen对象}
        self.processes = {}

        self._build_menu()
        self._build_body()

    # ---------------------------------------------------------- 菜单栏
    def _build_menu(self):
        menubar = tk.Menu(self.root)

        # ---- 工具箱下拉菜单 ----
        tool_menu = tk.Menu(menubar, tearoff=0)
        for name, script, desc in TOOLS:
            tool_menu.add_command(
                label=name,
                command=lambda s=script, n=name, d=desc: self._launch(s, n, d)
            )
        menubar.add_cascade(label="🔧 工具箱", menu=tool_menu)

        # ---- 帮助菜单 ----
        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label="🔍 子程序检查",
                              command=self._check_tools)
        help_menu.add_command(label="关于", command=self._show_about)
        menubar.add_cascade(label="❓ 帮助", menu=help_menu)

        # ---- 退出菜单（独立顶级菜单项） ----
        menubar.add_command(label="❌ 退出", command=self._exit)

        self.root.config(menu=menubar)

    # ---------------------------------------------------------- 主界面
    def _build_body(self):
        main = tk.Frame(self.root, padx=20, pady=15)
        main.pack(fill=tk.BOTH, expand=True)

        # 标题
        tk.Label(main, text="🧰 摄影工具箱",
                 font=("Microsoft YaHei", 18, "bold")).pack(pady=(0, 18))

        # 工具按钮 + 说明
        for name, script, desc in TOOLS:
            row = tk.Frame(main)
            row.pack(fill=tk.X, pady=5)

            tk.Button(
                row, text=name, width=26, anchor="w",
                font=("Microsoft YaHei", 12),
                command=lambda s=script, n=name, d=desc: self._launch(s, n, d)
            ).pack(side=tk.LEFT)

            tk.Label(row, text=desc, foreground="gray",
                     font=("Microsoft YaHei", 10)).pack(
                side=tk.LEFT, padx=(10, 0))

        # 底部状态栏
        self.status_var = tk.StringVar(value="就绪 — 点击菜单或按钮启动工具")
        tk.Label(main, textvariable=self.status_var,
                 foreground="blue", anchor="w",
                 font=("Microsoft YaHei", 10)).pack(
            side=tk.BOTTOM, fill=tk.X, pady=(12, 0))

    # ---------------------------------------------------------- 启动子程序
    def _launch(self, script, name, desc):
        if self.frozen:
            self._launch_frozen(script, name)
        else:
            self._launch_script(script, name)

    # ---- 方式1：py 源码方式，用当前解释器启动 ----
    def _launch_script(self, script, name):
        script_path = os.path.join(get_base_dir(), script)

        # 检查文件是否存在
        if not os.path.isfile(script_path):
            messagebox.showerror(
                "文件未找到",
                f"找不到脚本文件：\n{script_path}\n\n"
                f"请确认 {script} 与本主程序在同一目录下。")
            return

        # 检查是否已在运行
        if script in self.processes:
            proc = self.processes[script]
            if proc.poll() is None:
                messagebox.showinfo("提示", f"「{name}」已在运行中")
                return

        # 启动子进程
        try:
            kwargs = {"cwd": os.path.dirname(script_path),
                      "env": child_env()}
            # Windows下隐藏子进程控制台黑窗口
            if sys.platform == "win32":
                kwargs["creationflags"] = getattr(
                    subprocess, "CREATE_NO_WINDOW", 0)

            proc = subprocess.Popen(
                [sys.executable, script_path], **kwargs)

            self.processes[script] = proc
            self.status_var.set(f"✅ 已启动：{name}")
            print(f"[启动] {name} -> {script_path}  (PID: {proc.pid})")

        except Exception as e:
            messagebox.showerror("启动失败", f"{name}\n错误：{e}")

    # ---- 方式2：编译后，直接运行子工具的可执行文件 ----
    def _launch_frozen(self, script, name):
        tool = find_frozen_tool(script)

        if tool is None:
            stem = _tool_stem(script)
            base = get_base_dir()
            if sys.platform == "win32":
                expect = f"{stem}.exe"
            elif sys.platform == "darwin":
                expect = f"{stem}（Unix可执行）或 {stem}.app"
            else:
                expect = stem
            messagebox.showerror(
                "子程序未找到",
                f"找不到「{name}」的编译产物：{expect}\n\n"
                f"查找位置：\n"
                f"  {base}\n"
                f"  {os.path.join(base, 'tools')}\n\n"
                f"请先用 PyInstaller 编译 {script}，"
                f"把生成的可执行文件放到主程序同目录（或 tools/ 子目录）。")
            return

        # 检查是否已在运行
        if script in self.processes:
            proc = self.processes[script]
            if proc.poll() is None:
                messagebox.showinfo("提示", f"「{name}」已在运行中")
                return

        try:
            kwargs = {"cwd": os.path.dirname(tool),
                      "env": child_env()}
            if sys.platform == "win32":
                kwargs["creationflags"] = getattr(
                    subprocess, "CREATE_NO_WINDOW", 0)
            proc = subprocess.Popen([tool], **kwargs)
            self.processes[script] = proc
            self.status_var.set(f"✅ 已启动：{name}")
            print(f"[启动] {name} -> {tool}  (PID: {proc.pid})")
        except Exception as e:
            messagebox.showerror("启动失败", f"{name}\n错误：{e}")

    # ---------------------------------------------------------- 子程序检查
    def _check_tools(self):
        base = get_base_dir()
        lines = []
        if self.frozen:
            lines.append(f"运行方式：编译版（主程序目录：{base}）\n")
            for name, script, _ in TOOLS:
                p = find_frozen_tool(script)
                if p:
                    lines.append(f"✅ {name}\n    {p}")
                else:
                    stem = _tool_stem(script)
                    lines.append(f"❌ {name}\n    缺编译产物：{stem}.exe / {stem}"
                                 f"（源文件 {script}）")
        else:
            lines.append(f"运行方式：Python 源码（目录：{base}）\n")
            for name, script, _ in TOOLS:
                p = os.path.join(base, script)
                lines.append(f"{'✅' if os.path.isfile(p) else '❌'} {name}"
                             f"{'（缺 ' + script + '）' if not os.path.isfile(p) else ''}")
        messagebox.showinfo("子程序检查", "\n".join(lines))

    # ---------------------------------------------------------- 关于
    def _show_about(self):
        tool_list = "\n".join(f"  • {name}" for name, _, _ in TOOLS)
        mode = "编译版" if self.frozen else "Python 源码版"
        messagebox.showinfo(
            "关于",
            f"🧰 摄影工具箱 v2.0（{mode}）\n\n"
            f"集成工具：\n{tool_list}\n\n"
            f"编译版：各子工具的可执行文件需与主程序同目录\n"
            f"（或放在 tools/ 子目录）。\n"
            f"Python: {sys.version.split()[0]}")

    # ---------------------------------------------------------- 退出
    def _exit(self):
        # 收集仍在运行的子进程
        running = []
        for script, proc in self.processes.items():
            if proc.poll() is None:
                for name, s, _ in TOOLS:
                    if s == script:
                        running.append(name)
                        break

        if running:
            msg = "以下工具仍在运行：\n\n"
            msg += "\n".join(f"  • {n}" for n in running)
            msg += "\n\n确定要退出并关闭所有子程序吗？"
            if not messagebox.askyesno("确认退出", msg):
                return
            # 终止所有子进程
            for script, proc in self.processes.items():
                if proc.poll() is None:
                    try:
                        proc.terminate()
                    except Exception:
                        pass

        self.root.destroy()


# ============================================================
if __name__ == "__main__":
    root = tk.Tk()
    MainApp(root)
    root.mainloop()
