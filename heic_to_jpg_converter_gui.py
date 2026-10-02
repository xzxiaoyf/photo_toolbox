# -*- coding: utf-8 -*-
"""
heic_to_jpg_converter_gui.py —— HEIC/HEIF/HIF → JPG 批量转换器（tkinter ttk clam 版）

由 wxPython 旧版重写：界面改用 ttk clam 风格（与 bird_scanner.py 同一套观感），
依赖只有 pillow + pillow-heif（不再需要 wx）。

界面：
    源照片目录： [只读输入框显示完整路径] [选择源目录]
    输出JPG目录：[只读输入框显示完整路径] [选择输出目录]
    [提交] [退出]
每张照片的处理结果输出到命令行窗口（终端 / PyCharm 控制台），界面只显示一行状态；
结束后命令行打印统计：照片总数、转换成功数、失败数、耗时。

功能与修复（相对旧版）：
  * 递归扫描源目录（含子目录），输出目录结构与源保持一致
  * EXIF 超过 JPEG 64KB 上限时（小米/iPhone 的 HEIC 常见，实测 285KB）
    旧版会整张失败且界面仍提示「操作完成」→ 现在自动精简 EXIF（保留拍摄
    时间 / 相机 / 曝光 / GPS），转换不再失败
  * 修正方向：手机竖拍的 HEIC 在容器里带 irot 旋转属性，旧版直接搬运
    EXIF 方向标记会转出横倒的图 → 现在解析容器旋转、把像素摆正，
    并把输出 EXIF 方向统一为 1，任何看图软件里方向都正确
  * 保留 ICC 色彩配置文件（Display P3 等），颜色不偏
  * 原子写出（先写临时文件再改名），中途退出不会留下半个文件
  * 同名 JPG 已存在时覆盖并在命令行明确记录，不静默

运行：
    python heic_to_jpg_converter_gui.py                     # 图形界面
    python heic_to_jpg_converter_gui.py --cli 源目录 输出目录  # 命令行批处理
打包：
    pyinstaller -F heic_to_jpg_converter_gui.py
"""

import os
import struct
import sys
import tempfile
import threading
import time
import traceback

import tkinter as tk
from tkinter import ttk, filedialog

import pillow_heif
from PIL import Image

HEIF_EXTS = {".heic", ".heif", ".hif"}
OTHER_IMG_EXTS = {".jpg", ".jpeg", ".jpe", ".jfif", ".png",
                  ".tif", ".tiff", ".bmp", ".gif", ".webp"}
EXIF_LIMIT = 65533          # JPEG APP1 段上限（留余量）
JPEG_QUALITY = 95
DECODE_THREADS = 4          # pillow_heif 多线程解码（24MP 约 0.8s）

try:
    pillow_heif.options.DECODE_THREADS = DECODE_THREADS
except Exception:
    pass


# ============================================================
# HEIF 容器 irot / imir 属性解析（纯标准库，遍历 ISO-BMFF 盒子）
#
# 背景：pillow_heif 解码返回的是【未旋转】的原始像素，旋转信息存在
# 容器的 irot（旋转）/ imir（镜像）属性里，不看容器就会转出横倒的图。
# 标定（3 张小米竖拍样张，与 macOS sips 渲染逐像素比对，差 0.2~0.4/255）：
#   irot 原始值 v → 顺时针旋转 v×90°：
#     v=1 → ROTATE_270(顺90)   v=2 → ROTATE_180   v=3 → ROTATE_90(逆90)
# ============================================================
def _walk_boxes(data, start, end):
    """产出 (type, payload_start, payload_end)。"""
    pos = start
    while pos + 8 <= end:
        size, typ = struct.unpack_from(">I4s", data, pos)
        hdr = 8
        if size == 1:
            size = struct.unpack_from(">Q", data, pos + 8)[0]
            hdr = 16
        elif size == 0:
            size = end - pos
        if size < hdr or pos + size > end:
            break
        yield typ, pos + hdr, pos + size
        pos += size


def parse_heif_transforms(path):
    """返回 (irot_raw 0-3 或 None, imir_axis 0/1 或 None)。"""
    try:
        with open(path, "rb") as f:
            data = f.read()
    except OSError:
        return None, None

    irot = imir = None
    props = []              # [(box_type, payload)]，顺序即属性索引（1 起）
    primary_id = None
    assoc = {}              # item_id -> [属性索引]

    def scan(s, e):
        nonlocal primary_id
        for typ, ps, pe in _walk_boxes(data, s, e):
            if typ == b"meta":                    # FullBox：跳过 4 字节 version/flags
                scan(ps + 4, pe)
            elif typ == b"iprp":
                scan(ps, pe)
            elif typ == b"ipco":
                for t2, p2, e2 in _walk_boxes(data, ps, pe):
                    props.append((t2, data[p2:e2]))
            elif typ == b"pitm":
                ver = data[ps]
                fmt = ">I" if ver >= 1 else ">H"
                primary_id = struct.unpack_from(fmt, data, ps + 4)[0]
            elif typ == b"ipma":
                flags = struct.unpack_from(">I", data, ps)[0] & 0xFFFFFF
                off = ps + 4
                cnt = struct.unpack_from(">I", data, off)[0]
                off += 4
                idsize = 4 if flags & 1 else 2
                for _ in range(cnt):
                    iid = struct.unpack_from(">I" if idsize == 4 else ">H", data, off)[0]
                    off += idsize
                    n = data[off]
                    off += 1
                    lst = []
                    for _k in range(n):
                        if flags & 2:
                            lst.append(struct.unpack_from(">H", data, off)[0] & 0x7FFF)
                            off += 2
                        else:
                            lst.append(data[off] & 0x7F)
                            off += 1
                    assoc[iid] = lst

    for typ, ps, pe in _walk_boxes(data, 0, len(data)):
        if typ == b"meta":
            scan(ps + 4, pe)

    if primary_id is None:
        return None, None
    idx_irot = {i + 1 for i, (t, _) in enumerate(props) if t == b"irot"}
    idx_imir = {i + 1 for i, (t, _) in enumerate(props) if t == b"imir"}
    for pi in assoc.get(primary_id, []):
        if irot is None and pi in idx_irot:
            irot = props[pi - 1][1][0] & 0x03
        elif imir is None and pi in idx_imir:
            imir = props[pi - 1][1][0] & 0x01
    return irot, imir


# ============================================================
# 解码与方向处理
# ============================================================
def decode_heif(path):
    """解码 HEIF。返回 (PIL.Image, exif bytes, icc bytes 或 None)。"""
    h = pillow_heif.open_heif(path, convert_hdr_to_8bit=True)
    img = h.to_pillow()
    if img.mode not in ("RGB", "L"):
        img = img.convert("RGB")
    return img, h.info.get("exif", b""), h.info.get("icc_profile")


def make_upright(img, exif_raw, irot, imir):
    """把像素转正。返回 (img, rotated, 依据说明)。"""
    if irot:                       # 容器旋转优先（实测标定见文件头注释）
        img = img.transpose({1: Image.ROTATE_270,
                             2: Image.ROTATE_180,
                             3: Image.ROTATE_90}[irot])
        return img, True, "容器irot=%d" % irot
    if imir is not None:           # 按 HEIF 规范实现（无实测样本）
        img = img.transpose(Image.FLIP_TOP_BOTTOM if imir == 1
                            else Image.FLIP_LEFT_RIGHT)
        return img, True, "容器imir=%d" % imir
    if exif_raw:                   # 无容器变换时退回 EXIF 方向标记
        try:
            ex = Image.Exif()
            ex.load(exif_raw)
            o = ex.get(0x0112)
            if o in (3, 6, 8):
                img = img.transpose({3: Image.ROTATE_180,
                                     6: Image.ROTATE_270,
                                     8: Image.ROTATE_90}[o])
                return img, True, "EXIF方向=%d" % o
        except Exception:
            pass
    return img, False, ""


def build_exif(exif_raw, rotated):
    """决定输出的 EXIF 字节。返回 (bytes, 说明)。

    原样放得下且没动过像素方向 → 原样保留（保真最高）；
    否则用 PIL 重建：保留拍摄时间/相机/曝光/GPS，去掉 MakerNotes、
    内嵌缩略图、XMP（这三样是把 EXIF 撑过 64KB 限高的元凶），
    方向标记归一为 1（像素已摆正）。
    """
    if exif_raw and len(exif_raw) <= EXIF_LIMIT and not rotated:
        return exif_raw, "EXIF原样(%dB)" % len(exif_raw)
    try:
        ex = Image.Exif()
        if exif_raw:
            ex.load(exif_raw)
        if rotated:
            ex[0x0112] = 1
        ex.get_ifd(0x8769).pop(0x927C, None)          # MakerNotes
        for t in (0x0201, 0x0202, 0x02BC):            # 缩略图指针 / XMP
            ex.pop(t, None)
        blob = ex.tobytes()
        if len(blob) <= EXIF_LIMIT:
            note = ("EXIF精简(%d→%dB)" % (len(exif_raw), len(blob))
                    if exif_raw else "新建EXIF(%dB)" % len(blob))
            return blob, note
    except Exception:
        pass
    return b"", "EXIF无法保留"


def convert_one(src, dst, log=None):
    """转换单张。返回 (True, 耗时ms, 说明) 或 (False, 0, 失败原因)。"""
    t0 = time.perf_counter()
    try:
        img, exif_raw, icc = decode_heif(src)
        irot, imir = parse_heif_transforms(src)
        img, rotated, why = make_upright(img, exif_raw, irot, imir)
        exif_blob, ex_note = build_exif(exif_raw, rotated)
        kwargs = {"format": "JPEG", "quality": JPEG_QUALITY}
        if exif_blob:
            kwargs["exif"] = exif_blob
        if icc:
            kwargs["icc_profile"] = icc
        # 原子写出：同目录临时文件 → 改名（中途退出不留半个文件）
        fd, tmp = tempfile.mkstemp(dir=os.path.dirname(dst) or ".",
                                   prefix=".jpg_", suffix=".tmp")
        os.close(fd)
        try:
            img.save(tmp, **kwargs)
            os.chmod(tmp, 0o644)
            os.replace(tmp, dst)
        except Exception:
            if os.path.exists(tmp):
                os.remove(tmp)
            raise
        ms = int((time.perf_counter() - t0) * 1000)
        note = "；".join(x for x in (why, ex_note) if x)
        return True, ms, note
    except Exception as e:
        if log:
            log("    原因: %s: %s" % (type(e).__name__, e))
        return False, 0, "%s: %s" % (type(e).__name__, e)


# ============================================================
# 批量扫描（GUI 与 --cli 共用）
# ============================================================
def collect_files(src):
    """递归收集。返回 (heif列表[(绝对路径, 相对目录)], 其他图片数)。"""
    heif, others = [], 0
    for dirpath, _dirnames, filenames in os.walk(src):
        for fn in filenames:
            ext = os.path.splitext(fn)[1].lower()
            if ext in HEIF_EXTS:
                heif.append((os.path.join(dirpath, fn),
                             os.path.relpath(dirpath, src)))
            elif ext in OTHER_IMG_EXTS:
                others += 1
    heif.sort()
    return heif, others


def convert_directory(src, dst, log=print):
    """批量转换。返回统计 dict。"""
    t_all = time.perf_counter()
    pairs, n_other = collect_files(src)
    log("=" * 72)
    log("源目录: %s" % src)
    log("输出目录: %s" % dst)
    log("递归扫描：HEIC/HEIF/HIF 共 %d 张%s"
        % (len(pairs), "（另有其它图片 %d 张，不处理）" % n_other if n_other else ""))
    if not pairs:
        log("没有找到需要转换的 HEIC/HEIF/HIF 文件。")
        return {"found": 0, "ok": 0, "fail": 0, "overwrite": 0,
                "other": n_other, "elapsed": 0.0}

    os.makedirs(dst, exist_ok=True)
    n_ok = n_fail = n_over = 0
    for i, (path, rel) in enumerate(pairs, 1):
        name = os.path.basename(path)
        stem = os.path.splitext(name)[0]
        out_dir = os.path.normpath(os.path.join(dst, rel))
        os.makedirs(out_dir, exist_ok=True)
        dst_path = os.path.join(out_dir, stem + ".jpg")
        existed = os.path.exists(dst_path)
        ok, ms, note = convert_one(path, dst_path, log=log)
        rel_show = os.path.join(rel, stem + ".jpg") if rel else stem + ".jpg"
        if ok:
            n_ok += 1
            if existed:
                n_over += 1
                log("[%3d/%d] %-24s ✓ %-24s 覆盖已有文件（%d ms）%s"
                    % (i, len(pairs), name, rel_show, ms,
                       ("；" + note) if note else ""))
            else:
                log("[%3d/%d] %-24s ✓ %-24s %4d ms %s"
                    % (i, len(pairs), name, rel_show, ms,
                       ("；" + note) if note else ""))
        else:
            n_fail += 1
            log("[%3d/%d] %-24s ✗ %s" % (i, len(pairs), name, note))

    elapsed = time.perf_counter() - t_all
    log("-" * 72)
    log("统计：照片共 %d 张（HEIC/HEIF/HIF %d 张 + 其它图片 %d 张）"
        % (len(pairs) + n_other, len(pairs), n_other))
    log("      转换成功 %d 张，失败 %d 张%s，耗时 %.1f 秒"
        % (n_ok, n_fail,
           "（覆盖已有同名 JPG %d 张）" % n_over if n_over else "",
           elapsed))
    return {"found": len(pairs), "ok": n_ok, "fail": n_fail,
            "overwrite": n_over, "other": n_other,
            "elapsed": round(elapsed, 1)}


# ============================================================
# 图形界面（ttk clam，与 bird_scanner.py 同风格）
# ============================================================
def run_gui():
    root = tk.Tk()
    root.title("HEIC/HEIF/HIF → JPG 批量转换器")
    style = ttk.Style(root)
    style.theme_use("clam")
    root.configure(bg=style.lookup("TFrame", "background") or "#DCDAD5")

    frm = ttk.Frame(root, padding=14)
    frm.grid(row=0, column=0, sticky="nsew")

    var_src = tk.StringVar()
    var_dst = tk.StringVar()
    var_status = tk.StringVar(value="空闲（结果输出到命令行窗口）")

    # ---- 源目录行 ----
    ttk.Label(frm, text="源照片目录：").grid(row=0, column=0, sticky="e")
    ttk.Entry(frm, textvariable=var_src, width=52, state="readonly"
              ).grid(row=0, column=1, sticky="we", padx=6, pady=3)

    # ---- 输出目录行 ----
    ttk.Label(frm, text="输出JPG目录：").grid(row=1, column=0, sticky="e")
    ttk.Entry(frm, textvariable=var_dst, width=52, state="readonly"
              ).grid(row=1, column=1, sticky="we", padx=6, pady=3)

    frm.columnconfigure(1, weight=1)

    # ---- 状态行 ----
    ttk.Label(frm, textvariable=var_status
              ).grid(row=2, column=0, columnspan=2, sticky="w", pady=(6, 8))

    state = {"running": False, "msg": None}

    def choose(which):
        d = filedialog.askdirectory(title="选择源照片目录" if which == "src"
                                    else "选择输出 JPG 目录")
        if d:
            (var_src if which == "src" else var_dst).set(d)

    def set_buttons(running):
        st = "disabled" if running else "normal"
        for b in (btn_src, btn_dst, btn_ok, btn_quit):
            b.config(state=st)

    def worker(src, dst):
        """后台线程：只写普通变量，绝不碰任何 Tk 对象（跨线程调 Tk 不可靠）。"""
        try:
            stats = convert_directory(src, dst, log=print)
            if stats["found"] == 0:
                state["msg"] = "完成：目录里没有 HEIC/HEIF/HIF 文件"
            else:
                state["msg"] = ("完成：转换 %d/%d 张，失败 %d 张，耗时 %.1f 秒"
                                "（详见命令行）"
                                % (stats["ok"], stats["found"], stats["fail"],
                                   stats["elapsed"]))
        except Exception:
            state["msg"] = "出错：%s" % traceback.format_exc(limit=1).strip()
        state["running"] = False

    def poll():
        """主线程轮询：把后台结果搬到界面，保证 Tk 调用都在主线程。"""
        if state["running"]:
            root.after(200, poll)
            return
        if state["msg"]:
            var_status.set(state["msg"])
            state["msg"] = None
        set_buttons(False)

    def submit():
        if state["running"]:
            return
        src, dst = var_src.get().strip(), var_dst.get().strip()
        if not src:
            var_status.set("请先选择源照片目录")
            return
        if not dst:
            var_status.set("请先选择输出 JPG 目录")
            return
        if not os.path.isdir(src):
            var_status.set("源照片目录不存在：%s" % src)
            return
        # 输出目录不存在时自动创建（convert_directory 里有 makedirs）
        state["running"] = True
        set_buttons(True)
        var_status.set("转换中…（结果输出到命令行窗口）")
        threading.Thread(target=worker, args=(src, dst), daemon=True).start()
        root.after(200, poll)

    # ---- 按钮行（同一行） ----
    btn_row = ttk.Frame(frm)
    btn_row.grid(row=3, column=0, columnspan=2, sticky="w")
    btn_src = ttk.Button(btn_row, text="选择源目录",
                         command=lambda: choose("src"))
    btn_src.pack(side="left", padx=(0, 8))
    btn_dst = ttk.Button(btn_row, text="选择输出目录",
                         command=lambda: choose("dst"))
    btn_dst.pack(side="left", padx=(0, 8))
    btn_ok = ttk.Button(btn_row, text="提交", command=submit)
    btn_ok.pack(side="left", padx=(0, 8))
    btn_quit = ttk.Button(btn_row, text="退出", command=root.destroy)
    btn_quit.pack(side="left")

    root.mainloop()


# ============================================================
# 入口
# ============================================================
def main():
    if len(sys.argv) >= 4 and sys.argv[1] == "--cli":
        src, dst = sys.argv[2], sys.argv[3]
        if not os.path.isdir(src):
            print("源目录不存在：%s" % src)
            sys.exit(2)
        stats = convert_directory(src, dst, log=print)
        sys.exit(0 if stats["fail"] == 0 else 1)
    if "--cli" in sys.argv:
        print("用法：%s --cli 源目录 输出目录" % sys.argv[0])
        sys.exit(2)
    run_gui()


if __name__ == "__main__":
    main()
