# -*- coding: utf-8 -*-
"""bird_scanner.py — 鸟类照片批量识别（本地模型，不上云）。

功能：
  1. GUI（ttk / clam 风格）选择照片目录，显示完整路径；
  2. 点「提交」后在后台线程扫描目录内全部照片，YOLO 检测 + s1v2 分类；
  3. 每张照片的处理结果实时输出到【控制台】（不在界面刷屏）；
  4. 结束后在控制台打印统计（处理多少张、识别多少张、耗时）；
  5. 识别命中的照片写入边车 JSON（<照片名>.bird.json，供地图工具读取），
     并在照片目录生成汇总 birds_report.json。

判定门槛（实测校准）：
  整图检测候选 >= 0.30；确认检出鸟需 检测置信 >= 0.50 且 校正后分类 >= 20%。
  整图无确认鸟时自动 2x2 分块检测兜底（小目标/远距离）；
  分块高分但分类低分的记「疑似」（det>=0.40 且 校正后分类>=5%）供人工复核。
  物种结论按《中国观鸟年报-中国鸟类名录 10.0》做地域校正（top1 为
  非中国分布种时取 top5 中最靠前的中国种，原始 top5 始终保留）。

依赖：onnxruntime + opencv-python + numpy（venv 已具备），模型在 bird_id_models/。
也可命令行静默跑：python bird_scanner.py --cli <照片目录>
"""
import json
import sys
import threading
import time
from datetime import datetime
from pathlib import Path

import cv2
import numpy as np
import onnxruntime as ort

# ---------------------------------------------------------------- 常量
BASE_DIR = Path(__file__).resolve().parent
EXTS = {".jpg", ".jpeg", ".png", ".bmp", ".tif", ".tiff",
        ".hif", ".heic", ".heif"}   # hif: Sony HEIF；heic/heif: iPhone 等


def find_model_dir():
    """按优先级自动定位 bird_id_models/（脚本目录 → 当前目录 → 备用位置）。"""
    candidates = [
        BASE_DIR / "bird_id_models",
        Path.cwd() / "bird_id_models",
        Path("/Volumes/ssknvme512/WorkBuddy/2026-09-28-11-52-07/bird_id_models"),
    ]
    for c in candidates:
        if (c / "yolo_bird_detect.onnx").exists() and (c / "s1v2_bird_cls.onnx").exists():
            return c
    raise FileNotFoundError(
        "找不到模型目录 bird_id_models/（需要 yolo_bird_detect.onnx + s1v2_bird_cls.onnx）。\n"
        "  已尝试的位置：\n" +
        "".join("    - %s\n" % c for c in candidates) +
        "  解决办法：把 bird_id_models 文件夹整个拷到 bird_scanner.py 旁边即可。"
    )

DET_IMGSZ = 640
CLS_IMGSZ = 224
MEAN = np.array([0.485, 0.456, 0.406], dtype=np.float32).reshape(3, 1, 1)
STD = np.array([0.229, 0.224, 0.225], dtype=np.float32).reshape(3, 1, 1)

DET_CONF_CAND = 0.30    # 整图检测候选门槛
DET_CONF_OK = 0.50      # 判定检出鸟：检测置信
CLS_CONF_OK = 20.0      # 判定检出鸟：校正后分类 top-1（%）
MAX_BIRDS = 5           # 单张最多细分类的目标数（防鸟群爆量）

# —— 二轮增强（v2）：分块检测兜底 + 中国分布校正 + 疑似档 ——
TILE_CONF_CAND = 0.20   # 分块检测候选门槛（分块后目标占比变大，可放宽）
TILE_DET_OK = 0.45      # 分块检测的「确认检出鸟」门槛（分块框更贴合，略降）
SUSPECT_DET = 0.40      # 「疑似」：分块检测置信
SUSPECT_CLS = 5.0       # 「疑似」：校正后分类置信（%）
REGION_MIN_PICK = 5.0   # 校正种可信下限（%）：低于此值保留原判并标注非中国分布

# —— 三轮增强（v3）：异域类群黑名单（治荷花/蜻蜓类误检） ——
# 分类器对不认识的物体（荷花苞、蜻蜓）也会给出高分答案，且物种「随机」；
# 但实测（20260822 目录 21 案例逐张人眼复核）规律极其一致：
#   · 误检 15 处的 top1 全部属于「中国完全没有分布的类群」（蜂鸟/极乐鸟/
#     唐纳雀/美洲鹃/红鹳等）——分类器把不认识的东西往异域奇种上猜；
#   · 真鸟 6 处的 top1 类群（麻雀/鸭/鹭/鸥）中国都有分布，哪怕种名被认错。
# 因此 top1 命中以下关键词时直接判「非鸟」丢弃。仅查原始 top1，不动 top5，
# 故不影响地域校正；'剪嘴鸥''鹦鹉'刻意不入单（中国或有记录/有归化种群，
# 且实测为真鸟的合理误认）。
ABSENT_GROUP_KWS = (
    "蜂鸟", "极乐鸟", "园丁鸟", "琴鸟",              # 美洲/大洋洲特有
    "唐纳雀", "裸鼻雀", "森莺", "拟鹂", "拟椋鸟",    # 美洲雀形目各科
    "拾叶雀", "灶鸟", "砍林鸟", "霸鹟", "伞鸟",
    "蚁鸟", "娇鹟", "侏儒鸟",
    "美洲鹃", "美洲鹫", "美洲鸵",
    "巨嘴鸟",                                    # 巨嘴鸟科，美洲特有（中国犀鸟不算）
    "带鹀",                                        # 新大陆雀鹀类
    "红鹳", "火烈鸟",                               # 中国无野生火烈鸟
    "鸸鹋", "鹤鸵", "几维", "食火鸡",
)
# 阈值依据（云龙湖 55 张实测）：苍鹭正确答案 6.1% 能过线被救回；
# 而鸥类照片 top5 里的鹭类干扰候选 3.4% 被挡住，保留原判更诚实。
# 设计原则（实测得出）：
#  ·「是不是鸟」看原始 top1 分类分——分类器对飞行姿态常给错种名但分数不低；
#  ·「是什么鸟」才做中国分布校正——实测两次把错误 top1（雪鹭/南美绿鹭）
#    纠正成视觉正确的夜鹭（依据《中国观鸟年报-中国鸟类名录 10.0》1501 种，
#    bird_id_models/china_birds_v10.txt）；原始 top5 始终保留可复核；
#  · 整图无确认鸟时自动 2x2 分块检测兜底（检测输入固定 640，整图压缩 ~10 倍
#    导致远距离小目标漏检，实测 DSC01110 苍鹭整图 0.185 → 分块 0.55）。


# ---------------------------------------------------------------- 模型
def load_pairs(model_dir):
    en = (model_dir / "labels_10753.txt").read_text(encoding="utf-8").splitlines()
    cn = (model_dir / "labels_cn_10753.txt").read_text(encoding="utf-8").splitlines()
    src = cn if any("\u4e00" <= c <= "\u9fff" for c in cn[0]) else en
    pairs = []
    for line in src:
        parts = line.split("\t")
        if len(parts) >= 2:
            pairs.append((parts[0].strip(), parts[1].strip()))
        else:
            pairs.append((line.strip(), ""))
    return pairs


def make_session(path):
    opts = ort.SessionOptions()
    opts.intra_op_num_threads = 2
    opts.graph_optimization_level = ort.GraphOptimizationLevel.ORT_ENABLE_ALL
    return ort.InferenceSession(str(path), opts, providers=["CPUExecutionProvider"])


# ---------------------------------------------------------------- 推理
_HEIF_READY = False


def _init_heif():
    """按需启用 HEIF/HIF 解码（可选依赖 pillow_heif；OpenCV 不带 HEIF 支持）。"""
    global _HEIF_READY
    if _HEIF_READY:
        return True
    try:
        import pillow_heif
        try:
            pillow_heif.options.DECODE_THREADS = 4   # 24MP HIF 约 0.8s（默认更慢）
        except Exception:
            pass
        pillow_heif.register_heif_opener()
        _HEIF_READY = True
    except ImportError:
        _HEIF_READY = False
    return _HEIF_READY


def imread_unicode(path):
    """兼容中文/特殊字符路径的图片读取（cv2.imread 在部分平台不支持）。

    JPEG/PNG 等走 OpenCV；OpenCV 解不开的 HEIF 容器（Sony .HIF、
    iPhone .HEIC 等）自动回退 pillow_heif，统一返回 BGR。
    """
    data = np.fromfile(str(path), dtype=np.uint8)
    if data.size == 0:
        return None
    img = cv2.imdecode(data, cv2.IMREAD_COLOR)
    if img is not None:
        return img
    if Path(path).suffix.lower() not in (".hif", ".heic", ".heif"):
        return None
    if not _init_heif():
        return None
    try:
        from PIL import Image
        with Image.open(str(path)) as im:
            rgb = np.asarray(im.convert("RGB"))
        return cv2.cvtColor(rgb, cv2.COLOR_RGB2BGR)
    except Exception:
        return None


def preprocess_det(img):
    h, w = img.shape[:2]
    scale = min(DET_IMGSZ / w, DET_IMGSZ / h)
    nw, nh = int(w * scale), int(h * scale)
    resized = cv2.resize(img, (nw, nh))
    canvas = np.full((DET_IMGSZ, DET_IMGSZ, 3), 114, dtype=np.uint8)
    dx, dy = (DET_IMGSZ - nw) // 2, (DET_IMGSZ - nh) // 2
    canvas[dy:dy + nh, dx:dx + nw] = resized
    blob = canvas[:, :, ::-1].transpose(2, 0, 1).astype(np.float32) / 255.0
    return blob[np.newaxis], scale, dx, dy


def iou(a, b):
    x1, y1 = max(a[0], b[0]), max(a[1], b[1])
    x2, y2 = min(a[2], b[2]), min(a[3], b[3])
    inter = max(0, x2 - x1) * max(0, y2 - y1)
    aa = (a[2] - a[0]) * (a[3] - a[1])
    bb = (b[2] - b[0]) * (b[3] - b[1])
    return inter / (aa + bb - inter + 1e-6)


def detect(det_sess, img, conf_thr=DET_CONF_CAND, iou_thr=0.5):
    blob, scale, dx, dy = preprocess_det(img)
    out = det_sess.run(None, {det_sess.get_inputs()[0].name: blob})[0]
    if out.ndim == 3:
        out = out[0].T
    cands = []
    for det in out:
        if len(det) < 5:
            continue
        cx, cy, bw, bh = det[:4]
        conf = det[4] if len(det) == 5 else det[4:].max()
        if conf < conf_thr:
            continue
        x1 = int((cx - bw / 2 - dx) / scale)
        y1 = int((cy - bh / 2 - dy) / scale)
        x2 = int((cx + bw / 2 - dx) / scale)
        y2 = int((cy + bh / 2 - dy) / scale)
        cands.append((x1, y1, x2, y2, float(conf)))
    cands.sort(key=lambda x: -x[4])
    keep = []
    while cands:
        best = cands.pop(0)
        keep.append(best)
        cands = [r for r in cands if iou(best, r) < iou_thr]
    return keep


def classify(cls_sess, pairs, crop, topk=5):
    img = cv2.resize(crop, (CLS_IMGSZ, CLS_IMGSZ))
    img = img[:, :, ::-1].transpose(2, 0, 1).astype(np.float32) / 255.0
    img = (img - MEAN) / STD
    logits = cls_sess.run(None, {cls_sess.get_inputs()[0].name: img[np.newaxis]})[0][0]
    e = np.exp(logits - logits.max())
    probs = e / e.sum()
    idx = probs.argsort()[::-1][:topk]
    return [{"rank": n + 1, "en": pairs[i][0], "cn": pairs[i][1],
             "conf": round(float(probs[i]) * 100, 2)} for n, i in enumerate(idx)]


def region_pick(top5, china):
    """地域校正：top1 非中国分布时，取 top5 里最靠前的中国分布种。

    返回 (verdict, fixed)；china 为 None 时原样返回 top1。
    """
    top1 = top5[0]
    if not china or top1["cn"] in china:
        return top1, False
    for t in top5:
        if t["cn"] in china:
            return t, True
    return top1, False        # top5 全是非中国种：保留 top1（可能是迷鸟）


def is_absent_group(cn_name):
    """top1 是否命中异域类群黑名单（命中 = 分类器在乱猜，大概率非鸟）。"""
    return any(k in cn_name for k in ABSENT_GROUP_KWS)


def is_junk(top1, china):
    """异域类群拦截：类群命中黑名单 且 物种本身不在《中国名录》。

    名录豁免是关键：大红鹳、白冠带鹀等虽属异域类群，但名录收录了它们
    （真实记录种），模型认识这些种，top1 命中时不应拦截。
    """
    if not is_absent_group(top1["cn"]):
        return False
    return china is None or top1["cn"] not in china


def crop_at(img, box, pad=0.15):
    """按检测框裁鸟图，四周各扩 pad 比例的余量。"""
    x1, y1, x2, y2 = box[:4]
    h, w = img.shape[:2]
    pw, ph = int((x2 - x1) * pad), int((y2 - y1) * pad)
    return img[max(0, y1 - ph):min(h, y2 + ph), max(0, x1 - pw):min(w, x2 + pw)]


def judge(cls_sess, pairs, china, img, box):
    """对一个检测框：裁切 -> 分类 -> top5 -> 地域校正出最终物种结论。"""
    top = classify(cls_sess, pairs, crop_at(img, box), topk=5)
    top1 = top[0]
    pick, fixed = region_pick(top, china)
    use_pick = fixed and pick["conf"] >= REGION_MIN_PICK
    species = pick if use_pick else top1
    return {"bbox": [int(box[0]), int(box[1]), int(box[2]), int(box[3])],
            "det_conf": round(float(box[4]), 3),
            "top5": top,
            "species": species["cn"], "en": species["en"], "conf": species["conf"],
            "region_fixed": use_pick,
            "foreign": bool(china) and top1["cn"] not in china and not use_pick,
            "junk": is_junk(top1, china)}


def tile_detect(det_sess, img, iou_thr=0.5):
    """2x2 带重叠的分块检测（小目标兜底），坐标映射回原图并按 IoU 去重。"""
    h, w = img.shape[:2]
    ov = 0.15
    th, tw = int(h / 2 * (1 + ov)), int(w / 2 * (1 + ov))
    cands = []
    for ty in (0, h - th):
        for tx in (0, w - tw):
            sub = img[ty:ty + th, tx:tx + tw]
            for c in detect(det_sess, sub, conf_thr=TILE_CONF_CAND,
                            iou_thr=iou_thr):
                cands.append((c[0] + tx, c[1] + ty, c[2] + tx, c[3] + ty, c[4]))
    cands.sort(key=lambda x: -x[4])
    keep = []
    for c in cands:
        if all(iou(c, k) < iou_thr for k in keep):
            keep.append(c)
    return keep


def is_strong(j, tile=False):
    """确认标准：检测置信达标 且 原始 top1 分类分达标（鸟性判断不掺校正）。

    top1 落在异域类群黑名单（junk）的一票否决——分类器在乱猜非中国类群，
    大概率根本不是鸟（荷花/蜻蜓实测案例）。
    """
    if j.get("junk"):
        return False
    det_ok = TILE_DET_OK if tile else DET_CONF_OK
    return j["det_conf"] >= det_ok and j["top5"][0]["conf"] >= CLS_CONF_OK


def is_suspect(j):
    """疑似标准：用于飞行姿态等分类器低分场景，标注出来供人工复核。"""
    if j.get("junk"):
        return False
    return j["det_conf"] >= SUSPECT_DET and j["conf"] >= SUSPECT_CLS


def identify_photo(det_sess, cls_sess, pairs, china, path):
    """单张照片：整图检测 -> 无确认鸟时分块检测兜底。

    返回 {"file","ok","birds":[确认],"suspects":[疑似],"ms"}
    """
    t_start = time.perf_counter()
    img = imread_unicode(path)
    if img is None:
        return {"file": Path(path).name, "ok": False, "birds": [],
                "suspects": [], "ms": 0.0}
    n_dets = 0
    n_junk = 0
    strong, suspects = [], []
    dets = detect(det_sess, img)
    n_dets += len(dets)
    for box in dets[:MAX_BIRDS]:
        j = judge(cls_sess, pairs, china, img, box)
        if j.get("junk"):
            n_junk += 1
            continue
        if is_strong(j):
            strong.append(j)
    if not strong:                       # 分块兜底
        tiles = tile_detect(det_sess, img)
        n_dets += len(tiles)
        for box in tiles[:MAX_BIRDS + 1]:
            j = judge(cls_sess, pairs, china, img, box)
            if j.get("junk"):
                n_junk += 1
                continue
            if is_strong(j, tile=True):
                strong.append(j)
            elif is_suspect(j):
                suspects.append(j)
    strong.sort(key=lambda j: -j["conf"])
    suspects.sort(key=lambda j: -j["conf"])
    return {"file": Path(path).name, "ok": True, "birds": strong,
            "suspects": suspects, "n_dets": n_dets, "n_junk": n_junk,
            "img_w": img.shape[1], "img_h": img.shape[0],
            "ms": round((time.perf_counter() - t_start) * 1000)}


# ---------------------------------------------------------------- 扫描
def run_scan(dir_str, model=None, out_console=True, write_sidecar=True):
    """扫描目录：控制台逐张输出 + 写边车 JSON + 汇总 JSON。返回汇总 dict。"""
    det_sess, cls_sess, pairs, model_info, china = model
    root = Path(dir_str).expanduser().resolve()
    files = sorted(p for p in root.iterdir()
                   if p.is_file() and p.suffix.lower() in EXTS)
    log = print if out_console else (lambda *a, **k: None)

    log("=" * 72)
    log("扫描目录: %s" % root)
    log("照片共 %d 张（%s）" % (len(files), ", ".join(sorted({p.suffix for p in files}) or "无")))
    log("模型: %s | 鸟种 %d | 门槛: det>=%.2f 且 cls>=%.0f%% | 校正后 cls"
        % (model_info, len(pairs), DET_CONF_OK, CLS_CONF_OK))
    t_all = time.perf_counter()

    n_done, n_ok, n_fail, n_bird, n_susp, n_junk_total = 0, 0, 0, 0, 0, 0
    hits, susp_hits = [], []

    for i, p in enumerate(files, 1):
        r = identify_photo(det_sess, cls_sess, pairs, china, p)
        n_done += 1
        n_junk_total += r.get("n_junk", 0)
        if not r["ok"]:
            n_fail += 1
            note = ""
            if p.suffix.lower() in (".hif", ".heic", ".heif") and not _HEIF_READY:
                note = "（HEIF 需安装 pillow_heif：pip install pillow-heif）"
            log("[%3d/%d] %-28s ✗ 读不了图%s" % (i, len(files), r["file"], note))
            continue
        n_ok += 1
        if r["birds"]:
            n_bird += 1
            b0 = r["birds"][0]
            head = "%s %.1f%%" % (b0["species"], b0["conf"])
            if b0["region_fixed"]:
                head += "［校正自 %s］" % b0["top5"][0]["cn"]
            log("[%3d/%d] %-28s ✓ %s（%d 只，%d ms）"
                % (i, len(files), r["file"], head, len(r["birds"]), r["ms"]))
            for k, b in enumerate(r["birds"], 1):
                note = ""
                if b["region_fixed"]:
                    note = "［校正自 %s %.1f%%］" % (b["top5"][0]["cn"],
                                                    b["top5"][0]["conf"])
                elif b["foreign"]:
                    note = "（非中国分布，可能迷鸟或标注差异）"
                log("         bird%d: %s %.1f%% / %s  bbox=%s det=%.2f%s"
                    % (k, b["species"], b["conf"], b["en"], b["bbox"],
                       b["det_conf"], note))
            sidecar_name = None
            if write_sidecar:
                # 边车 JSON（供 photo_track_map_v3 等工具读取）
                sidecar = p.with_suffix(".bird.json")
                sidecar.write_text(json.dumps({
                    "file": r["file"], "path": str(p),
                    "img_w": r["img_w"], "img_h": r["img_h"],
                    "scan_time": datetime.now().isoformat(timespec="seconds"),
                    "birds": r["birds"],
                }, ensure_ascii=False, indent=2), encoding="utf-8")
                sidecar_name = sidecar.name
            hits.append({"file": r["file"], "path": str(p),
                         "sidecar": sidecar_name,
                         "birds": r["birds"], "ms": r["ms"],
                         "img_w": r["img_w"], "img_h": r["img_h"]})
        elif r["suspects"]:
            n_susp += 1
            s0 = r["suspects"][0]
            log("[%3d/%d] %-28s ? 疑似 %s %.1f%%（det=%.2f，%d ms，建议人工复核）"
                % (i, len(files), r["file"], s0["species"], s0["conf"],
                   s0["det_conf"], r["ms"]))
            susp_hits.append({"file": r["file"], "path": str(p),
                              "suspects": r["suspects"]})
        else:
            extra = "，拦截疑似非鸟 %d 处" % r["n_junk"] if r.get("n_junk") else ""
            log("[%3d/%d] %-28s   未检出鸟（%d ms%s）"
                % (i, len(files), r["file"], r["ms"], extra))

    elapsed = time.perf_counter() - t_all
    report = {
        "scan_time": datetime.now().isoformat(timespec="seconds"),
        "directory": str(root),
        "model": model_info,
        "thresholds": {"det_conf": DET_CONF_OK, "cls_conf_pct": CLS_CONF_OK,
                       "suspect_det": SUSPECT_DET, "suspect_cls_pct": SUSPECT_CLS,
                       "china_filter": bool(china)},
        "stats": {"total": len(files), "processed_ok": n_ok,
                  "failed": n_fail, "with_birds": n_bird,
                  "suspect": n_susp, "junk_blocked": n_junk_total,
                  "elapsed_sec": round(elapsed, 1)},
        "birds_photos": hits,
        "suspect_photos": susp_hits,
    }
    report_path = root / "birds_report.json"
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2),
                           encoding="utf-8")

    log("-" * 72)
    log("统计：处理 %d 张（成功 %d，失败 %d），识别出鸟 %d 张，疑似 %d 张，耗时 %.1f 秒"
        % (len(files), n_ok, n_fail, n_bird, n_susp, elapsed))
    if n_junk_total:
        log("异域类群拦截：%d 处（top1 为中国无分布类群，判非鸟丢弃）" % n_junk_total)
    log("汇总已写入: %s" % report_path)
    if n_bird:
        if write_sidecar:
            log("边车 JSON: %d 份（<照片名>.bird.json）" % n_bird)
        else:
            log("边车 JSON: 已关闭（仅生成汇总）")
    log("=" * 72)
    return report


def load_china_set(model_dir):
    """中国分布鸟种集合（中文名）。文件缺失时返回 None = 不做地域校正。"""
    p = model_dir / "china_birds_v10.txt"
    if not p.exists():
        return None
    return {line.strip() for line in p.read_text(encoding="utf-8").splitlines()
            if line.strip()}


def load_model():
    model_dir = find_model_dir()
    print("加载模型 ...（%s）" % model_dir)
    t0 = time.perf_counter()
    det = make_session(model_dir / "yolo_bird_detect.onnx")
    cls = make_session(model_dir / "s1v2_bird_cls.onnx")
    pairs = load_pairs(model_dir)
    china = load_china_set(model_dir)
    info = "YOLOv8+s1v2 ONNX(CPU) 加载 %.1fs" % (time.perf_counter() - t0)
    print("  %s | 鸟种 %d | 中国分布校正: %s"
          % (info, len(pairs), "%d 种" % len(china) if china else "关闭（缺名录文件）"))
    return det, cls, pairs, info, china


# ---------------------------------------------------------------- GUI
def gui_main():
    import tkinter as tk
    from tkinter import ttk, filedialog

    root = tk.Tk()
    root.title("鸟类照片批量识别（本地模型）")
    root.resizable(False, False)

    style = ttk.Style(root)
    style.theme_use("clam")
    style.configure("TButton", padding=6)
    style.configure("TLabel", padding=2)

    state = {"model": None, "dir": "", "running": False}

    frm = ttk.Frame(root, padding=16)
    frm.grid(sticky="nsew")

    ttk.Label(frm, text="照片目录：").grid(row=0, column=0, sticky="e")
    var_dir = tk.StringVar()
    ent_dir = ttk.Entry(frm, textvariable=var_dir, width=52, state="readonly")
    ent_dir.grid(row=0, column=1, columnspan=2, padx=6, pady=4, sticky="w")

    var_sidecar = tk.BooleanVar(value=True)
    ttk.Checkbutton(frm, text="同时生成每张照片的边车 JSON（<照片名>.bird.json）",
                    variable=var_sidecar).grid(row=1, column=0, columnspan=3,
                                               sticky="w", pady=(2, 0))

    var_status = tk.StringVar(value="空闲（首次提交需先加载模型，约几秒）")
    ttk.Label(frm, textvariable=var_status).grid(row=2, column=0, columnspan=3,
                                                 sticky="w", pady=(0, 8))

    def choose_dir():
        d = filedialog.askdirectory(title="选择照片目录")
        if d:
            state["dir"] = d
            var_dir.set(d)

    def worker():
        try:
            model = state["model"]
            if model is None:
                model = load_model()
                state["model"] = model
            report = run_scan(state["dir"], model=model,
                              write_sidecar=var_sidecar.get())
            n = report["stats"]
            var_status.set("完成：处理 %d 张，识别出鸟 %d 张，耗时 %.1f 秒"
                           % (n["total"], n["with_birds"], n["elapsed_sec"]))
        except Exception as exc:  # 模型缺失、目录不可读等，界面直接给出原因
            var_status.set("出错：%s" % exc)
        finally:
            state["running"] = False
            btn_ok.config(state="normal")

    def submit():
        if not state["dir"]:
            var_status.set("请先选择照片目录")
            return
        if state["running"]:
            return
        state["running"] = True
        btn_ok.config(state="disabled")
        var_status.set("扫描中…… 结果见控制台窗口")
        threading.Thread(target=worker, daemon=True).start()

    def poll_progress():
        root.after(300, poll_progress)

    # 三个按钮同一行
    btn_sel = ttk.Button(frm, text="选择照片目录", command=choose_dir)
    btn_sel.grid(row=3, column=0, sticky="e", padx=4, pady=(4, 0))
    btn_ok = ttk.Button(frm, text="提交", command=submit)
    btn_ok.grid(row=3, column=1, sticky="w", padx=4, pady=(4, 0))
    ttk.Button(frm, text="退出", command=root.destroy).grid(
        row=3, column=2, sticky="w", padx=4, pady=(4, 0))

    root.after(300, poll_progress)
    root.mainloop()


# ---------------------------------------------------------------- 入口
def main():
    if len(sys.argv) >= 3 and sys.argv[1] == "--cli":
        model = load_model()
        run_scan(sys.argv[2], model=model)
        return
    gui_main()


if __name__ == "__main__":
    main()
