#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
GPX 轨迹方向反转工具 (v2)
============================================================
把 GPX 文件中的轨迹整体反向（从终点走向起点），并保证输出文件符合
GPX 1.1 对 <time> 的硬性要求：**一律为 UTC，并以 Z 结尾**。

相对原版的修复清单
------------------------------------------------------------
[P1-1] 时间不再"抹掉偏移量直接补 Z"，而是真正换算到 UTC 后再写 Z。
       2024-03-15T08:30:00+08:00  ->  2024-03-15T00:30:00Z   (原版写成 08:30:00Z，谎报 8 小时)
       2024-03-15T08:30:00-05:00  ->  2024-03-15T13:30:00Z   (原版连负号都没识别)
[P1-2] 混合时区（部分带 Z、部分不带）不再抛
       TypeError: can't subtract offset-naive and offset-aware datetimes
[P1-3] 部分轨迹点缺 <time> 时，不再"点倒序但时间原样保留"（既非 UTC 又倒序），
       改为：时间照常归一化为 UTC+Z，跳过时间轴镜像，并在日志里明确告警。
[P1-4] 支持前缀命名空间写法 <gpx:gpx xmlns:gpx="...">（原版按空默认命名空间查找，
       会误报"未找到轨迹段 trkseg"）。
[P2-5] 命名空间扫描改为遍历整个文件（原版只读前 4096 字节，靠后的扩展命名空间
       仍会退化输出成 ns0:）。
[P2-6] 多段轨迹同时倒置段序，得到完整反转（原版只做段内倒序，结果是 2,1,4,3）。
[P2-7] 输出重名自动加序号 _R.gpx -> _R2.gpx，不再静默覆盖已有文件。
[P2-8] 改为"临时文件 + 原子替换"一次性写出；格式化失败不再被 bare except 吞掉。
[P2-9] 其它：保留 XML 注释、保留原始整数秒/毫秒精度、GPX 1.0 无命名空间文件可用、
       写出后回读校验点数、全局异常兜底。

作者说明：本文件为单文件 Tkinter 程序，无第三方依赖（Python 3.8+）。
"""

import os
import re
import tempfile
import threading
import xml.dom.minidom
import xml.etree.ElementTree as ET
from datetime import datetime, timezone

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from tkinter import scrolledtext
from tkinter import font as tkfont

try:
    from zoneinfo import ZoneInfo
except ImportError:  # Python < 3.9
    ZoneInfo = None


APP_TITLE = "GPX 轨迹方向反转工具 v2"

# 「无时区时间」的两种解释口径
NAIVE_AS_LOCAL = "按系统本地时区换算"
NAIVE_AS_UTC = "视为 UTC，仅补 Z"


# ============================================================
#  时间处理（核心修复区）
# ============================================================

# 匹配结尾的时区偏移：+08:00 / +0800 / -05:00 / -0500
_OFFSET_TAIL_RE = re.compile(r'([+-])(\d{2}):?(\d{2})$')


def local_tzinfo():
    """尽量取得"带夏令时规则"的本地时区；失败则退回当前固定偏移。"""
    if ZoneInfo is not None:
        tz_name = os.environ.get('TZ', '').strip()
        if tz_name:
            try:
                return ZoneInfo(tz_name)
            except Exception:
                pass
        # macOS / Linux：/etc/localtime 通常是指向 zoneinfo 的软链接
        try:
            real = os.path.realpath('/etc/localtime')
            marker = 'zoneinfo/'
            idx = real.rfind(marker)
            if idx != -1:
                return ZoneInfo(real[idx + len(marker):])
        except Exception:
            pass
    # 兜底：系统当前偏移（对中国大陆这类无夏令时地区完全等价）
    return datetime.now().astimezone().tzinfo or timezone.utc


def local_tz_display():
    """给界面显示用的本地时区描述。"""
    tz = local_tzinfo()
    off = datetime.now(tz).utcoffset()
    if off is None:
        return "本地时区"
    total = int(off.total_seconds())
    sign = '+' if total >= 0 else '-'
    total = abs(total)
    name = getattr(tz, 'key', None) or str(tz)
    return "%s (UTC%s%02d:%02d)" % (name, sign, total // 3600, (total % 3600) // 60)


def parse_time_text(text, naive_tz=None):
    """
    把 GPX 的 <time> 文本解析成 UTC 的 aware datetime。

    参数
      text     : 原始文本，如 '2024-03-15T08:30:00+08:00'
      naive_tz : 当文本**不含时区**时使用的时区；None 表示按 UTC 处理（不偏移）

    返回
      (datetime_utc | None, had_fraction: bool)
      datetime_utc 为 None 表示无法解析（调用方决定是告警还是原样保留）
    """
    if text is None:
        return None, False

    s = text.strip()
    if not s:
        return None, False

    had_fraction = '.' in s
    work = s

    # 1) 结尾 Z / z -> +00:00
    if work[-1] in ('Z', 'z'):
        work = work[:-1] + '+00:00'

    # 2) +0800 / -0500（缺冒号）-> +08:00 / -05:00
    m = _OFFSET_TAIL_RE.search(work)
    if m:
        work = work[:m.start()] + m.group(1) + m.group(2) + ':' + m.group(3)

    # 3) 兼容用空格代替 T 的写法
    if 'T' not in work and 't' not in work and ' ' in work:
        work = work.replace(' ', 'T', 1)

    try:
        dt = datetime.fromisoformat(work)
    except ValueError:
        # 兜底：兼容 Python < 3.11 不接受紧凑写法 / 极少数非标准分隔
        dt = None
        for fmt in ('%Y-%m-%dT%H:%M:%S.%f%z', '%Y-%m-%dT%H:%M:%S%z',
                    '%Y-%m-%dT%H:%M%z', '%Y%m%dT%H%M%S%z', '%Y%m%dT%H%M%S.%f%z',
                    '%Y-%m-%dT%H:%M:%S.%f', '%Y-%m-%dT%H:%M:%S'):
            try:
                dt = datetime.strptime(work, fmt)
                break
            except ValueError:
                continue
        if dt is None:
            return None, had_fraction

    if dt.tzinfo is None:
        # ★ 关键修复：原版这里把无时区时间直接当 UTC 用，导致本地墙钟被谎报为 UTC
        dt = dt.replace(tzinfo=naive_tz if naive_tz is not None else timezone.utc)

    # ★ 关键修复：真正换算到 UTC（原版只做了字符串替换）
    return dt.astimezone(timezone.utc), had_fraction


def format_utc(dt, with_fraction):
    """把 UTC datetime 渲染成 GPX 规范要求的 ...Z 形式。"""
    base = dt.strftime('%Y-%m-%dT%H:%M:%S')
    if with_fraction:
        base += '.%03d' % (dt.microsecond // 1000)
    return base + 'Z'


# ============================================================
#  XML / 命名空间处理
# ============================================================

def local_name(tag):
    """取标签的本地名（去掉 {namespace} 前缀）。注释节点的 tag 是函数，返回 ''。"""
    if not isinstance(tag, str):
        return ''
    if tag.startswith('{'):
        return tag.split('}', 1)[1]
    return tag


def namespace_of(tag):
    """取标签所属命名空间 URI，无命名空间返回 ''。"""
    if isinstance(tag, str) and tag.startswith('{'):
        return tag.split('}', 1)[0][1:]
    return ''


def collect_namespaces(file_path, log=None):
    """
    扫描**整个文件**收集 xmlns 声明并注册到 ElementTree。

    ★ 修复 P2-5：原版只 read(4096)，4KB 之后出现的扩展命名空间没被注册，
      输出时会退化成 ns0: 前缀。
    """
    ns_map = {}
    conflicts = []

    for event, payload in ET.iterparse(file_path, events=('start-ns', 'end')):
        if event == 'start-ns':
            prefix, uri = payload
            prefix = prefix or ''
            if not uri:
                continue
            if prefix in ns_map and ns_map[prefix] != uri:
                conflicts.append((prefix, ns_map[prefix], uri))
                continue
            ns_map.setdefault(prefix, uri)
        else:
            payload.clear()

    for prefix, uri in ns_map.items():
        try:
            ET.register_namespace(prefix, uri)
        except Exception:
            pass

    if log:
        for prefix, old, new in conflicts:
            log("提示：前缀 %s 被重复绑定（%s / %s），已按先出现的声明输出。"
                % (prefix or '(默认)', old, new))
        log("已注册命名空间 %d 个。" % len(ns_map))

    return ns_map


def child_by_local(parent, name, ns):
    """在直接子元素里按本地名查找（限定命名空间，ns 为 '' 表示无命名空间）。"""
    for child in parent:
        if local_name(child.tag) == name and namespace_of(child.tag) == ns:
            return child
    return None


def iter_by_local(parent, name, ns):
    """深度遍历，按本地名 + 命名空间筛选元素（忽略注释节点）。"""
    for elem in parent.iter():
        if local_name(elem.tag) == name and namespace_of(elem.tag) == ns:
            yield elem


# ============================================================
#  核心：GPX 反转
# ============================================================

class ReverseResult(object):
    def __init__(self):
        self.output_path = ''
        self.tracks = 0
        self.segments = 0
        self.points = 0
        self.mirrored_tracks = 0
        self.time_range_before = None
        self.time_range_after = None
        self.warnings = []
        self.logs = []


def reverse_gpx(file_path, naive_mode=NAIVE_AS_LOCAL, mirror_time=True,
                reverse_segments=True, log=None):
    """
    反转 GPX 轨迹方向。

    naive_mode       : NAIVE_AS_LOCAL / NAIVE_AS_UTC —— 无时区时间的解释口径
    mirror_time      : True  时间轴镜像重排（保持总时长不变且时间仍递增）
                       False 时间跟着点位走（时间序列会变成递减）
    reverse_segments : True  多段轨迹同时倒置段序（完整反转）
    log              : 可调用对象，用于输出过程日志

    返回 ReverseResult
    """
    out = ReverseResult()

    def emit(msg):
        out.logs.append(msg)
        if log:
            log(msg)

    if not os.path.isfile(file_path):
        raise ValueError("文件不存在：%s" % file_path)

    naive_tz = local_tzinfo() if naive_mode == NAIVE_AS_LOCAL else None

    # ---- 1. 命名空间：全文件扫描并注册（修复 P2-5） ----
    try:
        collect_namespaces(file_path, log=emit)
    except ET.ParseError as e:
        raise ValueError("GPX 文件 XML 格式错误：%s" % e)
    except OSError as e:
        raise ValueError("无法读取文件：%s" % e)

    # ---- 2. 解析（保留注释） ----
    parser = ET.XMLParser(target=ET.TreeBuilder(insert_comments=True))
    try:
        tree = ET.parse(file_path, parser=parser)
    except ET.ParseError as e:
        raise ValueError("GPX 文件 XML 格式错误：%s" % e)
    root = tree.getroot()

    if local_name(root.tag) != 'gpx':
        raise ValueError("根元素不是 <gpx>（实际为 <%s>），请确认这是 GPX 文件。"
                         % (local_name(root.tag) or '未知'))

    gpx_ns = namespace_of(root.tag)
    emit("根元素命名空间：%s" % (gpx_ns or '(无命名空间，兼容 GPX 1.0)'))

    # ---- 3. 归一化所有 GPX 命名空间下的 <time> 为 UTC+Z（修复 P1-1 / P1-3） ----
    time_elems = list(iter_by_local(root, 'time', gpx_ns))
    frac_digits = 0
    bad_times = []
    for te in time_elems:
        dt, had_frac = parse_time_text(te.text, naive_tz)
        if dt is None:
            bad_times.append((te.text or '').strip())
            continue
        if had_frac:
            frac_digits = 1
        te.text = format_utc(dt, had_frac)

    if bad_times:
        out.warnings.append(
            "有 %d 个 <time> 无法解析，已原样保留（前几个：%s）"
            % (len(bad_times), '、'.join(repr(t) for t in bad_times[:3])))
    if time_elems:
        emit("已把 %d 个 <time> 归一化为 UTC+Z（无时区口径：%s）。"
             % (len(time_elems), naive_mode))
    else:
        emit("文件中没有 <time> 元素，只反转点位顺序。")

    # ---- 4. 遍历每条 trk，反转轨迹 ----
    tracks = list(iter_by_local(root, 'trk', gpx_ns))

    for trk_idx, trk in enumerate(tracks, 1):
        segs = [c for c in trk
                if local_name(c.tag) == 'trkseg' and namespace_of(c.tag) == gpx_ns]
        if not segs:
            continue

        seg_pts = []
        for seg in segs:
            pts = [c for c in seg
                   if local_name(c.tag) == 'trkpt' and namespace_of(c.tag) == gpx_ns]
            seg_pts.append(pts)

        flat = [(seg, pt) for seg, pts in zip(segs, seg_pts) for pt in pts]
        if len(flat) < 2:
            emit("轨迹 #%d 点数不足 2，跳过。" % trk_idx)
            continue

        out.tracks += 1
        out.segments += len([s for s in seg_pts if s])
        out.points += len(flat)

        # ---- 4.1 时间轴处理 ----
        def time_of(pt):
            te = child_by_local(pt, 'time', gpx_ns)
            if te is None or not (te.text or '').strip():
                return None
            dt, _ = parse_time_text(te.text, naive_tz)
            return dt

        def set_time(pt, dt):
            te = child_by_local(pt, 'time', gpx_ns)
            if te is None:
                return
            te.text = format_utc(dt, bool(frac_digits))

        # 段序倒置时按"整条轨迹"做全局镜像；否则按"每个段"独立镜像
        groups = [flat] if reverse_segments else \
            [[(seg, pt) for pt in pts] for seg, pts in zip(segs, seg_pts) if pts]

        mirrored = 0
        for group in groups:
            group_times = [time_of(pt) for _seg, pt in group]
            if len(group) < 2:
                continue
            if any(t is None for t in group_times):
                # ★ 修复 P1-3：缺时间时不做镜像（时间已在第 3 步归一化为 UTC+Z）
                out.warnings.append(
                    "轨迹 #%d 有 %d 个点缺少可用的 <time>，该段未做时间轴镜像，"
                    "时间将随点位倒序（不再是单调递增）。"
                    % (trk_idx, sum(1 for t in group_times if t is None)))
                continue
            if not mirror_time:
                out.warnings.append(
                    "轨迹 #%d 已按你的设置关闭时间轴镜像，时间跟随点位倒序。"
                    % trk_idx)
                continue
            # 镜像：new = t_start + (t_end - t_old)，总时长不变且仍递增
            t_start = group_times[0]
            span = group_times[-1] - t_start
            for (seg, pt), t_old in zip(group, group_times):
                set_time(pt, t_start + (span - (t_old - t_start)))
            mirrored += 1

        out.mirrored_tracks += mirrored

        # 记录时间范围（取归一化后的全轨迹首末）
        all_times = [t for t in (time_of(pt) for _s, pt in flat) if t is not None]
        if all_times:
            out.time_range_before = (min(all_times), max(all_times))

        # ---- 4.2 段内点位倒序 ----
        for seg, pts in zip(segs, seg_pts):
            if len(pts) < 2:
                continue
            for pt in pts:
                seg.remove(pt)
            for pt in reversed(pts):
                seg.append(pt)

        # ---- 4.3 段序倒置（★ 修复 P2-6：原版漏了这一步，结果是 2,1,4,3） ----
        if reverse_segments and len(segs) > 1:
            for seg in segs:
                trk.remove(seg)
            for seg in reversed(segs):
                trk.append(seg)

        emit("轨迹 #%d：%d 段 / %d 点已反转%s%s"
             % (trk_idx, len(segs), len(flat),
                ("，段序已倒置" if (reverse_segments and len(segs) > 1) else ""),
                ("，时间轴已镜像" if mirrored else "")))

    if out.tracks == 0:
        raise ValueError("GPX 文件中没有找到可反转的轨迹点（trkseg/trkpt 至少需要 2 个点）。")

    # ---- 5. 输出：重名自动加序号（★ 修复 P2-7） ----
    dir_name = os.path.dirname(os.path.abspath(file_path))
    base_name = os.path.splitext(os.path.basename(file_path))[0]
    output_path = os.path.join(dir_name, "%s_R.gpx" % base_name)
    seq = 2
    while os.path.exists(output_path):
        output_path = os.path.join(dir_name, "%s_R%d.gpx" % (base_name, seq))
        seq += 1
    if seq > 2:
        emit("目标文件名已存在，本次输出为 %s" % os.path.basename(output_path))

    # ---- 6. 序列化 + 原子写出（★ 修复 P2-8） ----
    try:
        raw = ET.tostring(root, encoding='utf-8')
    except Exception as e:
        raise ValueError("序列化 XML 失败：%s" % e)

    text = None
    try:
        dom = xml.dom.minidom.parseString(raw)
        pretty = dom.toprettyxml(indent='  ', encoding='utf-8').decode('utf-8')
        lines = [ln for ln in pretty.split('\n') if ln.strip()]
        if lines and lines[0].lstrip().startswith('<?xml'):
            lines = lines[1:]
        text = '<?xml version="1.0" encoding="UTF-8"?>\n' + '\n'.join(lines) + '\n'
    except Exception as e:
        # ★ 修复 P2-8：不再静默吞掉异常，改为告警 + 退回未格式化输出
        out.warnings.append("XML 美化失败（%s），已输出未缩进版本。" % e)
        text = raw.decode('utf-8')

    if 'ns0:' in text and 'ns0:' not in base_name:
        # 极少数情况下 ET 仍会生成 ns0 —— 至少让用户看得见
        out.warnings.append("输出中出现了 ns0: 前缀，源文件可能使用了未声明的命名空间。")

    tmp_path = None
    try:
        fd, tmp_path = tempfile.mkstemp(dir=dir_name, prefix='.gpxrev_', suffix='.tmp')
        with os.fdopen(fd, 'w', encoding='utf-8', newline='\n') as f:
            f.write(text)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp_path, output_path)   # 原子替换，不会留下半个文件
        tmp_path = None
        # mkstemp 建的是 0600，跟源文件对齐权限，避免输出文件"打不开"
        try:
            os.chmod(output_path, os.stat(file_path).st_mode & 0o777)
        except OSError:
            pass
    except Exception as e:
        raise ValueError("写入输出文件失败：%s" % e)
    finally:
        if tmp_path and os.path.exists(tmp_path):
            try:
                os.remove(tmp_path)
            except OSError:
                pass

    # ---- 7. 回读校验 ----
    try:
        check_root = ET.parse(output_path).getroot()
        check_ns = namespace_of(check_root.tag)
        n_out = sum(1 for _ in iter_by_local(check_root, 'trkpt', check_ns))
        if n_out != out.points:
            raise ValueError("回读校验失败：写出 %d 个点，应有 %d 个。" % (n_out, out.points))
        emit("回读校验通过：%d 个 trkpt。" % n_out)
    except ET.ParseError as e:
        raise ValueError("输出文件无法重新解析，已中止：%s" % e)

    out.output_path = output_path

    # 记录反转后的时间范围
    try:
        root2 = ET.parse(output_path).getroot()
        ns2 = namespace_of(root2.tag)
        ts2 = []
        for te in iter_by_local(root2, 'time', ns2):
            dt, _ = parse_time_text(te.text, naive_tz)
            if dt:
                ts2.append(dt)
        if ts2:
            out.time_range_after = (min(ts2), max(ts2))
    except Exception:
        pass

    return out


# ============================================================
#  GUI
# ============================================================

def pick_font():
    """跨平台挑选一个可用的中文字体（原版硬编码 Microsoft YaHei，Mac/Linux 会退化）。"""
    preferred = ["PingFang SC", "Microsoft YaHei UI", "Microsoft YaHei",
                 "Hiragino Sans GB", "Noto Sans CJK SC", "Source Han Sans SC",
                 "WenQuanYi Micro Hei", "Helvetica Neue", "Arial"]
    try:
        available = set(tkfont.families())
    except Exception:
        return "TkDefaultFont"
    for name in preferred:
        if name in available:
            return name
    return "TkDefaultFont"


class GPXReverserApp(object):
    def __init__(self, root):
        self.root = root
        self.root.title(APP_TITLE)
        self.root.geometry("760x600")
        self.root.minsize(680, 520)

        self.font_family = pick_font()
        self.style = ttk.Style()
        try:
            self.style.theme_use("clam")
        except Exception:
            pass
        self.style.configure("Title.TLabel", font=(self.font_family, 15, "bold"))
        self.style.configure("Info.TLabel", font=(self.font_family, 10))
        self.style.configure("Hint.TLabel", font=(self.font_family, 9), foreground="#777")
        self.style.configure("Status.TLabel", font=(self.font_family, 11), foreground="#555")
        self.style.configure("Action.TButton", font=(self.font_family, 12), padding=8)
        self.style.configure("TCheckbutton", font=(self.font_family, 10))
        self.style.configure("TCombobox", font=(self.font_family, 10))

        self.selected_file = tk.StringVar(value="")
        self.path_display = tk.StringVar(value="未选择文件")
        self.status_var = tk.StringVar(value="就绪：请选择一个 GPX 文件")
        self.naive_mode = tk.StringVar(value=NAIVE_AS_LOCAL)
        self.mirror_time = tk.BooleanVar(value=True)
        self.reverse_segments = tk.BooleanVar(value=True)

        self._busy = False
        self._worker = None

        self._build_ui()

    # ---------- 界面 ----------
    def _build_ui(self):
        main = ttk.Frame(self.root, padding=18)
        main.pack(fill=tk.BOTH, expand=True)

        ttk.Label(main, text="GPX 轨迹方向反转工具",
                  style="Title.TLabel").pack(pady=(0, 12))

        # 文件选择
        file_frame = ttk.LabelFrame(main, text="文件选择", padding=10)
        file_frame.pack(fill=tk.X, pady=(0, 10))

        self.path_label = ttk.Label(file_frame, textvariable=self.path_display,
                                    style="Info.TLabel", wraplength=540,
                                    foreground="#333", justify=tk.LEFT)
        self.path_label.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 10))
        self.btn_browse = ttk.Button(file_frame, text="浏览...", style="Action.TButton",
                                     command=self._select_file)
        self.btn_browse.pack(side=tk.RIGHT)

        # 选项
        opt = ttk.LabelFrame(main, text="处理选项", padding=10)
        opt.pack(fill=tk.X, pady=(0, 10))

        row = ttk.Frame(opt)
        row.pack(fill=tk.X, pady=(0, 6))
        ttk.Label(row, text="无时区时间（如 2024-03-15T08:30:00）：",
                  style="Info.TLabel").pack(side=tk.LEFT)
        self.cmb_naive = ttk.Combobox(row, textvariable=self.naive_mode,
                                      values=[NAIVE_AS_LOCAL, NAIVE_AS_UTC],
                                      state="readonly", width=20,
                                      font=(self.font_family, 10))
        self.cmb_naive.pack(side=tk.LEFT, padx=(6, 0))
        ttk.Label(opt, text="GPX 规范要求 <time> 必须是 UTC+Z；本工具会把带偏移的时间真正换算到 UTC，"
                            "而不是简单把偏移删掉。",
                  style="Hint.TLabel").pack(anchor=tk.W)
        ttk.Label(opt, text="当前本地时区：%s" % local_tz_display(),
                  style="Hint.TLabel").pack(anchor=tk.W, pady=(0, 4))

        self.chk_mirror = ttk.Checkbutton(
            opt, variable=self.mirror_time,
            text="时间轴镜像重排（总时长不变，反转后时间仍严格递增）")
        self.chk_mirror.pack(anchor=tk.W)
        self.chk_seg = ttk.Checkbutton(
            opt, variable=self.reverse_segments,
            text="多段轨迹同时倒置段序（得到完整反转，而非每段各自倒序）")
        self.chk_seg.pack(anchor=tk.W)

        # 状态
        ttk.Label(main, textvariable=self.status_var,
                  style="Status.TLabel").pack(fill=tk.X, pady=(0, 8))

        # 日志
        log_frame = ttk.LabelFrame(main, text="运行日志", padding=6)
        log_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 10))
        self.log_text = scrolledtext.ScrolledText(
            log_frame, height=9, wrap=tk.WORD, font=(self.font_family, 10),
            background="#fbfbfb", foreground="#333", relief=tk.FLAT,
            state=tk.DISABLED)
        self.log_text.pack(fill=tk.BOTH, expand=True)

        # 按钮
        btn_bar = ttk.Frame(main)
        btn_bar.pack(pady=(4, 0))
        self.btn_submit = ttk.Button(btn_bar, text="提  交（反转轨迹）",
                                     style="Action.TButton", command=self._submit)
        self.btn_submit.pack(side=tk.LEFT, padx=12)
        self.btn_exit = ttk.Button(btn_bar, text="退出程序", style="Action.TButton",
                                   command=self._exit)
        self.btn_exit.pack(side=tk.LEFT, padx=12)

    def _log(self, msg):
        """线程安全地写日志。"""
        try:
            self.log_text.config(state=tk.NORMAL)
            self.log_text.insert(tk.END, msg + "\n")
            self.log_text.see(tk.END)
            self.log_text.config(state=tk.DISABLED)
        except tk.TclError:
            pass

    def _ui(self, func, *args):
        """把 UI 操作丢回主线程执行，避免 TclError。"""
        try:
            self.root.after(0, lambda: func(*args))
        except tk.TclError:
            pass

    def _set_busy(self, busy):
        self._busy = busy
        state = tk.DISABLED if busy else tk.NORMAL
        for w in (self.btn_submit, self.btn_browse):
            try:
                w.config(state=state)
            except tk.TclError:
                pass

    # ---------- 事件 ----------
    def _select_file(self):
        file_path = filedialog.askopenfilename(
            title="选择 GPX 文件",
            filetypes=[("GPX 文件", "*.gpx"), ("所有文件", "*.*")],
            initialdir=os.path.expanduser("~"))
        if file_path:
            self.selected_file.set(file_path)
            self.path_display.set(file_path)
            self.path_label.config(foreground="#1a73e8")
            self.status_var.set("已选择：%s" % os.path.basename(file_path))
            self._log("已选择文件：%s" % file_path)

    def _submit(self):
        if self._busy:
            return
        file_path = self.selected_file.get()
        if not file_path:
            messagebox.showwarning("提示", "请先选择一个 GPX 文件！")
            return
        if not os.path.isfile(file_path):
            messagebox.showerror("错误", "所选文件不存在！")
            return

        self._set_busy(True)
        self.status_var.set("正在处理，请稍候...")
        self._log("-" * 56)
        self._log("开始处理：%s" % os.path.basename(file_path))

        opts = (self.naive_mode.get(), self.mirror_time.get(),
                self.reverse_segments.get())
        self._worker = threading.Thread(
            target=self._run_worker, args=(file_path,) + opts, daemon=True)
        self._worker.start()

    def _run_worker(self, file_path, naive_mode, mirror_time, reverse_segments):
        try:
            res = reverse_gpx(file_path, naive_mode=naive_mode,
                              mirror_time=mirror_time,
                              reverse_segments=reverse_segments,
                              log=lambda m: self._ui(self._log, m))
        except ValueError as e:
            self._ui(self._on_fail, str(e), "失败：数据错误")
        except Exception as e:  # 全局兜底，绝不让线程静默死掉
            import traceback
            self._ui(self._log, traceback.format_exc())
            self._ui(self._on_fail, "处理出错：%s" % e, "处理失败")
        else:
            self._ui(self._on_success, file_path, res)

    def _on_fail(self, message, status):
        self._set_busy(False)
        self.status_var.set(status)
        self._log(status + "：" + message)
        messagebox.showerror("错误", message)

    def _on_success(self, src, res):
        self._set_busy(False)
        name = os.path.basename(res.output_path)
        self.status_var.set("完成 → %s" % name)

        for w in res.warnings:
            self._log("⚠ " + w)

        if res.time_range_before and res.time_range_after:
            b0, b1 = res.time_range_before
            a0, a1 = res.time_range_after
            self._log("时间范围（原始）：%s ~ %s" % (b0.isoformat(), b1.isoformat()))
            self._log("时间范围（输出）：%s ~ %s" % (a0.isoformat(), a1.isoformat()))

        warn_text = ""
        if res.warnings:
            warn_text = "\n\n注意：\n" + "\n".join("· " + w for w in res.warnings[:4])

        messagebox.showinfo(
            "成功",
            "轨迹反转完成！\n\n"
            "原始文件：%s\n"
            "输出文件：%s\n\n"
            "共反转 %d 条轨迹 / %d 个轨迹段 / %d 个轨迹点；\n"
            "所有 <time> 已按 GPX 规范统一为 UTC（Z 结尾）。%s"
            % (os.path.basename(src), name,
               res.tracks, res.segments, res.points, warn_text))

    def _exit(self):
        if self._busy:
            if not messagebox.askyesno("确认", "正在处理中，确定要强制退出吗？"):
                return
        if messagebox.askyesno("确认", "确定要退出程序吗？"):
            self.root.destroy()


def main():
    root = tk.Tk()
    GPXReverserApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
