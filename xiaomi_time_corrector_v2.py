#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
小米健康 GPS 轨迹时间修正工具 (v2.1)
============================================================
【用途】
小米健康 App 导出的 GPX / TCX 文件，时间标志写错了：
它把「中国区（UTC+8）的本地时间」直接配上了 UTC 的 "Z" 后缀。
本工具把这些时间标志改写成真正的 UTC + Z，**其余数据一律不动**。

    2024-03-15T08:30:00Z   （实为北京时间 08:30）
 -> 2024-03-15T00:30:00Z   （真正的 UTC）

另外：小米导出的 GPX / TCX 整个文档是「首尾相连」的（没有任何换行与缩进，
一个文件常常只有一行），不便阅读与人工比对。因此输出默认会做**缩进格式化**，
把文档按层级重新排版；该行为可在界面上关闭（关闭后输出与源文件排版完全一致）。

【依赖】
    pip install lxml -i https://pypi.tuna.tsinghua.edu.cn/simple

【相对原版的修复】
[P0-1] 防重复处理：输入文件名以 _Z / _UTC 结尾时，弹窗告警并要求二次确认
       （原版会把已修正文件再减 8 小时，累计 -16h，且输出 _Z_Z.gpx）。
[P0-2] 修改 0 处时不再谎报成功：不生成输出文件，明确提示"未发现需要修正的时间标志"
       （原版 fixed 0 处仍弹"修正完成"并生成同内容新文件）。
[P0-3] 处理前预览确认：列出各类修改点的数量与前几个 before -> after，
       让用户确认偏移方向无误（原版无任何校验，真 UTC 文件会被改错）。
[P1-4] 放弃"正则改文本"，改为 XML 树遍历。原版正则只认 <time>2024-...Z</time>
       这一种紧凑写法，以下全部漏改：带属性 <time a="1">、内部含缩进换行、
       无秒 08:32Z、7 位小数（strptime %f 上限 6 位，异常被静默吞掉）。
[P1-5] 补齐 TCX：同时修正 <Lap StartTime="...">（属性）与 <Activity>/<Lap> 的 <Id>，
       否则同一文件里 Lap 起点与第一个轨迹点相差 8 小时（原版只改了 <Time> 元素）。
[P1-6] 原版正则在原始文本上跑，XML 注释里的 <time>...</time> 也会被改掉
       （实测注释被从 08:30 改成 00:30，且计数虚高）。树遍历不会碰注释。
[P1-7] 直接用 lxml 解析器读文件（按 XML 声明自动识别编码），
       GBK 等非 UTF-8 文件不再 UnicodeDecodeError（原版硬编码 encoding='utf-8'）。
[P2-8] 保留 DOCTYPE / standalone / 注释 / 命名空间前缀 / 原缩进（用于"原样输出"模式）。
[P2-9] 输出重名自动加序号 xxx_Z.gpx -> xxx_Z2.gpx，不再静默覆盖。
[P2-10] 临时文件 + 原子替换写出；后台线程处理 + 日志区 + 按钮管控；
        root.destroy() 退出；跨平台字体。
[P2-11] 新增**输出缩进格式化**（默认开启）。小米健康导出的 GPX/TCX 整个文档
        首尾相连、没有任何换行缩进。格式化只改写"元素之间的排版空白"
        （纯空白的 text / tail），绝不触碰任何含内容的文本节点；遇到混合内容
        （元素内既有文本又有子元素）整段跳过 —— 保证数据零损失。
        缩进可选 2 空格 / 4 空格 / Tab，也可在界面上关闭（关闭后输出
        与源文件排版完全一致）。
        实现上没有用 lxml 的 pretty_print：它无法指定缩进宽度、会把混合内容
        排坏、还会对 <time> 这类已知节点外的文本做额外改写，且默认 2 空格
        不可调。改为自己遍历树、只重写纯空白节点，可控且可验证。
        注：格式化会让大文件体积增大（30 万点约 28MB -> 38MB），这是可读性的代价。

【偏移量】
常量 CN_OFFSET_HOURS = 8 即"中国区时间比 UTC 快 8 小时"。如设备在别的时区，
改这一个常量即可。
"""

import os
import re
import tempfile
import threading
import tkinter as tk
from datetime import datetime, timedelta
from tkinter import filedialog, messagebox, ttk
from tkinter import font as tkfont
from tkinter import scrolledtext

# ------------------------------------------------------------
#  常量
# ------------------------------------------------------------

#: 小米健康导出的时间标志实际是 UTC+8 的本地时间
CN_OFFSET_HOURS = 8

#: 输出文件名后缀
OUTPUT_SUFFIX = "_Z"

#: 会被误判为"已处理过"的后缀
DONE_SUFFIXES = ("_Z", "_UTC")

#: 需要修正的元素（按本地名小写匹配；GPX 是 <time>，TCX 是 <Time>，
#: 部分格式用 <Timestamp>）
TIME_ELEMENT_NAMES = ("time", "timestamp")

#: 需要修正的属性（TCX 的 <Lap StartTime="...">）
TIME_ATTRIBUTE_NAMES = ("StartTime",)

#: TCX 的 <Id>（Activity / Lap 的标识时间）
ID_ELEMENT_NAME = "Id"

#: 输出缩进格式化的可选缩进：(界面显示文案, 实际缩进字符)
INDENT_OPTIONS = (
    ("2 个空格", "  "),
    ("4 个空格", "    "),
    ("制表符 (Tab)", "\t"),
)

#: 默认缩进
DEFAULT_INDENT = INDENT_OPTIONS[0][1]

#: 匹配「日期时间 + Z」的完整写法
#: 兼容：T 或空格分隔、秒可省略、任意位小数秒
_FLAG_RE = re.compile(
    r'^(?P<y>\d{4})-(?P<mo>\d{2})-(?P<d>\d{2})(?P<sep>[T ])'
    r'(?P<h>\d{2}):(?P<mi>\d{2})(?::(?P<s>\d{2}))?'
    r'(?P<frac>\.\d+)?[Zz]$'
)


# ------------------------------------------------------------
#  时间文本处理（纯函数，可独立测试）
# ------------------------------------------------------------

def parse_flagged_local(text):
    """
    解析「中国区本地时间 + Z」这一错误标志。

    只接受以 Z / z 结尾的写法 —— 这正是需要修正的错误标志；
    带 +08:00 或完全无时区的写法不属于本工具的目标，一律不动。

    返回 dict 或 None：
        {'dt': naive datetime, 'sep': 'T'|' ',
         'frac': '.123' 或 '', 'has_sec': bool}
    """
    if not text:
        return None
    m = _FLAG_RE.match(text.strip())
    if not m:
        return None
    try:
        dt = datetime(int(m['y']), int(m['mo']), int(m['d']),
                      int(m['h']), int(m['mi']), int(m['s'] or 0))
    except ValueError:
        return None
    return {
        'dt': dt,
        'sep': m['sep'],
        'frac': m['frac'] or '',
        'has_sec': m['s'] is not None,
    }


def to_utc_text(info):
    """
    把解析结果转成真正的 UTC + Z 文本。

    小数秒部分**按原样拼回**，不经过 datetime 的微秒字段，
    因此 7 位及以上小数秒也能原值保留（datetime 只有微秒精度）。
    """
    dt = info['dt'] - timedelta(hours=CN_OFFSET_HOURS)
    head = dt.strftime('%Y-%m-%d')
    body = dt.strftime('%H:%M:%S') if info['has_sec'] else dt.strftime('%H:%M')
    return '%s%s%s%sZ' % (head, info['sep'], body, info['frac'])


def local_name(tag):
    """取标签 / 属性名的本地名（去掉 {namespace} 前缀）。"""
    if not isinstance(tag, str):
        return ''
    return tag.rsplit('}', 1)[1] if tag.startswith('{') else tag


# ------------------------------------------------------------
#  扫描与修正
# ------------------------------------------------------------

class Correction(object):
    """一次修正动作。"""

    __slots__ = ('node', 'attr', 'label', 'old', 'new')

    def __init__(self, node, attr, label, old, new):
        self.node = node
        self.attr = attr      # None 表示改元素文本
        self.label = label    # 界面展示用
        self.old = old
        self.new = new


class Analysis(object):
    """解析 + 扫描的结果，供预览确认后再落盘。"""

    def __init__(self):
        self.tree = None
        self.source_path = ''
        self.corrections = []      # [Correction]
        self.untouched = []        # [(label, text)] 形似时间但不符合目标格式
        self.counts = {}           # label -> 次数
        self.source_encoding = ''  # 源文件声明的编码
        self.has_declaration = True    # 源文件是否有 <?xml ...?>
        self.standalone = None         # 'yes' / 'no' / None（源文件没写）
        self.ends_with_newline = True  # 源文件是否以换行结尾

    @property
    def total(self):
        return len(self.corrections)


def _add_leading_trailing(raw, new):
    """替换元素文本时保留原有的首尾空白（缩进 / 换行）。"""
    lead = raw[:len(raw) - len(raw.lstrip())]
    trail = raw[len(raw.rstrip()):]
    return lead + new + trail


def reindent_tree(root, indent=DEFAULT_INDENT):
    """
    就地把整棵 XML 树重新缩进排版（输出格式化）。

    设计要点（保证"数据零改动"）：
      · 只改写**纯空白**的 text / tail —— 也就是元素之间的排版空白；
        任何含实际内容的文本节点一律不动，所以不会吃掉或改动数据。
      · 元素自身没有子元素时不处理（<ele>48.5</ele> 保持一行）。
      · 遇到**混合内容**（元素里既有文本又有子元素，例如
        <desc>起点 <b>牌楼</b> 东侧</desc>）时整段跳过：
        往这种位置插换行会改变文本内容，宁可排版差一点。
      · 不用 lxml 的 pretty_print：它无法指定缩进宽度、会把混合内容排坏。

    返回被重排的元素个数。
    """
    touched = [0]

    def walk(el, depth):
        kids = list(el)          # 含注释 / 处理指令，它们也要换行才好看
        if not kids:
            return
        # 混合内容：文本里有实义内容，或某个子节点后面跟着实义文本 —— 原样保留
        if (el.text and el.text.strip()) or any(k.tail and k.tail.strip() for k in kids):
            return
        pad = '\n' + indent * (depth + 1)
        end = '\n' + indent * depth
        el.text = pad
        last = len(kids) - 1
        for i, kid in enumerate(kids):
            walk(kid, depth + 1)
            kid.tail = end if i == last else pad
        touched[0] += 1

    walk(root, 0)
    return touched[0]


_DECL_RE = re.compile(rb'<\?xml\s[^>]*\?>')
_STANDALONE_RE = re.compile(rb'standalone\s*=\s*[\'"](yes|no)[\'"]', re.I)


def read_source_declaration(path):
    """
    从源文件读出 XML 声明信息。

    返回 (has_declaration, standalone)：
      has_declaration -- 源文件开头是否有 <?xml ...?>
      standalone      -- 'yes' / 'no' / None（源文件没写这个属性）

    注：lxml 的 docinfo.standalone 对"没写"和"写了 no"都返回 False，
    无法区分，所以必须直接读原文。
    """
    try:
        with open(path, 'rb') as f:
            head = f.read(1024)
    except OSError:
        return True, None
    m = _DECL_RE.search(head)
    if not m:
        return False, None
    sm = _STANDALONE_RE.search(m.group(0))
    return True, (sm.group(1).decode('ascii').lower() if sm else None)


def read_ends_with_newline(path):
    """源文件是否以换行结尾（lxml 写出时不会补，需要自己补回来）。"""
    try:
        with open(path, 'rb') as f:
            f.seek(0, os.SEEK_END)
            size = f.tell()
            if size == 0:
                return False
            f.seek(max(0, size - 1))
            return f.read(1) in (b'\n', b'\r')
    except OSError:
        return False


def analyze_file(path, fix_tcx_extras=True):
    """
    解析文件并扫描所有需要修正的时间标志。不写盘。

    返回 Analysis；任何解析失败抛 ValueError。
    """
    from lxml import etree

    ana = Analysis()
    ana.source_path = path

    # 直接交给 lxml 解析：它会按 XML 声明自动识别编码，
    # 不必也不会再手工 open(encoding='utf-8')。
    parser = etree.XMLParser(remove_blank_text=False, resolve_entities=False)
    try:
        ana.tree = etree.parse(path, parser)
    except etree.XMLSyntaxError as e:
        raise ValueError("XML 解析失败（文件可能不是有效的 GPX/TCX）：%s" % e)
    except OSError as e:
        raise ValueError("无法读取文件：%s" % e)

    root = ana.tree.getroot()
    if root is None:
        raise ValueError("文件内容为空，没有 XML 根元素。")
    try:
        ana.source_encoding = (ana.tree.docinfo.encoding or '').upper()
    except Exception:
        ana.source_encoding = ''

    # XML 声明与结尾换行：lxml 的 docinfo 分不出"没写 standalone"和"写了 no"，
    # 所以直接从源文件里读原文，保证输出与源文件一致。
    ana.has_declaration, ana.standalone = read_source_declaration(path)
    ana.ends_with_newline = read_ends_with_newline(path)

    def record(label, node, attr, raw_text):
        info = parse_flagged_local(raw_text)
        if info:
            ana.corrections.append(
                Correction(node, attr, label, raw_text.strip(), to_utc_text(info)))
            ana.counts[label] = ana.counts.get(label, 0) + 1
            return True
        # 只把"长得像时间"的内容列进未处理清单，避免把普通 Id
        # 之类的文本当成时间误报给用户
        text = (raw_text or '').strip()
        if text and re.search(r'\d{1,2}:\d{2}', text):
            ana.untouched.append((label, text))
        return False

    for el in root.iter():
        if not isinstance(el.tag, str):     # 跳过注释 / 处理指令
            continue
        name = local_name(el.tag)
        low = name.lower()

        # 1) 时间元素：GPX <time> / TCX <Time> / <Timestamp>
        if low in TIME_ELEMENT_NAMES and el.text:
            record(name, el, None, el.text)

        # 2) TCX 的 Activity / Lap 标识时间
        elif fix_tcx_extras and name == ID_ELEMENT_NAME and el.text:
            record(name, el, None, el.text)

        # 3) 时间属性：TCX <Lap StartTime="...">
        if fix_tcx_extras:
            for aname in list(el.attrib):
                if local_name(aname) in TIME_ATTRIBUTE_NAMES:
                    record(local_name(aname), el, aname, el.get(aname))

    return ana


def apply_and_write(analysis, pretty=True, indent=DEFAULT_INDENT):
    """
    应用修正并原子写出。返回输出文件路径。
    调用前请确保 analysis.total > 0。

    pretty=True  （默认）输出做缩进格式化，便于阅读；
    pretty=False 完全保留源文件排版（只改时间文本）。
    """
    if analysis.total == 0:
        raise ValueError("没有需要修正的内容，未生成文件。")

    path = analysis.source_path
    tree = analysis.tree

    for c in analysis.corrections:
        if c.attr is None:
            # 格式化模式下，被修正节点内部的换行缩进一并规整掉；
            # 原样模式下则保留该节点原有的首尾空白。
            c.node.text = c.new if pretty else _add_leading_trailing(c.node.text or '', c.new)
        else:
            c.node.set(c.attr, c.new)

    if pretty:
        root_el = tree.getroot()
        if root_el is not None:
            reindent_tree(root_el, indent)

    # 输出文件名：原名 + _Z，重名自动加序号
    dir_name = os.path.dirname(os.path.abspath(path))
    base, ext = os.path.splitext(os.path.basename(path))
    out_path = os.path.join(dir_name, '%s%s%s' % (base, OUTPUT_SUFFIX, ext))
    seq = 2
    while os.path.exists(out_path):
        out_path = os.path.join(dir_name, '%s%s%d%s' % (base, OUTPUT_SUFFIX, seq, ext))
        seq += 1

    # 写出时不用 lxml 的 pretty_print（缩进已在 reindent_tree 里做好，
    # 这里只负责序列化）。XML 声明自己拼，以便原样保留源文件的 standalone
    # 属性与双引号风格（lxml 固定输出单引号，且会凭空补上 standalone='no'）。
    tmp_fd, tmp_path = tempfile.mkstemp(dir=dir_name, prefix='.xztime_', suffix='.tmp')
    os.close(tmp_fd)
    try:
        tree.write(tmp_path, xml_declaration=False, encoding='UTF-8')

        with open(tmp_path, 'rb') as f:
            body = f.read()

        prefix = b''
        if analysis.has_declaration:
            decl = '<?xml version="1.0" encoding="UTF-8"'
            if analysis.standalone in ('yes', 'no'):
                decl += ' standalone="%s"' % analysis.standalone
            prefix = decl.encode('ascii') + b'?>' + b'\n'
        # 格式化输出时，文件末尾统一补一个换行（正常文本文件该有的样子）；
        # 原样输出时，严格跟随源文件（有则保留、无则不加）。
        suffix = b'\n' if (pretty or analysis.ends_with_newline) else b''

        with open(tmp_path, 'wb') as f:
            f.write(prefix + body + suffix)
        os.replace(tmp_path, out_path)
        tmp_path = None
        try:
            os.chmod(out_path, os.stat(path).st_mode & 0o777)
        except OSError:
            pass
    finally:
        if tmp_path and os.path.exists(tmp_path):
            try:
                os.remove(tmp_path)
            except OSError:
                pass

    return out_path


def verify_output(out_path):
    """回读校验：文件可解析，且不再残留任何非 UTC+Z 的时间元素。返回合规元素数。"""
    from lxml import etree
    try:
        tree = etree.parse(out_path)
    except Exception as e:
        raise ValueError("输出文件无法重新解析：%s" % e)

    n_ok = 0
    n_bad = []
    for el in tree.getroot().iter():
        if not isinstance(el.tag, str):
            continue
        low = local_name(el.tag).lower()
        if low in TIME_ELEMENT_NAMES and el.text:
            s = el.text.strip()
            if re.match(r'^\d{4}-\d{2}-\d{2}[T ]\d{2}:\d{2}(:\d{2})?(\.\d+)?Z$', s):
                n_ok += 1
            else:
                n_bad.append(s)
    if n_bad:
        raise ValueError("校验失败：输出中仍有非 UTC+Z 的时间标志 %s" % n_bad[:3])
    return n_ok


# ------------------------------------------------------------
#  GUI
# ------------------------------------------------------------

def pick_font():
    """跨平台挑选可用中文字体。"""
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


def looks_already_done(path):
    """文件名是否以 _Z / _UTC 结尾（疑似已处理过）。"""
    base = os.path.splitext(os.path.basename(path))[0]
    for suf in DONE_SUFFIXES:
        if base.endswith(suf) or re.search(re.escape(suf) + r'\d+$', base):
            return True
    return False


class TimeCorrectorApp(object):
    def __init__(self, root):
        self.root = root
        self.root.title("小米健康 GPS 轨迹时间修正工具（中国区时间 -> UTC）")
        self.root.geometry("760x620")
        self.root.minsize(680, 560)

        self.font_family = pick_font()
        self.style = ttk.Style()
        try:
            self.style.theme_use("clam")
        except Exception:
            pass
        self.style.configure("Title.TLabel", font=(self.font_family, 14, "bold"))
        self.style.configure("Info.TLabel", font=(self.font_family, 10))
        self.style.configure("Hint.TLabel", font=(self.font_family, 9), foreground="#777")
        self.style.configure("Status.TLabel", font=(self.font_family, 11), foreground="#555")
        self.style.configure("Action.TButton", font=(self.font_family, 12), padding=8)
        self.style.configure("TCheckbutton", font=(self.font_family, 10))

        self.file_path_var = tk.StringVar(value="未选择文件")
        self.status_var = tk.StringVar(value="就绪：请选择小米健康导出的 .gpx 或 .tcx 文件")
        self.fix_tcx_extras = tk.BooleanVar(value=True)
        self.preview_first = tk.BooleanVar(value=True)
        self.pretty_output = tk.BooleanVar(value=True)
        self.indent_label = tk.StringVar(value=INDENT_OPTIONS[0][0])

        self._busy = False
        self._analysis = None

        self._build_ui()

    # ---------- 界面 ----------
    def _build_ui(self):
        main = ttk.Frame(self.root, padding=16)
        main.pack(fill=tk.BOTH, expand=True)

        ttk.Label(main, text="小米健康 GPS 轨迹时间修正工具",
                  style="Title.TLabel").pack(anchor=tk.W)
        ttk.Label(main, text="把「中国区时间 + Z」改写成「UTC + Z」（统一减 %d 小时），"
                             "其余数据原样保留。" % CN_OFFSET_HOURS,
                  style="Info.TLabel").pack(anchor=tk.W, pady=(2, 10))

        file_frame = ttk.LabelFrame(main, text="文件选择", padding=10)
        file_frame.pack(fill=tk.X, pady=(0, 10))
        self.file_label = ttk.Label(file_frame, textvariable=self.file_path_var,
                                    style="Info.TLabel", wraplength=520,
                                    justify=tk.LEFT, foreground="#006400")
        self.file_label.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 10))
        self.btn_browse = ttk.Button(file_frame, text="选择文件", style="Action.TButton",
                                     command=self.select_file)
        self.btn_browse.pack(side=tk.RIGHT)

        opt = ttk.LabelFrame(main, text="选项", padding=10)
        opt.pack(fill=tk.X, pady=(0, 10))
        self.chk_preview = ttk.Checkbutton(
            opt, variable=self.preview_first,
            text="处理前先预览确认（推荐：会列出修改点数量与前几个前后对照）")
        self.chk_preview.pack(anchor=tk.W)
        self.chk_tcx = ttk.Checkbutton(
            opt, variable=self.fix_tcx_extras,
            text="同时修正 TCX 的 Lap StartTime 属性与活动 Id（避免同文件内时间不一致）")
        self.chk_tcx.pack(anchor=tk.W)

        fmt = ttk.Frame(opt)
        fmt.pack(anchor=tk.W, fill=tk.X, pady=(2, 0))
        self.chk_pretty = ttk.Checkbutton(
            fmt, variable=self.pretty_output, command=self._toggle_indent,
            text="输出格式化（按层级缩进排版，便于阅读）")
        self.chk_pretty.pack(side=tk.LEFT)
        ttk.Label(fmt, text="缩进：", style="Info.TLabel").pack(side=tk.LEFT, padx=(14, 4))
        self.cmb_indent = ttk.Combobox(
            fmt, textvariable=self.indent_label, state="readonly", width=13,
            values=[label for label, _ in INDENT_OPTIONS])
        self.cmb_indent.pack(side=tk.LEFT)

        ttk.Label(opt, text="注：小米导出的文件通常是「首尾相连」的一整行。开启格式化后"
                            "会按层级换行缩进，只改排版空白、不动任何数据；"
                            "关闭则输出与源文件排版完全一致。",
                  style="Hint.TLabel").pack(anchor=tk.W, pady=(4, 0))
        ttk.Label(opt, text="注：带 +08:00 等真实偏移的时间、以及没有任何时区标记的时间，"
                            "不属于本工具的目标，一律保持原样。",
                  style="Hint.TLabel").pack(anchor=tk.W, pady=(2, 0))

        ttk.Label(main, textvariable=self.status_var,
                  style="Status.TLabel").pack(fill=tk.X, pady=(0, 6))

        log_frame = ttk.LabelFrame(main, text="处理报告", padding=6)
        log_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 10))
        self.log_text = scrolledtext.ScrolledText(
            log_frame, height=9, wrap=tk.WORD, font=(self.font_family, 10),
            background="#fbfbfb", foreground="#333", relief=tk.FLAT, state=tk.DISABLED)
        self.log_text.pack(fill=tk.BOTH, expand=True)

        bar = ttk.Frame(main)
        bar.pack()
        self.btn_run = ttk.Button(bar, text="开始修正", style="Action.TButton",
                                  command=self.start)
        self.btn_run.pack(side=tk.LEFT, padx=12)
        self.btn_exit = ttk.Button(bar, text="退出程序", style="Action.TButton",
                                   command=self.do_exit)
        self.btn_exit.pack(side=tk.LEFT, padx=12)

        self._toggle_indent()

    def log(self, msg):
        try:
            self.log_text.config(state=tk.NORMAL)
            self.log_text.insert(tk.END, msg + "\n")
            self.log_text.see(tk.END)
            self.log_text.config(state=tk.DISABLED)
        except tk.TclError:
            pass

    def ui(self, func, *args):
        try:
            self.root.after(0, lambda: func(*args))
        except tk.TclError:
            pass

    def set_busy(self, busy):
        self._busy = busy
        state = tk.DISABLED if busy else tk.NORMAL
        for w in (self.btn_run, self.btn_browse):
            try:
                w.config(state=state)
            except tk.TclError:
                pass

    def _toggle_indent(self):
        """格式化关掉时，缩进下拉框跟着置灰。"""
        try:
            self.cmb_indent.config(state="readonly" if self.pretty_output.get()
                                   else tk.DISABLED)
        except tk.TclError:
            pass

    def current_indent(self):
        """当前选择的缩进字符（以文案反查，避免依赖下拉框序号）。"""
        label = self.indent_label.get()
        for text, chars in INDENT_OPTIONS:
            if text == label:
                return chars
        return DEFAULT_INDENT

    @staticmethod
    def indent_desc(indent):
        for text, chars in INDENT_OPTIONS:
            if chars == indent:
                return text
        return repr(indent)

    # ---------- 流程 ----------
    def select_file(self):
        path = filedialog.askopenfilename(
            title="选择小米健康导出的轨迹文件",
            filetypes=[("GPS 轨迹文件", ("*.gpx", "*.tcx")), ("所有文件", "*.*")])
        if not path:
            return
        self.file_path_var.set(path)
        self.status_var.set("已选择：%s" % os.path.basename(path))
        self.log("已选择：%s" % path)

    def start(self):
        if self._busy:
            return
        path = self.file_path_var.get()
        if not path or not os.path.isfile(path):
            messagebox.showwarning("提示", "请先选择一个存在的 .gpx 或 .tcx 文件！")
            return

        # ★ 防重复处理闸门
        if looks_already_done(path):
            if not messagebox.askyesno(
                    "该文件可能已经修正过",
                    "文件名「%s」以 %s 结尾，看起来是本工具的输出文件。\n\n"
                    "如果它已经修正过，再次运行会把时间**再减 %d 小时**，"
                    "得到错误的结果。\n\n确实要继续处理吗？"
                    % (os.path.basename(path), " / ".join(DONE_SUFFIXES), CN_OFFSET_HOURS),
                    icon="warning", default="no"):
                self.log("已取消：用户确认该文件无需再次处理。")
                self.status_var.set("已取消（文件疑似已修正过）")
                return

        self.set_busy(True)
        self.status_var.set("正在解析并扫描时间标志...")
        self.log("-" * 60)
        self.log("开始处理：%s" % os.path.basename(path))
        threading.Thread(target=self._worker_analyze, args=(path,), daemon=True).start()

    def _worker_analyze(self, path):
        try:
            ana = analyze_file(path, fix_tcx_extras=self.fix_tcx_extras.get())
        except ValueError as e:
            self.ui(self._fail, str(e), "失败：文件无法解析")
            return
        except Exception as e:
            import traceback
            self.ui(self.log, traceback.format_exc())
            self.ui(self._fail, "处理出错：%s" % e, "处理失败")
            return
        self.ui(self._after_analyze, ana)

    def _after_analyze(self, ana):
        self.status_var.set("扫描完成：发现 %d 处待修正时间标志" % ana.total)

        if ana.total == 0:
            # ★ 0 处修改：不生成文件，也不谎报成功
            self.set_busy(False)
            detail = ""
            if ana.untouched:
                detail = ("\n\n文件里这些位置有时间值，但不属于本次修正的目标格式"
                          "（已保持原样）：\n" +
                          "\n".join("· <%s> %s" % (l, t)
                                    for l, t in ana.untouched[:5]))
            self.log("未发现需要修正的时间标志，未生成任何文件。")
            messagebox.showinfo(
                "未发现需要修正的时间标志",
                "这个文件里没有找到「中国区时间 + Z」形式的时间标志。\n\n"
                "可能的原因：\n"
                "· 文件已经修正过了；\n"
                "· 不是小米健康导出的文件；\n"
                "· 时间已经带 +08:00 这类真实偏移（本就正确，无需修改）。%s" % detail)
            return

        self.log("发现 %d 处待修正：" % ana.total)
        for label, n in sorted(ana.counts.items(), key=lambda kv: -kv[1]):
            self.log("   %-12s %d 处" % (label, n))
        if ana.source_encoding and ana.source_encoding.replace('-', '') != 'UTF8':
            self.log("提示：源文件编码为 %s，输出统一为 UTF-8（GPX/TCX 规范要求）。"
                     % ana.source_encoding)
        self.log("即将统一减去 %d 小时（中国区时间 -> UTC）：" % CN_OFFSET_HOURS)
        for c in ana.corrections[:3]:
            self.log("   %s -> %s" % (c.old, c.new))
        if ana.total > 3:
            self.log("   ...（共 %d 处）" % ana.total)

        if ana.untouched:
            self.log("以下位置有时间值但不符合目标格式，将保持原样：")
            for l, t in ana.untouched[:5]:
                self.log("   <%s> %s" % (l, t))
            if len(ana.untouched) > 5:
                self.log("   ...（共 %d 处）" % len(ana.untouched))

        if not self.preview_first.get():
            self._write(ana)
            return

        # ★ 预览确认：让用户亲眼看到偏移方向
        self.set_busy(False)
        sample = "\n".join("  %s\n    -> %s" % (c.old, c.new)
                           for c in ana.corrections[:3])
        if not messagebox.askyesno(
                "确认修正方向",
                "共发现 %d 处时间标志，将统一**减去 %d 小时**：\n\n%s%s\n\n"
                "确认按此方向修正吗？"
                % (ana.total, CN_OFFSET_HOURS, sample,
                   "\n  ...（共 %d 处）" % ana.total if ana.total > 3 else ""),
                default="yes"):
            self.log("已取消：用户在预览阶段放弃。")
            self.status_var.set("已取消（预览未确认）")
            return

        self.set_busy(True)
        self._write(ana)

    def _write(self, ana):
        # 在界面线程里先读好选项，再交给后台线程落盘（大文件格式化耗时明显，
        # 放在界面线程会让窗口卡住）
        pretty = bool(self.pretty_output.get())
        indent = self.current_indent()
        self.set_busy(True)
        self.status_var.set("正在写出%s..." % ("（格式化排版中）" if pretty else ""))
        threading.Thread(target=self._worker_write,
                         args=(ana, pretty, indent), daemon=True).start()

    def _worker_write(self, ana, pretty, indent):
        try:
            in_size = os.path.getsize(ana.source_path)
            out = apply_and_write(ana, pretty=pretty, indent=indent)
            out_size = os.path.getsize(out)
            n = verify_output(out)
        except ValueError as e:
            self.ui(self._fail, str(e), "失败：写入或校验未通过")
            return
        except Exception as e:
            import traceback
            self.ui(self.log, traceback.format_exc())
            self.ui(self._fail, "处理出错：%s" % e, "处理失败")
            return
        self.ui(self._after_write, ana, out, n, in_size, out_size, pretty, indent)

    def _after_write(self, ana, out, n, in_size, out_size, pretty, indent):
        self.set_busy(False)
        self.status_var.set("完成 → %s" % os.path.basename(out))
        self.log("已修正 %d 处，输出：%s" % (ana.total, out))
        if pretty:
            self.log("输出格式化：已开启（缩进 %s）" % self.indent_desc(indent))
            self.log("体积：%.1f KB -> %.1f KB（格式化会增加换行缩进，属正常）"
                     % (in_size / 1024.0, out_size / 1024.0))
            if out_size > in_size * 1.5 and in_size > 512 * 1024:
                self.log("提示：源文件较大且为紧凑写法，格式化后体积增长明显；"
                         "如不需要，可取消勾选「输出格式化」再跑一次。")
            fmt_note = "输出已按层级缩进排版（只改排版空白，数据未动）。"
        else:
            self.log("输出格式化：已关闭（排版与源文件完全一致）")
            fmt_note = "输出排版与源文件完全一致。"
        self.log("回读校验通过，共 %d 个 UTC+Z 时间元素。" % n)
        messagebox.showinfo(
            "修正完成",
            "已修正 %d 处时间标志（全部改为 UTC + Z）。\n\n%s\n\n"
            "输出文件：\n%s\n\n原文件未做任何改动。" % (ana.total, fmt_note, out))

    def _fail(self, message, status):
        self.set_busy(False)
        self.status_var.set(status)
        self.log(status + "：" + message)
        messagebox.showerror("错误", message)

    def do_exit(self):
        if self._busy and not messagebox.askyesno("确认", "正在处理中，确定要强制退出吗？"):
            return
        if messagebox.askyesno("确认", "确定要退出程序吗？"):
            self.root.destroy()


def main():
    try:
        import lxml  # noqa: F401
    except ImportError:
        import sys
        msg = ("缺少依赖 lxml。请在终端运行：\n\n"
               "pip install lxml -i https://pypi.tuna.tsinghua.edu.cn/simple")
        try:
            r = tk.Tk()
            r.withdraw()
            messagebox.showerror("缺少依赖", msg)
            r.destroy()
        except Exception:
            pass
        print(msg, file=sys.stderr)
        return 1

    root = tk.Tk()
    TimeCorrectorApp(root)
    root.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
