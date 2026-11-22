#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
M3U 直播源编辑管理系统  (主程序)
=============================================================
文件：M3U_Live_Editor.py
技术栈：Python 3.10 + PySide6 (Qt6) + requests + SQLite3
功能：m3u / m3u8 直播源文件的解析、编辑、增删改、批量处理、
      链接可用性测试（多线程）、ID 扫描、新旧文件对比分析、
      设置实时自动保存与持久化。
说明：本文件为唯一主程序（最终更新版），Nuitka 编译只使用此文件。
      版本 / 文档同步规则见同目录《软件升级迭代记录.md》。
=============================================================
"""

from __future__ import annotations

import os
import re
import sys
import csv
import json
import time
import difflib
import base64
import html
import shutil
import struct
import sqlite3
import hashlib
import gzip
import importlib.util
import itertools
import subprocess
import threading
import traceback
import unicodedata
import urllib.parse
import http.server
import webbrowser
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta

# ----------------------------------------------------------------------------
# Qt (PySide6)
# ----------------------------------------------------------------------------
from PySide6.QtCore import (
    Qt, QObject, QThread, Signal, Slot, QSize, QTimer, QSettings, QProcess,
    QAbstractTableModel, QSortFilterProxyModel, QModelIndex, QUrl, QByteArray,
    QRegularExpression, QEvent, QPoint, QRect, QMargins,
)
from PySide6.QtGui import (
    QIcon, QAction, QActionGroup, QFont, QColor, QBrush, QPalette, QKeySequence,
    QGuiApplication, QDesktopServices, QPixmap, QTextCursor, QCursor,
)
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QTabWidget, QVBoxLayout, QHBoxLayout,
    QFormLayout, QGridLayout, QLayout, QLabel, QLineEdit, QPushButton, QToolButton,
    QToolBar, QComboBox, QSpinBox, QDoubleSpinBox, QCheckBox, QRadioButton,
    QButtonGroup, QGroupBox, QTableView, QTableWidget, QTableWidgetItem,
    QHeaderView, QAbstractItemView, QSplitter, QFileDialog, QMessageBox,
    QProgressBar, QStatusBar, QMenu, QMenuBar, QDialog, QDialogButtonBox,
    QPlainTextEdit, QTextEdit, QScrollArea, QFrame, QSizePolicy, QListWidget,
    QListWidgetItem, QStackedWidget, QStyle, QSpacerItem, QSlider, QInputDialog,
    QApplication as _QApp,
)

# Qt Multimedia（唯一的 FFmpeg 解码内核：不依赖 Chromium / GL 上下文）
try:
    from PySide6.QtMultimedia import (  # type: ignore
        QAudioOutput, QMediaPlayer, QVideoSink,
    )
    from PySide6.QtMultimediaWidgets import QVideoWidget  # type: ignore
    M3ULE_QTMM_AVAILABLE = True
    M3ULE_QTMM_ERROR = ""
except Exception as _m3ule_qtmm_exc:  # pragma: no cover - 取决于运行环境
    QAudioOutput = QMediaPlayer = QVideoSink = None  # type: ignore
    QVideoWidget = None  # type: ignore
    M3ULE_QTMM_AVAILABLE = False
    M3ULE_QTMM_ERROR = f"{type(_m3ule_qtmm_exc).__name__}: {_m3ule_qtmm_exc}"

# ----------------------------------------------------------------------------
# 应用常量（全局唯一前缀 M3ULE_）
# ----------------------------------------------------------------------------
M3ULE_APP_NAME_CN = "M3U 直播源编辑管理系统"
M3ULE_APP_NAME_EN = "M3U_Live_Editor"
M3ULE_APP_ORG = "duma520"
M3ULE_VERSION = "1.8.4"
M3ULE_BUILD_DATE = "2026-10-06"
M3ULE_WINDOW_TITLE = f"{M3ULE_APP_NAME_CN}  v{M3ULE_VERSION}"

M3ULE_DEFAULT_USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)

M3ULE_EXTINF_ATTR_ORDER = (
    "channelID", "tvg-chno", "tvg-name", "tvg-id", "tvg-logo", "group-title",
)

M3ULE_PROBE_MAX_PLAYLIST_BYTES = 512 * 1024
M3ULE_PROBE_MAX_MEDIA_BYTES = 96 * 1024
M3ULE_PROBE_MAX_SEGMENT_BYTES = 128 * 1024

M3ULE_STATUS_OK = "成功"
M3ULE_STATUS_PARTIAL = "部分可用"
M3ULE_STATUS_FAIL = "失败"
M3ULE_STATUS_TIMEOUT = "超时"
M3ULE_STATUS_ERROR = "错误"
M3ULE_STATUS_CANCEL = "已取消"
M3ULE_STATUS_NONE = ""

M3ULE_TEST_STATE_ICON_MAP = {
    M3ULE_STATUS_OK: "🟢",
    M3ULE_STATUS_PARTIAL: "🟡",
    M3ULE_STATUS_FAIL: "🔴",
    M3ULE_STATUS_TIMEOUT: "🟠",
    M3ULE_STATUS_ERROR: "⚫",
    M3ULE_STATUS_CANCEL: "⚪",
    M3ULE_STATUS_NONE: "⚪",
}

# ----------------------------------------------------------------------------
# 路径 / 环境
# ----------------------------------------------------------------------------

def m3ule_get_program_dir() -> str:
    """返回程序所在目录（兼容源码运行 / Nuitka 编译 / PyInstaller）。"""
    override = os.environ.get("M3ULE_PROGRAM_DIR", "").strip()
    if override and os.path.isdir(override):
        return os.path.abspath(override)
    if "__compiled__" in globals():
        return os.path.dirname(os.path.abspath(sys.argv[0]))
    if getattr(sys, "frozen", False):
        return os.path.dirname(os.path.abspath(sys.executable))
    return os.path.dirname(os.path.abspath(__file__))


def m3ule_get_icon_path() -> str:
    """icon.ico 路径（存在返回路径，否则返回空字符串）。"""
    program_dir = m3ule_get_program_dir()
    candidates = [
        os.path.join(program_dir, "icon.ico"),
        os.path.join(program_dir, "_scaffold", "icon.ico"),
    ]
    meipass = getattr(sys, "_MEIPASS", None)
    if meipass:
        candidates.insert(0, os.path.join(meipass, "icon.ico"))
    for path in candidates:
        if os.path.isfile(path):
            return path
    return ""


def m3ule_ensure_dir(path: str) -> str:
    try:
        os.makedirs(path, exist_ok=True)
    except OSError:
        pass
    return path


def m3ule_get_data_dir() -> str:
    return m3ule_ensure_dir(os.path.join(m3ule_get_program_dir(), "data"))


def m3ule_get_backup_dir() -> str:
    return m3ule_ensure_dir(os.path.join(m3ule_get_program_dir(), "backups"))


def m3ule_get_log_dir() -> str:
    return m3ule_ensure_dir(os.path.join(m3ule_get_data_dir(), "logs"))


def m3ule_get_env_path() -> str:
    return os.path.join(m3ule_get_program_dir(), ".env")


def m3ule_get_db_path() -> str:
    env_path = os.environ.get("M3ULE_DB_PATH", "").strip()
    if env_path:
        return env_path
    return os.path.join(m3ule_get_data_dir(), "m3u_live_editor.db")


def m3ule_get_settings_path() -> str:
    return os.path.join(m3ule_get_data_dir(), "settings.ini")


def m3ule_load_env_file(path: str = "") -> dict:
    """读取 .env（KEY=VALUE，支持 # 注释、引号），加载到 os.environ（不覆盖已有变量）。"""
    env_file = path or m3ule_get_env_path()
    loaded: dict = {}
    if not os.path.isfile(env_file):
        return loaded
    try:
        with open(env_file, "r", encoding="utf-8-sig", errors="replace") as handle:
            for raw_line in handle:
                line = raw_line.strip()
                if not line or line.startswith("#"):
                    continue
                if line.lower().startswith("export "):
                    line = line[7:].strip()
                if "=" not in line:
                    continue
                key, _, value = line.partition("=")
                key = key.strip()
                value = value.strip()
                if len(value) >= 2 and value[0] == value[-1] and value[0] in ("\"", "'"):
                    value = value[1:-1]
                if not key:
                    continue
                loaded[key] = value
                os.environ.setdefault(key, value)
    except OSError:
        pass
    return loaded


def m3ule_save_env_key(key: str, value: str, path: str = "") -> bool:
    """把键值写入 .env（已有则替换该行，没有则追加）。"""
    env_file = path or m3ule_get_env_path()
    key = (key or "").strip()
    if not key:
        return False
    lines: list = []
    if os.path.isfile(env_file):
        try:
            with open(env_file, "r", encoding="utf-8-sig", errors="replace") as handle:
                lines = handle.read().splitlines()
        except OSError:
            lines = []
    replaced = False
    output: list = []
    for line in lines:
        stripped = line.strip()
        head = stripped[7:].strip() if stripped.lower().startswith("export ") else stripped
        name = head.split("=", 1)[0].strip() if "=" in head else ""
        if name == key:
            output.append(f"{key}={value}")
            replaced = True
        else:
            output.append(line)
    if not replaced:
        output.append(f"{key}={value}")
    try:
        with open(env_file, "w", encoding="utf-8") as handle:
            handle.write("\n".join(output).rstrip("\n") + "\n")
    except OSError:
        return False
    os.environ[key] = value
    return True


def m3ule_safe_int(value, default: int = 0) -> int:
    try:
        return int(str(value).strip())
    except (TypeError, ValueError):
        return default


def m3ule_safe_float(value, default: float = 0.0) -> float:
    try:
        return float(str(value).strip())
    except (TypeError, ValueError):
        return default


# ----------------------------------------------------------------------------
# #EXTINF 解析 / 格式化
# ----------------------------------------------------------------------------
_M3ULE_EXTINF_HEAD_RE = re.compile(r"^\s*#EXTINF\s*:(?P<body>.*)$", re.IGNORECASE)
_M3ULE_ATTR_RE = re.compile(
    r"([A-Za-z0-9_.\-]+)\s*=\s*(?:\"([^\"]*)\"|'([^']*)'|([^\s]+))"
)


def m3ule_split_extinf_body(body: str):
    """把 #EXTINF 的 body 拆成 (左半部分, 标题)，按第一个不在引号内的逗号分隔。"""
    in_quote = False
    for idx, ch in enumerate(body):
        if ch == '"':
            in_quote = not in_quote
        elif ch == "," and not in_quote:
            return body[:idx], body[idx + 1:]
    return body, ""


def m3ule_parse_extinf_line(line: str):
    """解析 #EXTINF 行，返回 (duration:str, attrs:OrderedDict, title:str)。"""
    match = _M3ULE_EXTINF_HEAD_RE.match(line)
    attrs: "OrderedDict[str, str]" = OrderedDict()
    if not match:
        return "0", attrs, ""
    left, title = m3ule_split_extinf_body(match.group("body"))
    left = left.strip()
    duration = "0"
    attr_text = ""
    if left:
        pieces = left.split(None, 1)
        duration = pieces[0].strip() or "0"
        if len(pieces) > 1:
            attr_text = pieces[1]
    for attr_match in _M3ULE_ATTR_RE.finditer(attr_text):
        key = attr_match.group(1)
        value = attr_match.group(2)
        if value is None:
            value = attr_match.group(3)
        if value is None:
            value = attr_match.group(4)
        if value is None:
            value = ""
        attrs[key] = value
    return duration, attrs, title


def m3ule_format_extinf_line(duration: str, attrs, title: str) -> str:
    """根据字段重新生成 #EXTINF 行（属性顺序按原顺序，新增属性按约定顺序补足）。"""
    ordered_keys: list = []
    for key in attrs.keys():
        if key not in ordered_keys:
            ordered_keys.append(key)
    for key in M3ULE_EXTINF_ATTR_ORDER:
        if key in attrs and key not in ordered_keys:
            ordered_keys.append(key)
    attr_parts = []
    for key in ordered_keys:
        value = attrs.get(key)
        if value is None:
            continue
        value_text = str(value).replace('"', "'").strip()
        if value_text == "" and key not in M3ULE_EXTINF_ATTR_ORDER:
            continue
        attr_parts.append(f'{key}="{value_text}"')
    head = f"#EXTINF:{duration if str(duration).strip() else '0'}"
    if attr_parts:
        head += " " + " ".join(attr_parts)
    return head + "," + (title if title is not None else "")


def m3ule_is_url_line(line: str) -> bool:
    stripped = line.strip()
    return bool(stripped) and not stripped.startswith("#")


def m3ule_test_state_to_avail(state: str):
    """把状态文本折成三态：True 有信号 / False 无信号 / None 未测。"""
    text = (state or "").strip()
    if not text:
        return None
    if M3ULE_STATUS_OK in text or M3ULE_STATUS_PARTIAL in text:
        return True
    if (M3ULE_STATUS_FAIL in text or M3ULE_STATUS_TIMEOUT in text
            or M3ULE_STATUS_ERROR in text or M3ULE_STATUS_CANCEL in text):
        return False
    return None


def m3ule_test_delta_label(prev_state: str, cur_state: str) -> str:
    """对比同一条链接「上一次」与「本次」的测试结果，给出差异结论。

    用于「对比上次」列：一眼看出这次测试相比上次是多了台还是少了台。
    """
    prev = m3ule_test_state_to_avail(prev_state)
    cur = m3ule_test_state_to_avail(cur_state)
    if prev is None:
        return M3ULE_DELTA_NONE if cur is None else M3ULE_DELTA_FIRST
    if cur is None:
        return M3ULE_DELTA_UNTESTED
    if prev and cur:
        return M3ULE_DELTA_KEEP_OK
    if prev and not cur:
        return M3ULE_DELTA_LOST
    if not prev and cur:
        return M3ULE_DELTA_GAINED
    return M3ULE_DELTA_KEEP_BAD


# ----------------------------------------------------------------------------
# 数据模型：单条频道条目
# ----------------------------------------------------------------------------

class M3ULiveEditorEntry:
    """一条频道记录（含原始行，保证未编辑时原样回写）。"""

    _uid_sequence = itertools.count(1)

    __slots__ = (
        "uid", "pre_lines", "extinf_raw", "between_lines", "url",
        "duration", "attrs", "title",
        "test_state", "test_ms", "test_detail", "test_http", "test_seg", "test_first_segment",
        "test_cached", "test_ts", "test_url",
        "test_kbps", "test_delay", "test_stream_id", "test_variants", "test_encrypted",
        "test_prev_state", "test_prev_ts", "test_prev_cached", "test_prev_known",
        "remark",
    )

    def __init__(self, pre_lines=None, extinf_raw=None, between_lines=None,
                 url=None, duration="0", attrs=None, title="", remark=""):
        self.uid = next(M3ULiveEditorEntry._uid_sequence)
        self.pre_lines = list(pre_lines or [])
        self.between_lines = list(between_lines or [])
        self.extinf_raw = extinf_raw
        self.url = url
        self.duration = duration
        self.attrs = attrs if attrs is not None else OrderedDict()
        self.title = title if title is not None else ""
        self.test_state = M3ULE_STATUS_NONE
        self.test_ms = -1
        self.test_detail = ""
        self.test_http = -1
        self.test_seg = -1
        self.test_first_segment = ""
        self.test_cached = False
        self.test_ts = ""
        self.test_url = ""
        self.test_kbps = -1
        self.test_delay = -1
        self.test_stream_id = ""
        self.test_variants = -1
        self.test_encrypted = False
        # 「上一次测试」快照：用于「对比上次」列，判断这次相比上次是多了台还是少了台
        self.test_prev_state = ""
        self.test_prev_ts = ""
        self.test_prev_cached = False
        self.test_prev_known = False
        self.remark = remark
        if self.extinf_raw is not None and not self.attrs and self.duration == "0" and not self.title:
            self.entry_parse_from_raw()

    # -- 解析 / 生成 ----------------------------------------------------------
    def entry_parse_from_raw(self) -> None:
        if self.extinf_raw is None:
            return
        duration, attrs, title = m3ule_parse_extinf_line(self.extinf_raw)
        self.duration = duration
        self.attrs = attrs
        self.title = title

    def entry_rebuild_extinf_line(self) -> None:
        if self.extinf_raw is None and not self.attrs and not self.title:
            return
        self.extinf_raw = m3ule_format_extinf_line(self.duration, self.attrs, self.title)

    def entry_has_extinf(self) -> bool:
        return self.extinf_raw is not None

    def entry_get_attr(self, key: str) -> str:
        return self.attrs.get(key, "")

    def entry_set_attr(self, key: str, value: str) -> None:
        value = "" if value is None else str(value)
        if value == "":
            if key in self.attrs:
                del self.attrs[key]
        else:
            self.attrs[key] = value
        if self.extinf_raw is None:
            self.duration = self.duration or "0"
        self.entry_rebuild_extinf_line()

    def entry_effective_name(self) -> str:
        name = (self.title or "").strip()
        if name:
            return name
        name = (self.entry_get_attr("tvg-name") or "").strip()
        if name:
            return name
        return (self.entry_get_attr("channelID") or "").strip()

    def entry_effective_group(self) -> str:
        return (self.entry_get_attr("group-title") or "").strip()

    def entry_matches_keyword(self, keyword: str) -> bool:
        if not keyword:
            return True
        needle = keyword.lower()
        haystack = " ".join((
            self.title or "", self.entry_get_attr("tvg-name"),
            self.entry_get_attr("group-title"), self.entry_get_attr("tvg-id"),
            self.entry_get_attr("channelID"), self.entry_get_attr("tvg-chno"),
            self.url or "", self.remark or "",
        )).lower()
        return needle in haystack

    def entry_to_lines(self) -> list:
        output: list = list(self.pre_lines)
        if self.extinf_raw is not None:
            output.append(self.extinf_raw)
        output.extend(self.between_lines)
        if self.url is not None:
            output.append(self.url)
        return output

    def entry_reset_test_result(self) -> None:
        self.test_state = M3ULE_STATUS_NONE
        self.test_ms = -1
        self.test_detail = ""
        self.test_http = -1
        self.test_seg = -1
        self.test_first_segment = ""
        self.test_cached = False
        self.test_ts = ""
        self.test_url = ""
        self.test_kbps = -1
        self.test_delay = -1
        self.test_stream_id = ""
        self.test_variants = -1
        self.test_encrypted = False
        self.entry_clear_previous_result()

    def entry_snapshot_previous_result(self) -> None:
        """把当前结果存为「上一次测试」，供「对比上次」列使用（测试开始前调用）。"""
        self.test_prev_state = self.test_state or ""
        self.test_prev_ts = self.test_ts or ""
        self.test_prev_cached = bool(self.test_cached)
        self.test_prev_known = True

    def entry_clear_previous_result(self) -> None:
        self.test_prev_state = ""
        self.test_prev_ts = ""
        self.test_prev_cached = False
        self.test_prev_known = False

    def entry_delta_label(self) -> str:
        """本次相对上次的差异结论（没有上次记录时返回空串）。"""
        if not self.test_prev_known:
            return M3ULE_DELTA_NONE
        return m3ule_test_delta_label(self.test_prev_state, self.test_state)

    def entry_apply_probe_payload(self, payload: dict, cached: bool = False,
                                  checked_at: str = "") -> None:
        self.test_state = payload.get("state", M3ULE_STATUS_NONE)
        self.test_ms = m3ule_safe_int(payload.get("ms", -1), -1)
        self.test_detail = payload.get("detail", "")
        self.test_http = m3ule_safe_int(payload.get("http_status", -1), -1)
        self.test_seg = m3ule_safe_int(payload.get("segments", -1), -1)
        self.test_first_segment = payload.get("first_segment", "")
        self.test_kbps = m3ule_safe_int(payload.get("real_kbps", -1), -1)
        self.test_delay = m3ule_safe_int(payload.get("live_delay_s", -1), -1)
        self.test_stream_id = str(payload.get("stream_id") or "")
        self.test_variants = m3ule_safe_int(payload.get("variant_count", -1), -1)
        self.test_encrypted = bool(payload.get("encrypted"))
        self.test_cached = bool(cached)
        self.test_ts = ((checked_at or "").strip() if cached
                        else datetime.now().strftime("%Y-%m-%d %H:%M:%S"))
        self.test_url = m3ule_probe_cache_key(payload.get("url") or self.url or "")

    def entry_set_cached_result(self, payload: dict, checked_at: str) -> None:
        """套用持久缓存里的检测结果（标记为缓存来源 + 缓存时间）。"""
        self.entry_apply_probe_payload(payload, cached=True, checked_at=checked_at)

    def entry_test_result_is_stale(self, new_url: str = "") -> bool:
        """检测结果是否已与当前链接不匹配（链接被改过就算过期）。"""
        if not self.test_state:
            return False
        target = m3ule_probe_cache_key(new_url if new_url else (self.url or ""))
        return bool(self.test_url) and self.test_url != target

    def entry_invalidate_test_if_url_changed(self, new_url: str) -> bool:
        """链接变化时丢弃旧检测结果，避免旧状态/旧缓存指向另一条链接。"""
        if self.entry_test_result_is_stale(new_url):
            self.entry_reset_test_result()
            return True
        return False

    def entry_test_result_is_fresh(self, ttl_hours: int) -> bool:
        """当前结果是否来自缓存、且仍在有效期内（用于测试时跳过）。"""
        if not self.test_cached or not self.test_state:
            return False
        if self.entry_test_result_is_stale():
            return False
        return m3ule_probe_cache_is_fresh(self.test_ts, ttl_hours)

    def entry_to_dict(self) -> dict:
        return {
            "duration": self.duration,
            "attrs": dict(self.attrs),
            "title": self.title,
            "url": self.url or "",
            "remark": self.remark or "",
        }


# ----------------------------------------------------------------------------
# 数据模型：整个文档
# ----------------------------------------------------------------------------

class M3ULiveEditorDocument:
    """m3u / m3u8 文档对象，负责解析、序列化、增删改与统计。"""

    def __init__(self):
        self.header_lines: list = ["#EXTM3U"]
        self.entries: list = []
        self.trailer_lines: list = []
        self.path: str = ""
        self.encoding: str = "utf-8"
        self.newline: str = "\r\n"
        self.trailing_newline: bool = True
        self.modified: bool = False

    # -- 编码 ----------------------------------------------------------------
    @staticmethod
    def doc_detect_newline(text: str) -> str:
        if "\r\n" in text:
            return "\r\n"
        if "\r" in text and "\n" not in text:
            return "\r"
        return "\n"

    @staticmethod
    def doc_decode_bytes(data: bytes):
        if data.startswith(b"\xef\xbb\xbf"):
            return data.decode("utf-8-sig", errors="replace"), "utf-8-sig"
        if data.startswith(b"\xff\xfe") or data.startswith(b"\xfe\xff"):
            try:
                return data.decode("utf-16", errors="replace"), "utf-16"
            except UnicodeDecodeError:
                pass
        for encoding in ("utf-8", "gbk", "gb18030", "big5", "latin-1"):
            try:
                return data.decode(encoding), encoding
            except (UnicodeDecodeError, LookupError):
                continue
        return data.decode("utf-8", errors="replace"), "utf-8"

    def doc_encode_text(self, text: str) -> bytes:
        encoding = self.encoding or "utf-8"
        try:
            return text.encode(encoding)
        except (UnicodeEncodeError, LookupError):
            return text.encode("utf-8")

    # -- 解析 ----------------------------------------------------------------
    def doc_clear(self) -> None:
        self.header_lines = ["#EXTM3U"]
        self.entries = []
        self.trailer_lines = []
        self.path = ""
        self.encoding = "utf-8"
        self.newline = "\r\n"
        self.trailing_newline = True
        self.modified = False

    def doc_parse_text(self, text: str) -> None:
        self.newline = self.doc_detect_newline(text)
        normalized = text.replace("\r\n", "\n").replace("\r", "\n")
        self.trailing_newline = normalized.endswith("\n")
        if self.trailing_newline:
            normalized = normalized[:-1]
        lines = normalized.split("\n")
        if not lines:
            lines = []

        self.header_lines = []
        self.entries = []
        self.trailer_lines = []
        self.modified = False

        start = 0
        if lines and lines[0].strip().upper().startswith("#EXTM3U"):
            self.header_lines.append(lines[0])
            start = 1

        pending_pre: list = []
        current_extinf = None
        current_between: list = []

        for index in range(start, len(lines)):
            line = lines[index]
            stripped = line.strip()
            if stripped[:7].upper() == "#EXTINF":
                if current_extinf is not None:
                    self.entries.append(M3ULiveEditorEntry(
                        pre_lines=pending_pre, extinf_raw=current_extinf,
                        between_lines=current_between, url=None))
                    pending_pre = []
                    current_between = []
                current_extinf = line
            elif m3ule_is_url_line(line):
                self.entries.append(M3ULiveEditorEntry(
                    pre_lines=pending_pre, extinf_raw=current_extinf,
                    between_lines=current_between, url=line))
                pending_pre = []
                current_extinf = None
                current_between = []
            else:
                if current_extinf is not None:
                    current_between.append(line)
                else:
                    pending_pre.append(line)

        if current_extinf is not None:
            self.entries.append(M3ULiveEditorEntry(
                pre_lines=pending_pre, extinf_raw=current_extinf,
                between_lines=current_between, url=None))
            pending_pre = []
        self.trailer_lines = pending_pre

    def doc_load_from_path(self, path: str, progress=None) -> str:
        with open(path, "rb") as handle:
            data = handle.read()
        if progress:
            progress(60, "正在解析内容…")
        text, encoding = self.doc_decode_bytes(data)
        self.doc_parse_text(text)
        self.encoding = encoding
        self.path = path
        self.modified = False
        if progress:
            progress(100, f"已加载 {len(self.entries)} 条频道")
        return encoding

    # -- 序列化 --------------------------------------------------------------
    def doc_serialize_text(self, progress=None) -> str:
        blocks: list = list(self.header_lines)
        total = max(1, len(self.entries))
        for position, entry in enumerate(self.entries):
            blocks.extend(entry.entry_to_lines())
            if progress and position % 500 == 0:
                progress(int(position * 100 / total), f"正在生成 {position}/{total}")
        blocks.extend(self.trailer_lines)
        text = self.newline.join(blocks)
        if self.trailing_newline:
            text += self.newline
        if progress:
            progress(100, "内容生成完成")
        return text

    def doc_save_to_path(self, path: str, progress=None) -> None:
        text = self.doc_serialize_text(progress=progress)
        if progress:
            progress(100, "正在写入文件…")
        with open(path, "wb") as handle:
            handle.write(self.doc_encode_text(text))
        self.path = path
        self.modified = False

    # -- 结构操作 ------------------------------------------------------------
    def doc_insert_entries(self, entries: list, at_index=None) -> None:
        if at_index is None or at_index < 0 or at_index > len(self.entries):
            at_index = len(self.entries)
        for offset, entry in enumerate(entries):
            self.entries.insert(at_index + offset, entry)
        self.modified = True

    def doc_remove_indices(self, indices) -> int:
        valid = sorted({i for i in indices if 0 <= i < len(self.entries)}, reverse=True)
        for index in valid:
            del self.entries[index]
        if valid:
            self.modified = True
        return len(valid)

    def doc_remove_uids(self, uids) -> int:
        target = set(uids)
        if not target:
            return 0
        before = len(self.entries)
        self.entries = [entry for entry in self.entries if entry.uid not in target]
        removed = before - len(self.entries)
        if removed:
            self.modified = True
        return removed

    def doc_move_entry(self, from_index: int, to_index: int) -> bool:
        if not (0 <= from_index < len(self.entries)):
            return False
        to_index = max(0, min(to_index, len(self.entries) - 1))
        if from_index == to_index:
            return False
        entry = self.entries.pop(from_index)
        self.entries.insert(to_index, entry)
        self.modified = True
        return True

    def doc_deduplicate(self, ignore_case: bool = True) -> int:
        """按链接去重（保留第一条）。空链接条目不参与去重，也不会被删除。"""
        seen: set = set()
        kept: list = []
        removed = 0
        for entry in self.entries:
            key = (entry.url or "").strip()
            if ignore_case:
                key = key.lower()
            if key and key in seen:
                removed += 1
                continue
            if key:
                seen.add(key)
            kept.append(entry)
        if removed:
            self.entries = kept
            self.modified = True
        return removed

    def doc_statistics(self) -> dict:
        groups: "OrderedDict[str, int]" = OrderedDict()
        id_values: set = set()
        url_values: set = set()
        for entry in self.entries:
            group = entry.entry_effective_group() or "(未分组)"
            groups[group] = groups.get(group, 0) + 1
            tvg_id = entry.entry_get_attr("tvg-id")
            if tvg_id:
                id_values.add(tvg_id)
            if entry.url:
                url_values.add(entry.url.strip())
        return {
            "entries": len(self.entries),
            "groups": len(groups),
            "group_map": dict(groups),
            "unique_ids": len(id_values),
            "unique_urls": len(url_values),
            "header": self.header_lines[0] if self.header_lines else "",
        }

    def doc_group_names(self) -> list:
        names: list = []
        for entry in self.entries:
            group = entry.entry_effective_group()
            if group and group not in names:
                names.append(group)
        return names

    def doc_find_entry_by_uid(self, uid: int):
        for entry in self.entries:
            if entry.uid == uid:
                return entry
        return None

    def doc_index_of_uid(self, uid: int) -> int:
        for index, entry in enumerate(self.entries):
            if entry.uid == uid:
                return index
        return -1


# ----------------------------------------------------------------------------
# 链接探测引擎（多线程安全，纯函数式）
# ----------------------------------------------------------------------------
try:  # 关闭不可信证书产生的告警刷屏
    import urllib3  # type: ignore
    urllib3.disable_warnings()  # type: ignore
except Exception:  # pragma: no cover
    pass

_M3ULE_REQUESTS_MODULE = None
_M3ULE_REQUESTS_TRIED = False


def m3ule_get_requests_module():
    global _M3ULE_REQUESTS_MODULE, _M3ULE_REQUESTS_TRIED
    if _M3ULE_REQUESTS_TRIED:
        return _M3ULE_REQUESTS_MODULE
    _M3ULE_REQUESTS_TRIED = True
    try:
        import requests  # type: ignore
        _M3ULE_REQUESTS_MODULE = requests
    except Exception:
        _M3ULE_REQUESTS_MODULE = None
    return _M3ULE_REQUESTS_MODULE


def m3ule_probe_result_template(url: str) -> dict:
    return {
        "url": url,
        "state": M3ULE_STATUS_NONE,
        "level": "fail",
        "ok": False,
        "has_program": False,
        "http_status": -1,
        "ms": -1,
        "kind": "unknown",
        "content_type": "",
        "segments": -1,
        "detail": "",
        "first_segment": "",
        "variant_url": "",
        "error": "",
        # 流元信息（由 m3u8 清单解出，用于判断“是否真的在直播”与“这背后是哪个台”）
        "live_delay_s": -1,
        "real_kbps": -1,
        "variant_count": -1,
        "stream_id": "",
        "stream_fingerprint": "",
        "encrypted": False,
        "target_duration": 0,
    }


def m3ule_probe_new_session(ignore_ssl: bool = True):
    requests = m3ule_get_requests_module()
    if requests is None:
        return None
    session = requests.Session()
    session.verify = not ignore_ssl
    return session


def m3ule_probe_http_get(session, url: str, timeout: float, headers: dict,
                         proxies, limit: int, range_header: str = "", cancel_check=None):
    """发起 GET 请求并最多读取 limit 字节，返回 (status, content_type, data, final_url)。"""
    if cancel_check and cancel_check():
        return -1, "", b"", url
    request_headers = dict(headers)
    if range_header:
        request_headers["Range"] = range_header
    response = session.get(
        url, headers=request_headers, timeout=(timeout, timeout),
        proxies=proxies, stream=True, allow_redirects=True,
    )
    status = response.status_code
    content_type = response.headers.get("Content-Type", "") or ""
    final_url = response.url
    data = bytearray()
    try:
        for chunk in response.iter_content(16384):
            if not chunk:
                continue
            data.extend(chunk)
            if len(data) >= limit:
                break
            if cancel_check and cancel_check():
                break
    finally:
        response.close()
    return status, content_type, bytes(data), final_url


def m3ule_probe_looks_like_playlist(url: str, content_type: str, data: bytes) -> bool:
    lowered_type = (content_type or "").lower()
    if "mpegurl" in lowered_type:
        return True
    path = urllib.parse.urlsplit(url).path.lower()
    if path.endswith(".m3u8") or path.endswith(".m3u"):
        return True
    head = data[:16384]
    return b"#EXTM3U" in head


def m3ule_probe_parse_playlist(text: str) -> dict:
    """解析 m3u8 播放列表，返回 variants / segments / 元信息。

    除结构外还尽力抽取可用的“流元信息”：
      · target_duration    每片时长
      · media_sequence     全局段序号（FonsView 这类服务里等价于运行计数）
      · date_times         每个分片的 UTC 起播时刻（→ 可算直播延迟）
      · segment_sizes      #EXTINF 第 2 字段的字节数（→ 可算真实码率）
      · encrypted          是否存在 #EXT-X-KEY
      · media_titles       #EXT-X-MEDIA 的 NAME / #EXTINF 标题（少数源会带）
    """
    variants: list = []
    segments: list = []
    titles: list = []
    date_times: list = []
    segment_sizes: list = []
    media_names: list = []
    title_hint = ""
    is_master = False
    target_duration = 0
    media_sequence = -1
    encrypted = False
    pending_size = -1
    lines = text.replace("\r\n", "\n").splitlines()
    index = 0
    total = len(lines)
    while index < total:
        line = lines[index].strip()
        if line.startswith("#EXT-X-STREAM-INF"):
            is_master = True
            probe = index + 1
            while probe < total and (not lines[probe].strip() or lines[probe].strip().startswith("#")):
                probe += 1
            if probe < total:
                variants.append(lines[probe].strip())
                index = probe
        elif line.startswith("#EXT-X-MEDIA-SEQUENCE"):
            match = re.search(r":\s*(\d+)", line)
            if match:
                media_sequence = int(match.group(1))
        elif line.startswith("#EXT-X-MEDIA:") or line.startswith("#EXT-X-MEDIA "):
            match = re.search(r'NAME\s*=\s*"([^"]*)"', line)
            if match:
                media_names.append(match.group(1))
                if not title_hint:
                    title_hint = match.group(1)
        elif line.startswith("#EXT-X-TARGETDURATION"):
            match = re.search(r":\s*([\d.]+)", line)
            if match:
                target_duration = int(float(match.group(1)))
        elif line.startswith("#EXT-X-PROGRAM-DATE-TIME"):
            match = re.search(r":\s*(\S+)", line)
            if match:
                date_times.append(match.group(1))
        elif line.startswith("#EXT-X-KEY"):
            if "METHOD=NONE" not in line.upper():
                encrypted = True
        elif line.startswith("#EXTINF"):
            _, _, title = m3ule_parse_extinf_line(line)
            title = (title or "").strip()
            if title:
                titles.append(title)
                title_hint = title_hint or title
            # #EXTINF:<时长>,<可选的字节数>（部分服务端会在这里给出分片大小）
            tail = line.split(",", 1)[1].strip() if "," in line else ""
            pending_size = int(tail) if tail.isdigit() else -1
            probe = index + 1
            while probe < total and (not lines[probe].strip() or lines[probe].strip().startswith("#")):
                probe += 1
            if probe < total:
                segments.append(lines[probe].strip())
                segment_sizes.append(pending_size)
                index = probe
        elif line and not line.startswith("#"):
            if not is_master:
                segments.append(line)
                segment_sizes.append(pending_size)
        index += 1
    if variants:
        is_master = True
    return {
        "is_master": is_master,
        "variants": variants,
        "segments": segments,
        "title_hint": title_hint,
        "media_titles": titles,
        "media_names": media_names,
        "target_duration": target_duration,
        "media_sequence": media_sequence,
        "date_times": date_times,
        "segment_sizes": [s for s in segment_sizes if s and s > 0],
        "encrypted": encrypted,
    }


def m3ule_probe_stream_fingerprint(segment_url: str) -> dict:
    """从分片地址推出“频道指纹”，用于判断同一编号背后的台是否被换过。

    优先识别 FonsView 系列（`/LIVES/<时间戳>_<码率号><频道流ID>_<段号>.ts`），
    可直接得到服务端的频道内部流 ID；其它服务端退化为“把数字段归一化后的
    地址模板”，同样可用于比较两个时刻的分片地址是否指向同一条流。
    """
    info = {"stream_id": "", "seg_id": "", "fingerprint": "", "pattern": ""}
    text = (segment_url or "").strip()
    if not text:
        return info
    try:
        path = urllib.parse.urlsplit(text).path
    except ValueError:
        path = text
    fonsview = re.search(r"/LIVES/(\d+)_(\d{3})(\d+)_(\d+)\.ts$", path)
    if fonsview:
        info["stream_id"] = fonsview.group(3)
        info["seg_id"] = fonsview.group(4)
        info["pattern"] = "fonsview"
        info["fingerprint"] = path[:fonsview.start(1)] + f"<epoch>_{fonsview.group(2)}" \
            + fonsview.group(3) + "_<seq>.ts"
        return info
    directory = path.rsplit("/", 1)[0] if "/" in path else ""
    name = path.rsplit("/", 1)[-1]
    normalized = re.sub(r"\d+", "#", name)
    info["fingerprint"] = f"{directory}/{normalized}"
    info["pattern"] = "generic"
    return info


def m3ule_probe_playlist_metadata(playlist: dict) -> dict:
    """把解析出的清单元信息折算成可展示的结论：直播延迟、真实码率等。"""
    meta = {
        "live_delay_s": -1,
        "real_kbps": -1,
        "target_duration": m3ule_safe_int(playlist.get("target_duration"), 0),
        "media_sequence": m3ule_safe_int(playlist.get("media_sequence"), -1),
        "encrypted": bool(playlist.get("encrypted")),
        "date_time_count": len(playlist.get("date_times") or []),
        "stream_id": "",
        "stream_fingerprint": "",
    }
    sizes = playlist.get("segment_sizes") or []
    if sizes:
        average = sum(sizes) / len(sizes)
        duration = meta["target_duration"] or 10
        if duration > 0 and average > 0:
            meta["real_kbps"] = int(round(average * 8 / duration / 1000))
    dates = playlist.get("date_times") or []
    if dates:
        delay = m3ule_probe_live_delay_seconds(dates[-1])
        if delay is not None:
            meta["live_delay_s"] = int(round(delay))
    segments = playlist.get("segments") or []
    if segments:
        fingerprint = m3ule_probe_stream_fingerprint(segments[0])
        meta["stream_id"] = fingerprint.get("stream_id", "")
        meta["stream_fingerprint"] = fingerprint.get("fingerprint", "")
    return meta


def m3ule_probe_live_delay_seconds(timestamp: str):
    """由 #EXT-X-PROGRAM-DATE-TIME 计算“该段起播时刻距现在多少秒”。"""
    text = (timestamp or "").strip()
    if not text:
        return None
    for pattern in ("%Y-%m-%dT%H:%M:%S.%fZ", "%Y-%m-%dT%H:%M:%SZ", "%Y-%m-%dT%H:%M:%S"):
        try:
            moment = datetime.strptime(text, pattern)
        except ValueError:
            continue
        return (datetime.utcnow() - moment).total_seconds()
    return None


def m3ule_probe_analyze_stream(session, url: str, timeout: float, headers: dict,
                               proxies, deep: bool, ignore_ssl: bool,
                               depth: int = 0, cancel_check=None) -> dict:
    """递归分析一个流地址，返回探测结果字典。"""
    result = m3ule_probe_result_template(url)
    if depth > 3:
        result["detail"] = "重定向层级过深"
        result["error"] = "too many redirects"
        return result

    guess_playlist = m3ule_probe_looks_like_playlist(url, "", b"")
    limit = M3ULE_PROBE_MAX_PLAYLIST_BYTES if guess_playlist else M3ULE_PROBE_MAX_MEDIA_BYTES
    range_header = "" if guess_playlist else "bytes=0-%d" % (M3ULE_PROBE_MAX_MEDIA_BYTES - 1)

    status, content_type, data, final_url = m3ule_probe_http_get(
        session, url, timeout, headers, proxies, limit, range_header, cancel_check)
    if status < 0:
        result["state"] = M3ULE_STATUS_CANCEL
        result["detail"] = "已取消"
        return result

    result["http_status"] = status
    result["content_type"] = content_type or ""
    if status not in (200, 206):
        result["state"] = M3ULE_STATUS_FAIL
        result["level"] = "fail"
        result["detail"] = f"HTTP {status}"
        result["error"] = f"HTTP {status}"
        return result

    is_playlist = m3ule_probe_looks_like_playlist(final_url, content_type, data)
    if is_playlist:
        result["kind"] = "hls"
        text = data.decode("utf-8", errors="replace")
        if "#EXTM3U" not in text:
            result["state"] = M3ULE_STATUS_PARTIAL
            result["level"] = "partial"
            result["ok"] = True
            result["detail"] = "返回内容非标准 m3u8"
            return result
        playlist = m3ule_probe_parse_playlist(text)
        if playlist["is_master"] and playlist["variants"]:
            variant_url = urllib.parse.urljoin(final_url, playlist["variants"][0])
            result["variant_url"] = variant_url
            result["variant_count"] = len(playlist["variants"])
            sub = m3ule_probe_analyze_stream(
                session, variant_url, timeout, headers, proxies, deep,
                ignore_ssl, depth + 1, cancel_check)
            result["state"] = sub["state"]
            result["level"] = sub["level"]
            result["ok"] = sub["ok"]
            result["has_program"] = sub["has_program"]
            result["http_status"] = sub["http_status"]
            result["content_type"] = sub["content_type"]
            result["segments"] = sub["segments"]
            result["first_segment"] = sub["first_segment"]
            result["error"] = sub["error"]
            result["detail"] = ("主列表→" + sub["detail"]) if sub["detail"] else "主列表可用"
            # 码率档位数来自主清单，其余元信息来自子清单
            for key in ("live_delay_s", "real_kbps", "stream_id", "stream_fingerprint",
                        "encrypted", "target_duration"):
                result[key] = sub.get(key, result[key])
            return result

        metadata = m3ule_probe_playlist_metadata(playlist)
        result["live_delay_s"] = metadata["live_delay_s"]
        result["real_kbps"] = metadata["real_kbps"]
        result["stream_id"] = metadata["stream_id"]
        result["stream_fingerprint"] = metadata["stream_fingerprint"]
        result["encrypted"] = metadata["encrypted"]
        result["target_duration"] = metadata["target_duration"]
        if result["variant_count"] < 0:
            result["variant_count"] = 1
        segments = [s for s in playlist["segments"] if s and not s.startswith("#")]
        result["segments"] = len(segments)
        title_hint = playlist.get("title_hint", "")
        if not segments:
            result["state"] = M3ULE_STATUS_PARTIAL
            result["level"] = "partial"
            result["ok"] = True
            result["detail"] = "播放列表有效但未发现分片"
            return result
        first_segment = urllib.parse.urljoin(final_url, segments[0])
        result["first_segment"] = first_segment
        if not deep:
            result["state"] = M3ULE_STATUS_OK
            result["level"] = "ok"
            result["ok"] = True
            result["detail"] = f"播放列表有效 · {len(segments)} 分片"
            if title_hint:
                result["detail"] += f" · 标题:{title_hint[:24]}"
            result["detail"] += m3ule_probe_metadata_summary(result)
            return result

        seg_status, seg_type, seg_data, _ = m3ule_probe_http_get(
            session, first_segment, timeout, headers, proxies,
            M3ULE_PROBE_MAX_SEGMENT_BYTES, "bytes=0-%d" % (M3ULE_PROBE_MAX_SEGMENT_BYTES - 1),
            cancel_check)
        if seg_status in (200, 206) and len(seg_data) > 0:
            result["state"] = M3ULE_STATUS_OK
            result["level"] = "ok"
            result["ok"] = True
            result["has_program"] = True
            result["detail"] = f"有节目 · {len(segments)} 分片 · 首片 {len(seg_data)}B"
        elif seg_status < 0:
            result["state"] = M3ULE_STATUS_CANCEL
            result["ok"] = True
            result["detail"] = "已取消"
            return result
        else:
            result["state"] = M3ULE_STATUS_PARTIAL
            result["level"] = "partial"
            result["ok"] = True
            result["has_program"] = False
            result["detail"] = f"播放列表有效但首片无效 (HTTP {seg_status})"
        if title_hint and result["state"] == M3ULE_STATUS_OK:
            result["detail"] += f" · 标题:{title_hint[:20]}"
        result["detail"] += m3ule_probe_metadata_summary(result)
        return result

    # 非 m3u8：直接媒体流
    result["kind"] = "media"
    received = len(data)
    if received > 0:
        result["state"] = M3ULE_STATUS_OK
        result["level"] = "ok"
        result["ok"] = True
        result["has_program"] = True
        result["detail"] = f"媒体流可用 · {content_type or '未知类型'} · {received}B"
    else:
        result["state"] = M3ULE_STATUS_FAIL
        result["level"] = "fail"
        result["detail"] = "无数据返回"
        result["error"] = "empty body"
    return result


def m3ule_probe_stream_url(url: str, timeout: float = 8.0, retries: int = 1,
                           deep: bool = True, user_agent: str = "",
                           proxy: str = "", ignore_ssl: bool = True,
                           cancel_check=None) -> dict:
    """探测单个直播链接是否可播放，返回结果字典（含 state / ms / detail）。"""
    result = m3ule_probe_result_template(url)
    requests = m3ule_get_requests_module()
    if requests is None:
        result["state"] = M3ULE_STATUS_ERROR
        result["detail"] = "缺少 requests 依赖"
        result["error"] = "requests not installed"
        return result
    if not (url or "").strip():
        result["state"] = M3ULE_STATUS_FAIL
        result["detail"] = "链接为空"
        result["error"] = "empty url"
        return result

    headers = {
        "User-Agent": (user_agent or M3ULE_DEFAULT_USER_AGENT),
        "Accept": "*/*",
        "Accept-Language": "zh-CN,zh;q=0.9",
        "Connection": "close",
    }
    proxies = None
    if proxy.strip():
        proxies = {"http": proxy.strip(), "https": proxy.strip()}

    started = time.time()
    attempts = max(1, int(retries) + 1)
    last_error = ""
    for attempt in range(attempts):
        if cancel_check and cancel_check():
            result["state"] = M3ULE_STATUS_CANCEL
            result["detail"] = "已取消"
            break
        session = None
        try:
            session = m3ule_probe_new_session(ignore_ssl)
            if session is None:
                result["state"] = M3ULE_STATUS_ERROR
                result["detail"] = "无法创建会话"
                break
            analyzed = m3ule_probe_analyze_stream(
                session, url, timeout, headers, proxies, deep, ignore_ssl,
                0, cancel_check)
            result.update(analyzed)
            result["ms"] = int((time.time() - started) * 1000)
            if result["state"] in (M3ULE_STATUS_OK, M3ULE_STATUS_PARTIAL, M3ULE_STATUS_CANCEL):
                return result
            last_error = result.get("error") or result.get("detail") or ""
        except requests.exceptions.Timeout:
            last_error = "连接或读取超时"
            result["state"] = M3ULE_STATUS_TIMEOUT
            result["detail"] = last_error
        except requests.exceptions.SSLError as exc:
            last_error = f"SSL 错误: {exc}"
            result["state"] = M3ULE_STATUS_ERROR
            result["detail"] = last_error
            ignore_ssl = True
        except requests.exceptions.TooManyRedirects as exc:
            last_error = f"重定向过多: {exc}"
            result["state"] = M3ULE_STATUS_FAIL
            result["detail"] = last_error
        except requests.exceptions.ConnectionError as exc:
            last_error = f"无法连接: {m3ule_probe_short_error(exc)}"
            result["state"] = M3ULE_STATUS_FAIL
            result["detail"] = last_error
        except requests.exceptions.InvalidURL as exc:
            last_error = f"链接格式错误: {exc}"
            result["state"] = M3ULE_STATUS_ERROR
            result["detail"] = last_error
            break
        except Exception as exc:  # noqa: BLE001 - 兜底，保证不中断批处理
            last_error = f"{type(exc).__name__}: {m3ule_probe_short_error(exc)}"
            result["state"] = M3ULE_STATUS_ERROR
            result["detail"] = last_error
        finally:
            if session is not None:
                try:
                    session.close()
                except Exception:
                    pass
        if attempt < attempts - 1:
            time.sleep(min(0.6, 0.15 * (attempt + 1)))
    result["ms"] = int((time.time() - started) * 1000)
    if result["state"] in (M3ULE_STATUS_NONE, ""):
        result["state"] = M3ULE_STATUS_FAIL
    if not result["detail"]:
        result["detail"] = last_error or "探测失败"
    result["error"] = last_error
    return result


def m3ule_probe_metadata_summary(result: dict) -> str:
    """把流元信息压成一段简短后缀，追加到测试详情里。"""
    parts = []
    kbps = m3ule_safe_int(result.get("real_kbps"), -1)
    if kbps > 0:
        parts.append(f"{kbps}kbps")
    delay = m3ule_safe_int(result.get("live_delay_s"), -1)
    if delay >= 0:
        parts.append(f"延迟{delay}s")
    stream_id = str(result.get("stream_id") or "").strip()
    if stream_id:
        parts.append(f"流ID{stream_id}")
    variants = m3ule_safe_int(result.get("variant_count"), -1)
    if variants > 1:
        parts.append(f"{variants}档")
    if result.get("encrypted"):
        parts.append("加密")
    return (" · " + " · ".join(parts)) if parts else ""


def m3ule_probe_short_error(exc) -> str:
    text = str(exc).strip().splitlines()[0] if str(exc).strip() else type(exc).__name__
    return text[:120]


def m3ule_probe_summarize(results: list) -> dict:
    summary = {
        "total": len(results), "ok": 0, "partial": 0,
        "fail": 0, "timeout": 0, "error": 0, "cancel": 0,
        "has_program": 0, "elapsed_ms": 0,
    }
    for item in results:
        state = item.get("state", "")
        if state == M3ULE_STATUS_OK:
            summary["ok"] += 1
        elif state == M3ULE_STATUS_PARTIAL:
            summary["partial"] += 1
        elif state == M3ULE_STATUS_TIMEOUT:
            summary["timeout"] += 1
        elif state == M3ULE_STATUS_ERROR:
            summary["error"] += 1
        elif state == M3ULE_STATUS_CANCEL:
            summary["cancel"] += 1
        else:
            summary["fail"] += 1
        if item.get("has_program"):
            summary["has_program"] += 1
    return summary


# ----------------------------------------------------------------------------
# HTML5 播放：本机中转服务 + 播放页
# ----------------------------------------------------------------------------
M3ULE_RELAY_HOST = "127.0.0.1"
M3ULE_RELAY_PLAYLIST_LIMIT = 2 * 1024 * 1024
M3ULE_HLSJS_LOCAL_NAME = "hls.min.js"
M3ULE_HLSJS_CDN_LIST = (
    "https://cdn.jsdelivr.net/npm/hls.js@1.5.20/dist/hls.min.js",
    "https://unpkg.com/hls.js@1/dist/hls.min.js",
    "https://cdnjs.cloudflare.com/ajax/libs/hls.js/1.5.20/hls.min.js",
)

# 播放页模板：__SRC_JSON__ / __TITLE__ / __TITLE_JSON__ / __AUTOPLAY_JS__ / __CDN_JSON__ / __UA_JSON__
M3ULE_HTML5_PLAYER_PAGE = """<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>__TITLE__</title>
<style>
 html,body{margin:0;height:100%;background:#0f1012;color:#e8eaed;
   font:13px/1.5 "Microsoft YaHei",system-ui,-apple-system,sans-serif;overflow:hidden}
 #wrap{display:flex;flex-direction:column;height:100%}
 #bar{display:flex;align-items:center;gap:8px;padding:6px 10px;background:#1c1d20;border-bottom:1px solid #2f3033}
 #bar b{white-space:nowrap;max-width:32%;overflow:hidden;text-overflow:ellipsis}
 #bar .u{color:#9aa0a6;flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:12px}
 button{background:#3c4043;color:#e8eaed;border:1px solid #5f6368;border-radius:3px;padding:3px 9px;cursor:pointer;font-size:12px}
 button:hover{background:#4a4d51}
 #stage{position:relative;flex:1;min-height:0;background:#000}
 video{width:100%;height:100%;display:block;background:#000}
 #overlay{position:absolute;inset:0;display:flex;flex-direction:column;align-items:center;justify-content:center;
   gap:6px;background:rgba(0,0,0,.6);text-align:center;padding:18px}
 #overlay.hide{display:none}
 #msg{font-size:14px}
 #sub{color:#9aa0a6;font-size:12px;max-width:80%}
 .err{color:#f28b82}
 #stat{padding:4px 10px;background:#1c1d20;border-top:1px solid #2f3033;color:#9aa0a6;
   display:flex;gap:16px;flex-wrap:wrap;font-size:12px}
</style>
</head>
<body>
<div id="wrap">
  <div id="bar">
    <b id="name">__TITLE__</b>
    <span class="u" id="url">__URLTEXT__</span>
    <button onclick="reload()">重新加载</button>
    <button onclick="copyUrl()">复制地址</button>
    <button onclick="toggleMute()" id="muteBtn">静音</button>
  </div>
  <div id="stage">
    <video id="v" controls autoplay playsinline></video>
    <div id="overlay"><div id="msg">正在准备播放…</div><div id="sub"></div></div>
  </div>
  <div id="stat">
    <span id="s1">引擎: 检测中…</span>
    <span id="s2">分辨率: —</span>
    <span id="s3">分片: —</span>
    <span id="s4">错误: 0</span>
  </div>
</div>
<script>
(function(){
  var SRC = __SRC_JSON__;
  var RAW = __RAW_JSON__;
  var NAME = __TITLE_JSON__;
  var AUTOPLAY = __AUTOPLAY_JS__;
  var CDN = __CDN_JSON__;
  var v = document.getElementById('v');
  var ov = document.getElementById('overlay');
  var msg = document.getElementById('msg');
  var sub = document.getElementById('sub');
  var hls = null, errCount = 0;

  window.__m3ule_state = 'LOADING';
  window.__m3ule_detail = '';
  window.__m3ule_media = 'init';
  window.onerror = function(m, s, l){ setState('ERR', 'script error: ' + m + ' @line ' + l); return false; };
  window.addEventListener('unhandledrejection', function(e){
    setState('ERR', 'unhandled promise: ' + (e && e.reason ? e.reason : ''));
  });
  function setState(s, d){ window.__m3ule_state = s; window.__m3ule_detail = d || ''; }
  function stat(id, t){ var el = document.getElementById(id); if (el) el.textContent = t; }
  function fail(text, detail){
    ov.classList.remove('hide'); msg.className = 'err'; msg.textContent = text;
    sub.textContent = detail || ''; setState('ERR', text + ' | ' + (detail || ''));
  }
  function ok(text){
    ov.classList.add('hide'); msg.className = ''; setState('OK', text);
  }
  function loadScript(list, i, done){
    if (i >= list.length){ done(false); return; }
    var s = document.createElement('script');
    s.src = list[i];
    s.onload = function(){ done(true); };
    s.onerror = function(){ loadScript(list, i + 1, done); };
    document.head.appendChild(s);
  }
  function tryAutoplay(){
    if (!AUTOPLAY) return;
    var p = v.play();
    if (p && p.catch) p.catch(function(){ stat('s1', '引擎: 需点击播放'); });
  }
  function nativePlay(why){
    window.__m3ule_media = 'native';
    stat('s1', '引擎: 原生 <video>');
    v.src = SRC;
    v.onerror = function(){
      fail('浏览器无法直接播放该格式', why + '；该流可能是 MPEG-TS/加密 HLS，请改用“用播放器打开”(VLC)');
    };
    v.load(); tryAutoplay();
    setTimeout(function(){
      if (!v.videoWidth && window.__m3ule_state !== 'OK'){
        fail('无法播放该链接', (why || '') + '；可回到主界面用“用播放器打开”(VLC) 复核');
      }
    }, 7000);
  }
  window.reload = function(){
    if (hls){ hls.stopLoad(); hls.startLoad(); } else { v.load(); tryAutoplay(); }
  };
  window.copyUrl = function(){
    var text = RAW || SRC;
    if (navigator.clipboard && navigator.clipboard.writeText){ navigator.clipboard.writeText(text); }
  };
  window.toggleMute = function(){
    v.muted = !v.muted;
    document.getElementById('muteBtn').textContent = v.muted ? '取消静音' : '静音';
  };
  window.__m3ule_switch_native = function(why){ nativePlay(why || '由宿主程序切换到原生播放'); };
  window.__m3ule_engine_info = function(){
    return JSON.stringify({
      state: window.__m3ule_state, media: window.__m3ule_media,
      hls: (window.Hls ? Hls.version : 'none'),
      mse: (typeof MediaSource !== 'undefined'),
      readyState: v.readyState, videoWidth: v.videoWidth,
      src: v.currentSrc || v.src || ''
    });
  };
  v.addEventListener('loadedmetadata', function(){ stat('s2', v.videoWidth + 'x' + v.videoHeight); });
  v.addEventListener('playing', function(){ ov.classList.add('hide'); if (window.__m3ule_state !== 'OK') setState('OK', '正在播放'); });
  v.addEventListener('error', function(){ if (window.__m3ule_state !== 'OK') fail('播放失败', '浏览器媒体元素报错'); });

  loadScript(['/hls.js'].concat(CDN), 0, function(loaded){
    if (!loaded || !window.Hls){
      nativePlay('未能加载 hls.js（离线环境缺少本地 hls.min.js）');
      return;
    }
    stat('s1', '引擎: hls.js ' + Hls.version);
    if (!Hls.isSupported()){ nativePlay('当前内核不支持 MSE'); return; }
    hls = new Hls({ lowLatencyMode: true, enableWorker: false, manifestLoadingMaxRetry: 3,
                    levelLoadingMaxRetry: 3, fragLoadingMaxRetry: 3, liveSyncDurationCount: 3 });
    setState('LOADING', 'hls.js 已加载，正在取清单');
    hls.loadSource(SRC);
    hls.attachMedia(v);
    hls.on(Hls.Events.MEDIA_ATTACHED, function(){
      window.__m3ule_media = 'attached';
      stat('s2', '媒体已连接');
      setState('LOADING', '媒体已连接，等待清单');
    });
    // 看护：若内嵌内核迟迟无法初始化媒体管线（缺少解码器/媒体后端），
    // 改为原生 <video> 并给出明确提示，避免界面一直“转圈”。
    setTimeout(function(){
      if (window.__m3ule_state === 'LOADING' && window.__m3ule_media === 'init'){
        nativePlay('内嵌内核未能初始化媒体播放器（可能缺少 H.264/AAC 解码支持）');
      }
    }, 6000);
    hls.on(Hls.Events.MANIFEST_PARSED, function(e, d){
      var levels = (d && d.levels) ? d.levels.length : 0;
      ok('清单已解析 · ' + levels + ' 个清晰度');
      stat('s3', levels + ' 个清晰度');
      tryAutoplay();
    });
    hls.on(Hls.Events.LEVEL_LOADED, function(e, d){
      if (d && d.details && d.details.fragments){ stat('s3', d.details.fragments.length + ' 分片'); }
    });
    hls.on(Hls.Events.ERROR, function(e, d){
      stat('s4', '错误 ' + (errCount + 1));
      if (!d || !d.fatal){
        setState('LOADING', '非致命错误: ' + (d ? d.details : '?'));
        return;
      }
      errCount++;
      if (d.type === 'networkError'){ fail('网络错误', d.details + '（链接可能已失效或被限制）'); }
      else if (d.type === 'mediaError'){ fail('解码错误', d.details + '（当前内核可能缺少 H.264/AAC 解码支持，建议用 VLC）'); }
      else { fail('播放失败', d.details); }
    });
  });
})();
</script>
</body>
</html>
"""


class M3ULiveEditorStreamRelayServer:
    """本机回环中转服务（127.0.0.1 随机端口）。

    作用：把任意外部直播流经由本机转发后再交给播放器，从而一次性解决
      ① 跨域（hls.js 通过 XHR 取清单/分片时的 CORS 限制）；
      ② 混合内容（https 页面加载 http 流）；
      ③ m3u8 内相对/绝对地址无法直接播放的问题（自动改写为经过本服务的地址）。
    仅监听回环地址，外部无法访问；只允许 http/https 目标。
    """

    def __init__(self, user_agent: str = "", timeout: float = 15.0, use_local_hlsjs: bool = True):
        self.user_agent = user_agent or M3ULE_DEFAULT_USER_AGENT
        self.timeout = max(3.0, float(timeout or 15.0))
        self.use_local_hlsjs = bool(use_local_hlsjs)
        self._httpd = None
        self._thread = None
        self._port = 0
        self._session_lock = threading.Lock()
        self._session = None
        self.relay_log: list = []

    def relay_record_request(self, entry: str) -> None:
        self.relay_log.append(entry)
        if len(self.relay_log) > 200:
            del self.relay_log[:100]

    def relay_recent_requests(self, limit: int = 20) -> list:
        return self.relay_log[-limit:]

    def relay_mark(self) -> int:
        """返回当前请求日志长度，作为后续观测的基准点。"""
        return len(self.relay_log)

    def relay_requests_since(self, mark: int) -> list:
        return self.relay_log[max(0, int(mark)):]

    def relay_asset_requests_since(self, mark: int) -> list:
        return [item for item in self.relay_requests_since(mark) if item.startswith("/asset")]

    # -- 生命周期 -----------------------------------------------------------
    def relay_start(self) -> bool:
        if self._httpd is not None:
            return True
        try:
            handler_class = self.relay_make_handler_class()
            self._httpd = http.server.ThreadingHTTPServer((M3ULE_RELAY_HOST, 0), handler_class)
            self._httpd.daemon_threads = True
            self._httpd.relay_owner = self  # type: ignore[attr-defined]
            self._port = int(self._httpd.server_address[1])
            self._thread = threading.Thread(
                target=self._httpd.serve_forever, name="M3ULEStreamRelay", daemon=True)
            self._thread.start()
            return True
        except Exception:
            self._httpd = None
            self._thread = None
            self._port = 0
            return False

    def relay_stop(self) -> None:
        httpd = self._httpd
        self._httpd = None
        self._thread = None
        self._port = 0
        if httpd is not None:
            try:
                httpd.shutdown()
                httpd.server_close()
            except Exception:
                pass
        with self._session_lock:
            if self._session is not None:
                try:
                    self._session.close()
                except Exception:
                    pass
                self._session = None

    def relay_is_running(self) -> bool:
        return self._httpd is not None

    def relay_base_url(self) -> str:
        return f"http://{M3ULE_RELAY_HOST}:{self._port}"

    def relay_player_url(self, stream_url: str, title: str = "") -> str:
        token = self.relay_encode_target(stream_url)
        name = urllib.parse.quote(title or "", safe="")
        return f"{self.relay_base_url()}/player?u={token}&t={name}"

    def relay_proxy_url(self, target_url: str) -> str:
        return f"{self.relay_base_url()}/asset?u={self.relay_encode_target(target_url)}"

    # -- 工具 ---------------------------------------------------------------
    @staticmethod
    def relay_encode_target(target_url: str) -> str:
        raw = base64.urlsafe_b64encode((target_url or "").encode("utf-8")).decode("ascii")
        return raw.rstrip("=")

    @staticmethod
    def relay_decode_target(token: str) -> str:
        if not token:
            return ""
        padded = token + "=" * (-len(token) % 4)
        try:
            return base64.urlsafe_b64decode(padded.encode("ascii")).decode("utf-8")
        except Exception:
            return ""

    @staticmethod
    def relay_target_allowed(target_url: str) -> bool:
        try:
            parts = urllib.parse.urlsplit(target_url or "")
        except ValueError:
            return False
        return parts.scheme.lower() in ("http", "https") and bool(parts.netloc)

    def relay_get_session(self):
        requests = m3ule_get_requests_module()
        if requests is None:
            return None
        with self._session_lock:
            if self._session is None:
                session = requests.Session()
                session.verify = False
                adapter = requests.adapters.HTTPAdapter(pool_connections=16, pool_maxsize=32)
                session.mount("http://", adapter)
                session.mount("https://", adapter)
                self._session = session
            return self._session

    # -- 播放页 -------------------------------------------------------------
    def relay_build_player_html(self, stream_url: str, title: str = "", autoplay: bool = True) -> str:
        # 播放页内的播放地址必须走本机中转，否则 hls.js 取清单/分片会被跨域策略拦截
        relay_source = self.relay_proxy_url(stream_url) if stream_url else stream_url
        page = M3ULE_HTML5_PLAYER_PAGE
        page = page.replace("__SRC_JSON__", json.dumps(relay_source, ensure_ascii=False))
        page = page.replace("__RAW_JSON__", json.dumps(stream_url or "", ensure_ascii=False))
        page = page.replace("__TITLE_JSON__", json.dumps(title or "未命名频道", ensure_ascii=False))
        page = page.replace("__TITLE__", html.escape(title or "HTML5 播放器", quote=True))
        page = page.replace("__URLTEXT__", html.escape(stream_url or "", quote=True))
        page = page.replace("__AUTOPLAY_JS__", "true" if autoplay else "false")
        page = page.replace("__CDN_JSON__", json.dumps(list(M3ULE_HLSJS_CDN_LIST)))
        return page

    def relay_local_hlsjs_path(self) -> str:
        program_dir = m3ule_get_program_dir()
        for candidate in (
            os.path.join(program_dir, "assets", M3ULE_HLSJS_LOCAL_NAME),
            os.path.join(program_dir, M3ULE_HLSJS_LOCAL_NAME),
        ):
            if os.path.isfile(candidate):
                return candidate
        return ""

    # -- 清单改写 -----------------------------------------------------------
    def relay_rewrite_playlist(self, text: str, base_url: str) -> str:
        """把 m3u8 中的所有 URI（分片、子清单、密钥、初始化段）改写为经过本服务的地址。"""
        output: list = []
        for raw_line in text.replace("\r\n", "\n").split("\n"):
            line = raw_line.rstrip("\r")
            stripped = line.strip()
            if not stripped:
                output.append(line)
                continue
            if stripped.startswith("#"):
                if 'URI="' in line:
                    line = re.sub(
                        r'URI="([^"]*)"',
                        lambda m: 'URI="%s"' % self.relay_proxy_url(
                            urllib.parse.urljoin(base_url, m.group(1))) if m.group(1) else 'URI=""',
                        line)
                output.append(line)
            else:
                output.append(self.relay_proxy_url(urllib.parse.urljoin(base_url, stripped)))
        return "\n".join(output)

    # -- HTTP 处理 ----------------------------------------------------------
    def relay_make_handler_class(self):
        owner = self

        class _M3ULEStreamRelayHandler(http.server.BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.0"

            def log_message(self, *_args):  # 静默：避免刷屏
                pass

            def send_response(self, code, message=None):
                # 本服务每个响应后立即关闭连接（HTTP/1.0 + Connection: close），
                # 否则 Chromium 会因连接未关闭而把导航判定为失败。
                self.close_connection = True
                super().send_response(code, message)
                self.send_header("Connection", "close")

            def do_GET(self):  # noqa: N802
                owner.relay_handle_request(self, head_only=False)

            def do_HEAD(self):  # noqa: N802
                owner.relay_handle_request(self, head_only=True)

            def do_OPTIONS(self):  # noqa: N802
                try:
                    self.send_response(204)
                    self.relay_send_cors_headers()
                    self.send_header("Access-Control-Allow-Methods", "GET, HEAD, OPTIONS")
                    self.send_header("Access-Control-Allow-Headers", "*")
                    self.send_header("Content-Length", "0")
                    self.end_headers()
                except Exception:
                    pass

            def relay_send_cors_headers(self):
                self.send_header("Access-Control-Allow-Origin", "*")
                self.send_header("Cache-Control", "no-store")

            def relay_send_text(self, status, text, content_type="text/plain; charset=utf-8"):
                body = text.encode("utf-8", errors="replace")
                try:
                    self.send_response(status)
                    self.send_header("Content-Type", content_type)
                    self.send_header("Content-Length", str(len(body)))
                    self.relay_send_cors_headers()
                    self.end_headers()
                    if body:
                        self.wfile.write(body)
                except (BrokenPipeError, ConnectionAbortedError, ConnectionResetError, OSError):
                    pass

        return _M3ULEStreamRelayHandler

    def relay_handle_request(self, handler, head_only: bool = False) -> None:
        try:
            parsed = urllib.parse.urlsplit(handler.path)
            route = parsed.path
            query = urllib.parse.parse_qs(parsed.query)
        except Exception:
            return
        token = (query.get("u") or [""])[0]
        if route not in ("/player", "/player.html", "/index.html"):
            self.relay_record_request(
                f"{route} -> {self.relay_decode_target(token)[:140]}")
        if route in ("/", "/player", "/player.html", "/index.html"):
            if route != "/":
                self.relay_record_request(f"{route} (播放页, 目标 {self.relay_decode_target(token)[:100]})")
            target = self.relay_decode_target(token)
            title = (query.get("t") or [""])[0]
            autoplay = (query.get("a") or ["1"])[0] not in ("0", "false")
            handler.relay_send_text(
                200, self.relay_build_player_html(target, title, autoplay),
                "text/html; charset=utf-8")
            return
        if route in ("/hls.js", "/hls.min.js"):
            path = self.relay_local_hlsjs_path() if self.use_local_hlsjs else ""
            if not path:
                handler.relay_send_text(404, "local hls.js not bundled")
                return
            try:
                with open(path, "rb") as handle:
                    data = handle.read()
            except OSError:
                handler.relay_send_text(404, "local hls.js unreadable")
                return
            try:
                handler.send_response(200)
                handler.send_header("Content-Type", "application/javascript; charset=utf-8")
                handler.send_header("Content-Length", str(len(data)))
                handler.relay_send_cors_headers()
                handler.end_headers()
                if not head_only:
                    handler.wfile.write(data)
            except (BrokenPipeError, ConnectionAbortedError, ConnectionResetError, OSError):
                pass
            return
        if route in ("/asset", "/stream", "/proxy"):
            self.relay_proxy_target(handler, self.relay_decode_target(token), head_only)
            return
        handler.relay_send_text(404, "unknown relay route")

    def relay_proxy_target(self, handler, target_url: str, head_only: bool = False) -> None:
        if not self.relay_target_allowed(target_url):
            handler.relay_send_text(403, "unsupported target url")
            return
        session = self.relay_get_session()
        if session is None:
            handler.relay_send_text(500, "requests library unavailable")
            return
        parts = urllib.parse.urlsplit(target_url)
        headers = {
            "User-Agent": self.user_agent,
            "Accept": "*/*",
            "Accept-Language": "zh-CN,zh;q=0.9",
            "Referer": f"{parts.scheme}://{parts.netloc}/",
            "Connection": "close",
        }
        range_header = handler.headers.get("Range")
        if range_header:
            headers["Range"] = range_header
        response = None
        try:
            response = session.get(
                target_url, headers=headers, timeout=(self.timeout, self.timeout),
                stream=True, allow_redirects=True)
            status = response.status_code
            content_type = response.headers.get("Content-Type", "") or ""
            final_url = response.url

            peek = b""
            for chunk in response.iter_content(4096):
                peek = chunk or b""
                break

            is_playlist = self.relay_target_is_playlist(final_url, content_type, peek)
            if is_playlist:
                buffer = bytearray(peek)
                for chunk in response.iter_content(65536):
                    buffer.extend(chunk)
                    if len(buffer) > M3ULE_RELAY_PLAYLIST_LIMIT:
                        break
                text = bytes(buffer).decode("utf-8", errors="replace")
                if "#EXTM3U" not in text:
                    handler.relay_send_text(status, text)
                    return
                rewritten = self.relay_rewrite_playlist(text, final_url)
                handler.relay_send_text(status, rewritten,
                                        "application/vnd.apple.mpegurl; charset=utf-8")
                return

            try:
                handler.send_response(status)
                if content_type:
                    handler.send_header("Content-Type", content_type)
                content_length = response.headers.get("Content-Length")
                if content_length:
                    handler.send_header("Content-Length", content_length)
                for header_name in ("Content-Range", "Accept-Ranges"):
                    header_value = response.headers.get(header_name)
                    if header_value:
                        handler.send_header(header_name, header_value)
                handler.relay_send_cors_headers()
                handler.end_headers()
            except (BrokenPipeError, ConnectionAbortedError, ConnectionResetError, OSError):
                return
            if head_only or status in (204, 304):
                return
            try:
                if peek:
                    handler.wfile.write(peek)
                for chunk in response.iter_content(65536):
                    if not chunk:
                        continue
                    handler.wfile.write(chunk)
            except (BrokenPipeError, ConnectionAbortedError, ConnectionResetError, OSError):
                pass
        except Exception as exc:  # noqa: BLE001 - 中转失败只需回传错误信息
            try:
                handler.relay_send_text(502, f"relay error: {type(exc).__name__}: {exc}")
            except Exception:
                pass
        finally:
            if response is not None:
                try:
                    response.close()
                except Exception:
                    pass

    @staticmethod
    def relay_target_is_playlist(url: str, content_type: str, peek: bytes) -> bool:
        lowered = (content_type or "").lower()
        if "mpegurl" in lowered:
            return True
        if urllib.parse.urlsplit(url or "").path.lower().endswith((".m3u8", ".m3u")):
            return True
        return b"#EXTM3U" in (peek or b"")[:2048]


# ----------------------------------------------------------------------------
# 弹窗播放内核：只保留两个 —— FFmpeg（Qt 多媒体内嵌）与 VLC（libvlc），默认 FFmpeg
# ----------------------------------------------------------------------------
M3ULE_PLAYER_BACKEND_DEFAULT = "qtmm"
M3ULE_PLAYER_BACKEND_LABELS = OrderedDict((
    ("qtmm", "FFmpeg（内嵌 Qt 多媒体）"),
    ("vlc", "VLC（libvlc）"),
))
M3ULE_PLAYER_BACKENDS = list(M3ULE_PLAYER_BACKEND_LABELS.values())
M3ULE_PLAYER_BACKEND_CHAIN = tuple(M3ULE_PLAYER_BACKEND_LABELS.keys())
# v1.8.4 起不再提供 HTML5（Qt WebEngine）/ mpv（libmpv）内核：旧设置值统一迁移到默认内核
M3ULE_PLAYER_BACKEND_LEGACY = {
    "html5": M3ULE_PLAYER_BACKEND_DEFAULT,
    "mpv": M3ULE_PLAYER_BACKEND_DEFAULT,
    "auto": M3ULE_PLAYER_BACKEND_DEFAULT,
    "自动": M3ULE_PLAYER_BACKEND_DEFAULT,
    "内嵌 HTML5（Qt WebEngine）": M3ULE_PLAYER_BACKEND_DEFAULT,
    "Qt 多媒体（FFmpeg 解码）": M3ULE_PLAYER_BACKEND_DEFAULT,
    "mpv（libmpv）": M3ULE_PLAYER_BACKEND_DEFAULT,
    "自动（推荐）": M3ULE_PLAYER_BACKEND_DEFAULT,
}
# 已移除内核留下的设置键（启动时清掉，避免设置文件里堆着没用的项）
M3ULE_PLAYER_OBSOLETE_SETTINGS = (
    "player/libmpv_path", "player/libmpv_dependency_repair",
    "player/html5_render_mode", "player/html5_render_fallback",
)
# 播放弹窗工具栏里的下拉框宽度上限：宽度跟着内容走，但长频道名不会把工具栏顶宽
M3ULE_PLAYER_COMBO_MAX_WIDTH = 260
M3ULE_LIBVLC_PATH_ENV = "M3ULE_LIBVLC_PATH"
M3ULE_LIBVLC_DIR_ENV = "M3ULE_LIBVLC_DIR"
M3ULE_LIBVLC_NAMES = ("libvlc.dll", "libvlc-5.dll", "libvlc-4.dll")

# 加载器硬错误弹框（「无法定位程序输入点 … 于动态链接库 … 上」）的开关位：
# 双击 bat / 无控制台运行时，操作系统会用模态框报告依赖解析失败，卡住整个界面且看不出是哪个模块。
# 设上这些位后，加载失败会以错误码返回，由程序自己写日志、给出可读原因。
M3ULE_LOADER_ERROR_MODE_FLAGS = 0x0001 | 0x0002 | 0x8000  # FAILCRITICALERRORS|NOGPFAULTERRORBOX|NOOPENFILEERRORBOX
M3ULE_LIBRARY_LOAD_CACHE = {}
M3ULE_PRELOADED_MODULES = {}


# ----------------------------------------------------------------------------
# 默认设置（所有设置均实时自动保存 / 启动自动加载）
# ----------------------------------------------------------------------------
M3ULE_SYNC_ACTION_UPDATE = "更新编号"
M3ULE_SYNC_ACTION_SAME = "已一致"
M3ULE_SYNC_ACTION_ADD = "新增"
M3ULE_SYNC_ACTION_UNMATCHED = "未匹配"
M3ULE_SYNC_ACTION_CONFLICT = "冲突"
M3ULE_SYNC_ACTION_NO_INDEX = "无编号"
M3ULE_SYNC_ACTION_REMOVE = "删除旧频道"
M3ULE_SYNC_ACTION_SKIP = "跳过"
M3ULE_SYNC_ACTION_ORDER = (
    M3ULE_SYNC_ACTION_UPDATE, M3ULE_SYNC_ACTION_ADD, M3ULE_SYNC_ACTION_REMOVE,
    M3ULE_SYNC_ACTION_SKIP, M3ULE_SYNC_ACTION_CONFLICT,
    M3ULE_SYNC_ACTION_NO_INDEX, M3ULE_SYNC_ACTION_UNMATCHED, M3ULE_SYNC_ACTION_SAME,
)
M3ULE_SYNC_MATCH_MODES = ("忽略大小写与空格", "忽略大小写", "完全一致")
M3ULE_SYNC_SOURCE_MODES = ("已校对的文件", "数据库编号映射")
M3ULE_SYNC_MODES = (
    "只更新编号（同名频道，保留原文件其它频道）",
    "整表替换（用来源重建，旧频道清除）",
)
M3ULE_SYNC_NEW_TITLE_MODES = ("只用频道名", "[编号] 频道名")
M3ULE_SYNC_INDEX_PATTERNS = (
    r"se_idx=(\d+)",
    r"[?&](?:idx|chno|channel|chan|chn|num|no|index|id)=(\d+)",
    r"/(?:idx|index|channel)=(\d+)",
)

M3ULE_DEFAULT_SETTINGS = {
    "probe/workers": 16,
    "probe/timeout": 8.0,
    "probe/retries": 1,
    "probe/deep": True,
    "probe/ignore_ssl": True,
    "probe/user_agent": M3ULE_DEFAULT_USER_AGENT,
    "probe/proxy": "",
    "cache/enabled": True,
    "cache/auto_apply": True,
    "cache/skip_fresh": True,
    "cache/ttl_hours": 72,
    "cache/auto_store": True,
    "player/path": "",
    "player/html5_mode": "内嵌窗口",
    "player/backend": M3ULE_PLAYER_BACKEND_LABELS[M3ULE_PLAYER_BACKEND_DEFAULT],
    "player/libvlc_path": "",
    "player/html5_autoplay": True,
    "player/html5_local_hlsjs": True,
    "ui/theme": "浅色",
    "ui/font_size": 10,
    "ui/test_failed_only": False,
    "ui/filter_failed_only": False,
    "ui/test_scope": "全部条目",
    "ui/current_tab": 0,
    "ui/sort_column": -1,
    "ui/sort_order": 0,
    "ui/column_widths": "{}",
    "ui/column_layout_edit": "",
    "ui/column_layout_test": "",
    "ui/settings_category": 0,
    "ui/log_auto_scroll": True,
    "ui/table_row_height": 24,
    "io/last_open_dir": "",
    "io/last_save_dir": "",
    "io/last_file": "",
    "io/auto_open_last": True,
    "io/auto_backup_on_save": True,
    "io/backup_keep": 30,
    "io/auto_save_settings": True,
    "scan/template": "",
    "scan/start": 0,
    "scan/end": 199,
    "scan/step": 1,
    "scan/pad": 3,
    "scan/workers": 16,
    "scan/timeout": 8.0,
    "scan/deep": True,
    "scan/auto_add_id_attr": True,
    "diff/mode": 0,
    "diff/pair_signal_filter": 0,
    "diff/pair_history_old": True,
    "diff/pair_old": "",
    "diff/pair_new": "",
    "sync/source_mode": M3ULE_SYNC_SOURCE_MODES[0],
    "sync/source_file": "",
    "sync/target_file": "",
    "sync/match_mode": M3ULE_SYNC_MATCH_MODES[0],
    "sync/mode": M3ULE_SYNC_MODES[0],
    "sync/add_missing": True,
    "sync/new_group": "",
    "sync/new_tvg_name": True,
    "sync/new_title_mode": M3ULE_SYNC_NEW_TITLE_MODES[0],
    "sync/write_tvg_name": True,
    "sync/write_title": True,
    "sync/write_ids": True,
    "sync/keep_meta": True,
    "sync/skip_dead": True,
    "sync/keep_unnamed": True,
    "sync/id_prefix": "",
    "logo/sources": "",
    "logo/use_db": True,
    "logo/use_head_epg": True,
    "logo/fill_missing": True,
    "logo/fuzzy": False,
    "logo/store": True,
    "logo/dir_url_prefix": "",
    "logo/last_source_dir": "",
    "logo/last_dir": "",
    "logo/bundled_added": False,
    "log/to_file": True,
    "io/recent_files": "",
    "env/epg_api_key": "",
    "env/db_password": "",
    "env/proxy_url": "",
}

M3ULE_TEST_STATE_COLORS = {
    M3ULE_STATUS_OK: QColor("#137333"),
    M3ULE_STATUS_PARTIAL: QColor("#9a6b00"),
    M3ULE_STATUS_FAIL: QColor("#c5221f"),
    M3ULE_STATUS_TIMEOUT: QColor("#c05621"),
    M3ULE_STATUS_ERROR: QColor("#5f6368"),
    M3ULE_STATUS_CANCEL: QColor("#5f6368"),
    M3ULE_STATUS_NONE: QColor("#5f6368"),
}

M3ULE_TEST_STATE_BG = {
    M3ULE_STATUS_OK: QColor("#e6f4ea"),
    M3ULE_STATUS_PARTIAL: QColor("#fef7e0"),
    M3ULE_STATUS_FAIL: QColor("#fce8e6"),
    M3ULE_STATUS_TIMEOUT: QColor("#fdece0"),
    M3ULE_STATUS_ERROR: QColor("#f1f3f4"),
    M3ULE_STATUS_CANCEL: QColor("#f1f3f4"),
}

# 二次测试差异（「对比上次」列）：这次测试相比上次是多台还是少台
M3ULE_DELTA_NONE = ""
M3ULE_DELTA_FIRST = "首次测试"
M3ULE_DELTA_GAINED = "★新增可用"
M3ULE_DELTA_LOST = "★新失效"
M3ULE_DELTA_KEEP_OK = "仍然可用"
M3ULE_DELTA_KEEP_BAD = "仍然不可用"
M3ULE_DELTA_UNTESTED = "本次未测"
M3ULE_DELTA_ORDER = [M3ULE_DELTA_GAINED, M3ULE_DELTA_LOST, M3ULE_DELTA_KEEP_OK,
                     M3ULE_DELTA_KEEP_BAD, M3ULE_DELTA_FIRST, M3ULE_DELTA_UNTESTED]
M3ULE_DELTA_COLORS = {
    M3ULE_DELTA_GAINED: QColor("#137333"),
    M3ULE_DELTA_LOST: QColor("#c5221f"),
    M3ULE_DELTA_KEEP_OK: QColor("#5f6368"),
    M3ULE_DELTA_KEEP_BAD: QColor("#9aa0a6"),
    M3ULE_DELTA_FIRST: QColor("#1a73e8"),
    M3ULE_DELTA_UNTESTED: QColor("#9aa0a6"),
}
M3ULE_DELTA_BG = {
    M3ULE_DELTA_GAINED: QColor("#e6f4ea"),
    M3ULE_DELTA_LOST: QColor("#fce8e6"),
}

# 列自定义（每张表各一套布局）
M3ULE_COLUMN_LAYOUT_KEYS = {"edit": "ui/column_layout_edit",
                            "test": "ui/column_layout_test"}

# 内嵌播放器的渲染方式（Chromium 在部分机器上无法创建 GL 上下文 → 必须走软件渲染）

# ----------------------------------------------------------------------------
# 设置管理（QSettings + .env 密钥）
# ----------------------------------------------------------------------------

class M3ULiveEditorConfigManager(QObject):
    """集中管理设置项：读写、默认值、自动保存、.env 密钥。"""

    sig_config_changed = Signal(str, object)

    def __init__(self, parent=None):
        super().__init__(parent)
        self._settings = QSettings(m3ule_get_settings_path(), QSettings.IniFormat)
        self._settings.setFallbacksEnabled(False)
        self.cfg_seed_defaults()
        self.secret_env: dict = {}
        self.cfg_reload_env_secrets()

    def cfg_seed_defaults(self) -> None:
        """把从未写入过的默认设置补齐落盘，保证所有设置项都真实保存在 INI 中。"""
        pending = False
        for key, value in M3ULE_DEFAULT_SETTINGS.items():
            if not self._settings.contains(key):
                self._settings.setValue(key, value)
                pending = True
        if pending and self.cfg_get_bool("io/auto_save_settings", True):
            self._settings.sync()

    # -- 通用读写 -----------------------------------------------------------
    def cfg_get(self, key: str, default=None):
        """读取设置。按默认值类型做安全转换（QSettings INI 会把 bool 读回字符串）。"""
        if default is None:
            default = M3ULE_DEFAULT_SETTINGS.get(key, "")
        if isinstance(default, bool):
            value = self._settings.value(key, default)
            if isinstance(value, str):
                return value.strip().lower() in ("1", "true", "yes", "on")
            return bool(value)
        if isinstance(default, int):
            return m3ule_safe_int(self._settings.value(key, default), int(default))
        if isinstance(default, float):
            return m3ule_safe_float(self._settings.value(key, default), float(default))
        value = self._settings.value(key, default)
        return "" if value is None else str(value)

    def cfg_set(self, key: str, value, emit: bool = True) -> None:
        self._settings.setValue(key, value)
        if self.cfg_get_bool("io/auto_save_settings", True):
            self._settings.sync()
        if emit:
            self.sig_config_changed.emit(key, value)

    def cfg_get_bool(self, key: str, default: bool = False) -> bool:
        value = self._settings.value(key, default)
        if isinstance(value, str):
            return value.strip().lower() in ("1", "true", "yes", "on")
        return bool(value)

    def cfg_set_many(self, values: dict) -> None:
        for key, value in values.items():
            self._settings.setValue(key, value)
        if self.cfg_get_bool("io/auto_save_settings", True):
            self._settings.sync()

    def cfg_reset_all(self) -> None:
        self._settings.clear()
        self._settings.sync()
        for key, value in M3ULE_DEFAULT_SETTINGS.items():
            self._settings.setValue(key, value)
        self._settings.sync()

    def cfg_save_geometry(self, key: str, value: QByteArray) -> None:
        self._settings.setValue(key, value)
        self._settings.sync()

    def cfg_load_geometry(self, key: str) -> QByteArray:
        value = self._settings.value(key, QByteArray())
        return value if isinstance(value, QByteArray) else QByteArray()

    def cfg_save_state(self, key: str, value: QByteArray) -> None:
        self._settings.setValue(key, value)
        self._settings.sync()

    def cfg_load_state(self, key: str) -> QByteArray:
        value = self._settings.value(key, QByteArray())
        return value if isinstance(value, QByteArray) else QByteArray()

    # -- .env 密钥 ----------------------------------------------------------
    def cfg_reload_env_secrets(self) -> dict:
        self.secret_env = m3ule_load_env_file()
        return self.secret_env

    def cfg_env_value(self, name: str, default: str = "") -> str:
        return os.environ.get(name, self.secret_env.get(name, default)) or default

    def cfg_save_env_secret(self, name: str, value: str) -> bool:
        return m3ule_save_env_key(name, value)

    def cfg_get_user_agent(self) -> str:
        return self.cfg_env_value("M3ULE_USER_AGENT", self.cfg_get("probe/user_agent")) or M3ULE_DEFAULT_USER_AGENT

    def cfg_get_proxy(self) -> str:
        return self.cfg_env_value("M3ULE_PROXY", self.cfg_get("probe/proxy"))

    def cfg_get_db_password(self) -> str:
        return self.cfg_env_value("M3ULE_DB_PASSWORD", "")


# ----------------------------------------------------------------------------
# 表格模型
# ----------------------------------------------------------------------------
M3ULE_TABLE_COLUMNS = [
    {"key": "seq",        "title": "序号",      "editable": False, "width": 56},
    {"key": "name",       "title": "频道名称",   "editable": True,  "width": 160},
    {"key": "tvg-name",   "title": "tvg名称",   "editable": True,  "width": 140},
    {"key": "group-title", "title": "分组",     "editable": True,  "width": 120},
    {"key": "tvg-id",     "title": "tvg-id",    "editable": True,  "width": 78},
    {"key": "channelID",  "title": "channelID", "editable": True,  "width": 92},
    {"key": "tvg-chno",   "title": "频道号",    "editable": True,  "width": 78},
    {"key": "duration",   "title": "时长",      "editable": True,  "width": 60},
    {"key": "test",       "title": "状态",      "editable": False, "width": 92},
    {"key": "delta",      "title": "对比上次",  "editable": False, "width": 108},
    {"key": "ms",         "title": "耗时(ms)",  "editable": False, "width": 78},
    {"key": "tested_at",  "title": "检测时间",   "editable": False, "width": 132},
    {"key": "kbps",       "title": "码率(kbps)", "editable": False, "width": 86},
    {"key": "delay",      "title": "延迟(s)",   "editable": False, "width": 74},
    {"key": "stream_id",  "title": "流ID",      "editable": False, "width": 96},
    {"key": "detail",     "title": "测试详情",   "editable": False, "width": 240},
    {"key": "remark",     "title": "备注",      "editable": True,  "width": 130},
    {"key": "url",        "title": "链接",      "editable": True,  "width": 420},
]


class M3ULiveEditorTableModel(QAbstractTableModel):
    """频道列表模型：支持编辑、测试状态着色、按 uid 定位。"""

    sig_model_entry_edited = Signal(int)   # uid
    sig_model_structure_changed = Signal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self._document = M3ULiveEditorDocument()
        self._columns = list(M3ULE_TABLE_COLUMNS)

    # -- Qt 模型接口 --------------------------------------------------------
    def rowCount(self, parent=QModelIndex()):
        if parent.isValid():
            return 0
        return len(self._document.entries)

    def columnCount(self, parent=QModelIndex()):
        if parent.isValid():
            return 0
        return len(self._columns)

    def headerData(self, section, orientation, role=Qt.DisplayRole):
        if orientation == Qt.Horizontal:
            if role == Qt.DisplayRole:
                if 0 <= section < len(self._columns):
                    return self._columns[section]["title"]
                return ""
            if role == Qt.ToolTipRole:
                if 0 <= section < len(self._columns):
                    return self._columns[section]["title"]
        else:
            if role == Qt.DisplayRole:
                return str(section + 1)
        return None

    def flags(self, index):
        if not index.isValid():
            return Qt.NoItemFlags
        base = Qt.ItemIsEnabled | Qt.ItemIsSelectable
        if index.column() < len(self._columns) and self._columns[index.column()]["editable"]:
            return base | Qt.ItemIsEditable
        return base

    def data(self, index, role=Qt.DisplayRole):
        if not index.isValid():
            return None
        row = index.row()
        column = index.column()
        entries = self._document.entries
        if not (0 <= row < len(entries)):
            return None
        entry = entries[row]
        key = self._columns[column]["key"]

        if role in (Qt.DisplayRole, Qt.EditRole):
            return self.mdl_display_value(entry, key, row)

        if role == Qt.TextAlignmentRole:
            if key in ("seq", "tvg-chno", "tvg-id", "channelID", "duration", "ms",
                       "test", "tested_at", "kbps", "delay"):
                return int(Qt.AlignCenter)
            if key in ("stream_id", "delta"):
                return int(Qt.AlignCenter)
            return int(Qt.AlignVCenter | Qt.AlignLeft)

        if role == Qt.ForegroundRole:
            if key in ("test", "ms", "detail", "tested_at", "delay"):
                color = M3ULE_TEST_STATE_COLORS.get(entry.test_state)
                if color is not None:
                    return QBrush(color)
            if key == "delta":
                color = M3ULE_DELTA_COLORS.get(entry.entry_delta_label())
                if color is not None:
                    return QBrush(color)
            if key == "remark" and (entry.remark or "").strip():
                return QBrush(QColor("#1a73e8"))
            if key == "stream_id" and entry.test_stream_id:
                return QBrush(QColor("#6a3ab2"))

        if role == Qt.BackgroundRole:
            background = M3ULE_TEST_STATE_BG.get(entry.test_state)
            if background is not None and key in ("test", "ms", "detail", "tested_at", "delay"):
                return QBrush(background)
            if key == "delta":
                delta_bg = M3ULE_DELTA_BG.get(entry.entry_delta_label())
                if delta_bg is not None:
                    return QBrush(delta_bg)

        if role == Qt.FontRole and key == "delta":
            label = entry.entry_delta_label()
            if label in (M3ULE_DELTA_GAINED, M3ULE_DELTA_LOST):
                font = QFont()
                font.setBold(True)
                return font

        if role == Qt.ToolTipRole:
            if key == "url":
                return entry.url or ""
            if key == "detail":
                tip = entry.test_detail or "尚未测试"
                if entry.test_first_segment:
                    tip += f"\n首个分片: {entry.test_first_segment}"
                return tip
            if key == "test":
                tip = f"状态: {entry.test_state or '未测试'}\n{entry.test_detail or ''}"
                if entry.test_cached:
                    tip += f"\n来源: 检测缓存（{entry.test_ts or '时间未知'}）"
                return tip
            if key == "kbps":
                if not (entry.test_kbps and entry.test_kbps > 0):
                    return "尚未测出码率\n（从清单 #EXTINF 的分片字节数换算）"
                tip = (f"清单实测码率：{entry.test_kbps} kbps\n"
                       "（由 #EXTINF 的分片字节数 ÷ 分片时长换算，"
                       "比主清单的 BANDWIDTH 更接近实际占用）")
                if entry.test_variants > 1:
                    tip += f"\n该源提供 {entry.test_variants} 个码率档位"
                if entry.test_encrypted:
                    tip += "\n清单含 #EXT-X-KEY（加密流）"
                return tip
            if key == "delay":
                if entry.test_delay is None or entry.test_delay < 0:
                    return "无法计算直播延迟\n（清单未提供 #EXT-X-PROGRAM-DATE-TIME）"
                tips = [f"清单最后一段的起播时刻距现在约 {entry.test_delay} 秒",
                        "（来自 #EXT-X-PROGRAM-DATE-TIME，即该流相对真实时间的滞后）"]
                if entry.test_delay > 120:
                    tips.append("★ 数值偏大：该频道可能已经卡住或在循环播放旧内容")
                else:
                    tips.append("数值正常，说明内容确实在向前推进")
                return "\n".join(tips)
            if key == "stream_id":
                if not entry.test_stream_id:
                    return ("未取得频道内部流ID\n"
                            "（当前服务的分片地址不符合可识别格式，"
                            "仍可用详情中的地址模板做对比）")
                return ("频道内部流ID（由分片地址解析）\n"
                        "服务端分配给该编号的“流实例编号”，同一编号在短时间内稳定，"
                        "但源端重启/重连时可能变化。\n"
                        "用法：把两份文件的流ID 互相比对——\n"
                        "  · 变化很小 → 多半只是源端重启，不代表换台；\n"
                        "  · 变化很大，或与另一个编号的旧值相同 → "
                        "该编号背后的频道很可能被换过（建议再播放确认）。")
            if key == "tested_at":
                if not entry.test_ts:
                    return "尚未检测"
                source = "检测缓存" if entry.test_cached else "本次运行实测"
                return (f"{source}：{entry.test_ts}\n"
                        f"距现在：{m3ule_probe_cache_age_text(entry.test_ts)}")
            if key == "delta":
                if not entry.test_prev_known:
                    return ("还没有「上一次」测试记录。\n"
                            "再测一次（或在别的时间再测同一批链接），"
                            "这里就会显示相对上次是多了台还是少了台。")
                prev = entry.test_prev_state or "未测"
                cur = entry.test_state or "未测"
                if entry.test_prev_cached:
                    prev += "（检测缓存）"
                lines = [f"上一次：{prev}"
                         + (f"（{entry.test_prev_ts}）" if entry.test_prev_ts else ""),
                         f"本次：{cur}"
                         + (f"（{entry.test_ts}）" if entry.test_ts else ""),
                         "结论：" + (entry.entry_delta_label() or "—")]
                if entry.entry_delta_label() == M3ULE_DELTA_LOST:
                    lines.append("★ 这条链接以前能播，现在播不了了 —— 重点关注是否被换台或下线")
                elif entry.entry_delta_label() == M3ULE_DELTA_GAINED:
                    lines.append("★ 这条链接以前不行，现在可以了 —— 可能是新上的频道")
                return "\n".join(lines)
            if key == "name":
                return entry.entry_effective_name()
        return None

    def setData(self, index, value, role=Qt.EditRole):
        if not index.isValid() or role != Qt.EditRole:
            return False
        row = index.row()
        column = index.column()
        entries = self._document.entries
        if not (0 <= row < len(entries)):
            return False
        if not self._columns[column]["editable"]:
            return False
        entry = entries[row]
        key = self._columns[column]["key"]
        text = "" if value is None else str(value)
        stale_cleared = False
        if key == "url":
            if (entry.url or "") == text:
                return False
            stale_cleared = entry.entry_invalidate_test_if_url_changed(text)
            entry.url = text
        elif key == "remark":
            if (entry.remark or "") == text:
                return False
            entry.remark = text
        elif key == "duration":
            if entry.duration == text:
                return False
            entry.duration = text.strip() or "0"
            entry.entry_rebuild_extinf_line()
        elif key == "name":
            if (entry.title or "") == text:
                return False
            entry.title = text
            entry.entry_rebuild_extinf_line()
        else:
            if entry.entry_get_attr(key) == text:
                return False
            entry.entry_set_attr(key, text)
        self._document.modified = True
        self.dataChanged.emit(index, index)
        if stale_cleared:
            # 链接变了，状态/耗时/检测时间等列都要跟着刷新
            self.mdl_notify_uid_changed(entry.uid)
        self.sig_model_entry_edited.emit(entry.uid)
        return True

    # -- 便利方法 -----------------------------------------------------------
    def mdl_display_value(self, entry, key: str, row: int):
        if key == "seq":
            return row + 1
        if key == "name":
            return entry.title
        if key == "duration":
            return entry.duration
        if key == "test":
            if not entry.test_state:
                return ""
            icon = M3ULE_TEST_STATE_ICON_MAP.get(entry.test_state, "")
            label = f"{icon} {entry.test_state}".strip()
            return f"{label}（缓存）" if entry.test_cached else label
        if key == "ms":
            return entry.test_ms if entry.test_ms is not None and entry.test_ms >= 0 else ""
        if key == "tested_at":
            return entry.test_ts or ""
        if key == "kbps":
            return entry.test_kbps if entry.test_kbps and entry.test_kbps > 0 else ""
        if key == "delay":
            return entry.test_delay if entry.test_delay is not None and entry.test_delay >= 0 else ""
        if key == "stream_id":
            return entry.test_stream_id or ""
        if key == "detail":
            return entry.test_detail or ""
        if key == "delta":
            return entry.entry_delta_label()
        if key == "remark":
            return entry.remark or ""
        if key == "url":
            return entry.url or ""
        return entry.entry_get_attr(key)

    def mdl_set_document(self, document: M3ULiveEditorDocument) -> None:
        self.beginResetModel()
        self._document = document
        self.endResetModel()

    def mdl_document(self) -> M3ULiveEditorDocument:
        return self._document

    def mdl_columns(self) -> list:
        return self._columns

    def mdl_entry_at(self, row: int):
        entries = self._document.entries
        if 0 <= row < len(entries):
            return entries[row]
        return None

    def mdl_uid_at(self, row: int) -> int:
        entry = self.mdl_entry_at(row)
        return entry.uid if entry is not None else -1

    def mdl_row_of_uid(self, uid: int) -> int:
        return self._document.doc_index_of_uid(uid)

    def mdl_entries(self) -> list:
        return self._document.entries

    def mdl_uids(self) -> list:
        return [entry.uid for entry in self._document.entries]

    def mdl_refresh_all(self) -> None:
        self.beginResetModel()
        self.endResetModel()

    def mdl_notify_uid_changed(self, uid: int, columns=None) -> None:
        row = self.mdl_row_of_uid(uid)
        if row < 0:
            return
        if columns:
            for column in columns:
                idx = self.index(row, column)
                self.dataChanged.emit(idx, idx)
        else:
            self.dataChanged.emit(self.index(row, 0),
                                  self.index(row, self.columnCount() - 1))

    def mdl_notify_uids_changed(self, uids) -> None:
        if not uids:
            return
        rows = sorted({self.mdl_row_of_uid(uid) for uid in uids})
        rows = [row for row in rows if row >= 0]
        if not rows:
            return
        top = self.index(min(rows), 0)
        bottom = self.index(max(rows), self.columnCount() - 1)
        self.dataChanged.emit(top, bottom)

    def mdl_notify_structural_change(self) -> None:
        self.beginResetModel()
        self.endResetModel()
        self.sig_model_structure_changed.emit()

    def mdl_column_keys(self) -> list:
        return [column["key"] for column in self._columns]


class M3ULiveEditorSortFilterProxyModel(QSortFilterProxyModel):
    """支持关键词 / 分组 / 测试状态 / 仅失败 的过滤，以及数值感知排序。"""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.filter_keyword = ""
        self.filter_group = ""
        self.filter_state = ""
        self.filter_failed_only = False
        self.filter_untested_only = False
        self.setDynamicSortFilter(True)

    def prx_set_filters(self, keyword="", group="", state="",
                        failed_only=False, untested_only=False) -> None:
        # Qt 6.9+ 推荐 beginFilterChange()/endFilterChange()，旧版回退到 invalidate 系列
        modern_api = hasattr(self, "beginFilterChange") and hasattr(self, "endFilterChange")
        if modern_api:
            self.beginFilterChange()
        self.filter_keyword = (keyword or "").strip()
        self.filter_group = group or ""
        self.filter_state = state or ""
        self.filter_failed_only = bool(failed_only)
        self.filter_untested_only = bool(untested_only)
        if modern_api:
            self.endFilterChange()
        elif hasattr(self, "invalidateRowsFilter"):  # pragma: no cover - 旧版本兼容
            self.invalidateRowsFilter()
        else:  # pragma: no cover - 更旧版本兼容
            self.invalidateFilter()

    def filterAcceptsRow(self, source_row, source_parent):
        model = self.sourceModel()
        if model is None:
            return True
        entry = model.mdl_entry_at(source_row)
        if entry is None:
            return False
        if self.filter_group and entry.entry_effective_group() != self.filter_group:
            return False
        if self.filter_keyword and not entry.entry_matches_keyword(self.filter_keyword):
            return False
        if self.filter_state and entry.test_state != self.filter_state:
            return False
        if self.filter_failed_only and entry.test_state in ("", M3ULE_STATUS_OK, M3ULE_STATUS_NONE):
            return False
        if self.filter_untested_only and entry.test_state not in ("", M3ULE_STATUS_NONE):
            return False
        return True

    def lessThan(self, left, right):
        model = self.sourceModel()
        if model is None:
            return super().lessThan(left, right)
        left_entry = model.mdl_entry_at(left.row())
        right_entry = model.mdl_entry_at(right.row())
        if left_entry is None or right_entry is None:
            return super().lessThan(left, right)
        key = model.mdl_column_keys()[left.column()]
        if key in ("seq", "tvg-id", "tvg-chno", "channelID", "duration", "ms"):
            left_text = str(model.mdl_display_value(left_entry, key, left.row()))
            right_text = str(model.mdl_display_value(right_entry, key, right.row()))
            left_num = m3ule_safe_int(re.sub(r"[^0-9\-]", "", left_text), 1 << 30)
            right_num = m3ule_safe_int(re.sub(r"[^0-9\-]", "", right_text), 1 << 30)
            if left_num != right_num:
                return left_num < right_num
        return super().lessThan(left, right)


# ----------------------------------------------------------------------------
# 检测结果缓存：把测过的链接结果持久化，下次打开 / 再次测试时直接复用
# ----------------------------------------------------------------------------
def m3ule_probe_cache_key(url: str) -> str:
    """把链接规范化为检测缓存键：去空白与片段，协议/主机名小写，去掉默认端口。"""
    text = (url or "").strip()
    if not text:
        return ""
    try:
        parts = urllib.parse.urlsplit(text)
        host = (parts.hostname or "").lower()
    except ValueError:
        return text
    if not host:
        return text
    scheme = (parts.scheme or "").lower()
    try:
        port = parts.port
    except ValueError:
        port = None
    if (scheme == "http" and port == 80) or (scheme == "https" and port == 443):
        port = None
    netloc = host if port is None else f"{host}:{port}"
    if parts.username:
        auth = parts.username
        if parts.password:
            auth += ":" + parts.password
        netloc = f"{auth}@{netloc}"
    return urllib.parse.urlunsplit((scheme, netloc, parts.path, parts.query, ""))


def m3ule_probe_cache_age_hours(checked_at: str):
    """返回缓存时间距现在的小时数；无法解析时返回 None。"""
    text = (checked_at or "").strip()
    if not text:
        return None
    for pattern in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%dT%H:%M:%S", "%Y-%m-%d"):
        try:
            moment = datetime.strptime(text, pattern)
        except ValueError:
            continue
        return max(0.0, (datetime.now() - moment).total_seconds() / 3600.0)
    return None


def m3ule_probe_cache_is_fresh(checked_at: str, ttl_hours) -> bool:
    """缓存是否仍在有效期内（ttl_hours <= 0 表示永久有效）。"""
    age = m3ule_probe_cache_age_hours(checked_at)
    if age is None:
        return False
    ttl = m3ule_safe_int(ttl_hours, 0)
    if ttl <= 0:
        return True
    return age <= ttl


def m3ule_probe_cache_age_text(checked_at: str) -> str:
    """把缓存时间转成“多久以前”的简短中文描述。"""
    age = m3ule_probe_cache_age_hours(checked_at)
    if age is None:
        return (checked_at or "").strip()
    if age < 1.0 / 60.0:
        return "刚刚"
    if age < 1:
        return f"{int(age * 60)} 分钟前"
    if age < 24:
        return f"{age:.1f} 小时前"
    return f"{age / 24:.1f} 天前"


def m3ule_parse_indexed_title(title: str):
    """解析标题里内嵌的编号，支持 `[000] 频道名` 与 `000 频道名` 两种写法。

    返回 (编号, 频道名, 来源写法)；无法识别时返回 (None, 原标题, "")。
    """
    text = (title or "").strip()
    if not text:
        return None, "", ""
    match = re.match(r"^\[\s*(\d{1,6})\s*\]\s*(.*)$", text)
    if match:
        return int(match.group(1)), match.group(2).strip(), "方括号"
    match = re.match(r"^(\d{1,6})\s*[\.、:：\-]?\s+(\S.*)$", text)
    if match:
        return int(match.group(1)), match.group(2).strip(), "数字前缀"
    return None, text, ""


def m3ule_extract_index_from_url(url: str):
    """从链接里提取频道编号（优先识别直播源常见的 se_idx / idx / chno 等参数）。"""
    text = (url or "").strip()
    if not text:
        return None
    for pattern in (
        r"se_idx=(\d+)",
        r"[?&](?:idx|chno|channel|chan|chn|num|no|index|id)=(\d+)",
        r"/(?:idx|index|channel)=(\d+)",
    ):
        match = re.search(pattern, text, re.I)
        if match:
            try:
                return int(match.group(1))
            except ValueError:
                continue
    return None


def m3ule_build_index_name_map(entries, existing: dict = None) -> dict:
    """把「编号 → 频道名」映射汇总出来，供 ID 扫描 / 编号映射表使用。

    数据来源优先级：标题里内嵌的编号 > 链接里的编号参数。
    已存在的映射（如数据库里手工确认过的）不会被标题覆盖。

    ★ 标题里只有编号没有名称时（例如 `[048]`）**同样会收录**，
    名称留空并在记录里标记 `unnamed=True` —— 这样用户能看到「哪些编号还没认出是什么台」，
    而不是这些编号直接消失。
    """
    result: dict = {}
    for key, value in (existing or {}).items():
        number = m3ule_safe_int(str(key).replace("idx:", ""), -1)
        name = (value.get("channel_name") if isinstance(value, dict) else value) or ""
        if number >= 0 and name:
            result[number] = {"name": name.strip(), "source": "数据库",
                              "unnamed": False,
                              "remark": (value.get("remark") if isinstance(value, dict)
                                         else "") or ""}
    for entry in entries or []:
        number = None
        name = ""
        source = ""
        title_index, title_name, pattern = m3ule_parse_indexed_title(entry.title or "")
        if title_index is not None:
            number = title_index
            name = title_name
            source = f"标题({pattern})" if name else "标题(仅编号)"
            if not name:
                # 标题只有编号（如 `[048]`）时，标题本身不能当名称用；
                # 只额外看一眼 tvg-name 属性，避免把“048”误当成频道名
                attr_name = (entry.entry_get_attr("tvg-name") or "").strip()
                if attr_name:
                    name = attr_name
                    source = "tvg-name 属性"
        else:
            url_index = m3ule_extract_index_from_url(entry.url or "")
            if url_index is not None:
                number = url_index
                name = (entry.entry_effective_name() or "").strip()
                source = "链接参数"
        if number is None:
            continue
        record = result.setdefault(number, {})
        record.setdefault("name", "")
        if name and not record["name"]:
            record["name"] = name
        record.setdefault("source", source)
        record.setdefault("remark", entry.remark or "")
        record.setdefault("uid", entry.uid)
        record.setdefault("url", entry.url or "")
        record["unnamed"] = not bool(record.get("name"))
    return result

def m3ule_index_map_summary(index_map: dict) -> dict:
    """统计映射结果：总数、已命名、待确认。"""
    total = len(index_map or {})
    named = sum(1 for record in (index_map or {}).values() if record.get("name"))
    return {"total": total, "named": named, "unnamed": total - named}


# ----------------------------------------------------------------------------
# 频道同步：把「已校对文件的 频道名 → 编号」同步到另一个文件
#
# 用户场景：A 文件（例如「广州珠江宽频的m3u8直播源 - 154」）已经人工校对完
# 「哪个编号是哪个台」；B 文件（例如 xteve.m3u）里有同样的频道，但编号还是旧的。
# 需要：B 里**同名**频道的编号改成 A 里确认的编号（**只改链接里的编号数字，
# 不动分组 / 台标 / tvg-id / channelID / 频道号等任何其它信息**），
# B 里没有的频道按名字**追加**到末尾（分组留空，用户后续自行分组）。
# 常量见文件上部（M3ULE_SYNC_*，设置默认值要用到，所以放在 M3ULE_DEFAULT_SETTINGS 之前）。
# ----------------------------------------------------------------------------
def m3ule_sync_match_options(mode: str) -> dict:
    """把「匹配方式」文字转成布尔参数（设置里存文字，代码里用布尔）。"""
    text = (mode or "").strip()
    if text == M3ULE_SYNC_MATCH_MODES[2]:
        return {"ignore_case": False, "ignore_space": False}
    if text == M3ULE_SYNC_MATCH_MODES[1]:
        return {"ignore_case": True, "ignore_space": False}
    return {"ignore_case": True, "ignore_space": True}


def m3ule_sync_clean_name(text: str) -> str:
    """去掉名称前的编号标记：`[000] 广东民生` → `广东民生`（只认方括号编号，避免误删名字里的数字）。"""
    name = re.sub(r"^\[\s*\d{1,6}\s*\]\s*", "", (text or "").strip())
    return name.strip()


def m3ule_sync_normalize_name(text: str, ignore_case: bool = True, ignore_space: bool = True) -> str:
    """把频道名规范化，用于「同名」比较（只影响比较，不影响显示与写回）。"""
    name = m3ule_sync_clean_name(text)
    if not name:
        return ""
    if ignore_space:
        name = unicodedata.normalize("NFKC", name)
        name = re.sub(r"\s+", "", name)
    if ignore_case:
        name = name.casefold()
    return name


def m3ule_sync_url_index_span(url: str):
    """链接里编号数字的 (起点, 终点, 原文字)；没有编号时返回 (None, None, "")。"""
    text = url or ""
    for pattern in M3ULE_SYNC_INDEX_PATTERNS:
        match = re.search(pattern, text, re.I)
        if match:
            start, end = match.span(1)
            return start, end, match.group(1)
    return None, None, ""


def m3ule_sync_pad_number(number: int, width: int = 0) -> str:
    """按宽度补零（新编号比宽度长时原样输出）。"""
    digits = str(int(number))
    target = max(0, int(width or 0))
    return digits.rjust(target, "0") if len(digits) < target else digits


def m3ule_sync_url_with_index(url: str, number: int, width: int = 0) -> str:
    """把链接里的编号替换成 number（只动那几位数字，其余原样）。"""
    text = url or ""
    start, end, old = m3ule_sync_url_index_span(text)
    if start is None:
        return text
    digits = m3ule_sync_pad_number(number, int(width or 0) or len(old))
    return text[:start] + digits + text[end:]


def m3ule_sync_url_template(url: str) -> str:
    """把链接里的编号换成 {idx}，用于识别「同一个地址模板」。没有编号时返回空串。"""
    text = url or ""
    start, end, _old = m3ule_sync_url_index_span(text)
    if start is None:
        return ""
    return text[:start] + "{idx}" + text[end:]


def m3ule_sync_url_from_template(template: str, number: int, width: int = 0) -> str:
    """按地址模板生成新链接。"""
    return (template or "").replace("{idx}", m3ule_sync_pad_number(number, width))


def m3ule_sync_retitle_index(extinf_raw: str, number: int, width: int = 0):
    """标题里带 `[NNN]` 时，只把那几位数字换掉（其余字符一个不动）；没有则返回 None。"""
    if not extinf_raw:
        return None
    pattern = re.compile(r"^(\s*#EXTINF[^,]*,\s*)\[\s*(\d{1,6})\s*\]")

    def replace(match):
        digits = m3ule_sync_pad_number(number, int(width or 0) or len(match.group(2)))
        return match.group(1) + "[" + digits + "]"

    return pattern.sub(replace, extinf_raw, count=1) if pattern.match(extinf_raw) else None


def m3ule_sync_entry_index(entry) -> int:
    """条目当前编号：优先链接里的编号参数，其次标题里的 `[NNN]`。"""
    number = m3ule_extract_index_from_url(entry.url or "")
    if number is None:
        title_index, _name, _pattern = m3ule_parse_indexed_title(entry.title or "")
        number = title_index
    return number


def m3ule_sync_entry_names(entry) -> list:
    """条目可参与匹配的名字（标题去编号、tvg-name），去重且保持顺序。"""
    names: list = []
    for candidate in (m3ule_sync_clean_name(entry.title or ""),
                      m3ule_sync_clean_name(entry.entry_get_attr("tvg-name") or "")):
        if candidate and candidate not in names:
            names.append(candidate)
    return names


def m3ule_sync_build_confirmed(entries=None, remarks=None, match=None) -> dict:
    """汇总「频道名 → 已确认编号」。

    来源：① 已校对文件（标题 `[NNN]` 或链接编号参数）；② 数据库里的编号映射（反向使用）。
    同一个名字对应多个编号时记为**冲突**（不参与自动改写，交给人工判断）。
    """
    options = dict(match or {})
    ignore_case = bool(options.get("ignore_case", True))
    ignore_space = bool(options.get("ignore_space", True))
    display: dict = {}
    numbers: dict = {}

    def collect(name: str, number, source: str) -> None:
        if number is None or int(number) < 0:
            return
        key = m3ule_sync_normalize_name(name, ignore_case, ignore_space)
        if not key:
            return
        display.setdefault(key, (name or "").strip())
        numbers.setdefault(key, {})[int(number)] = source

    for key, value in (remarks or {}).items():
        number = m3ule_safe_int(str(key).replace("idx:", ""), -1)
        name = (value.get("channel_name") if isinstance(value, dict) else value) or ""
        collect(str(name).strip(), number, "数据库")
    for entry in (entries or []):
        number = m3ule_sync_entry_index(entry)
        for name in m3ule_sync_entry_names(entry):
            collect(name, number, "文件")

    names: dict = {}
    conflicts: dict = {}
    for key, mapping in numbers.items():
        candidates = sorted(mapping)
        record = {
            "name": display.get(key, ""), "normalized": key, "numbers": candidates,
            "number": candidates[0] if len(candidates) == 1 else None,
            "source": "、".join(sorted({mapping[item] for item in candidates})),
            "conflict": len(candidates) > 1,
        }
        names[key] = record
        if record["conflict"]:
            conflicts[record["name"] or key] = candidates
    return {"names": names, "conflicts": conflicts, "count": len(names),
            "conflict_count": len(conflicts)}


def m3ule_sync_dominant_template(entries) -> dict:
    """目标文件里最常用的地址模板与补零宽度（用于给新增频道拼链接）。"""
    counter: dict = {}
    widths: dict = {}
    for entry in (entries or []):
        template = m3ule_sync_url_template(entry.url or "")
        if not template:
            continue
        counter[template] = counter.get(template, 0) + 1
        _start, _end, old = m3ule_sync_url_index_span(entry.url or "")
        if old:
            widths.setdefault(template, {})
            widths[template][len(old)] = widths[template].get(len(old), 0) + 1
    if not counter:
        return {"template": "", "count": 0, "width": 3}
    template = max(counter, key=lambda item: counter[item])
    width_table = widths.get(template) or {}
    width = max(width_table, key=lambda item: width_table[item]) if width_table else 3
    return {"template": template, "count": counter[template], "width": int(width)}


def m3ule_sync_dominant_duration(entries) -> str:
    """目标文件里最常用的时长写法（新增条目跟着它，保持文件风格一致）。"""
    counter: dict = {}
    for entry in (entries or []):
        value = str(entry.duration if entry.duration is not None else "0").strip() or "0"
        counter[value] = counter.get(value, 0) + 1
    if not counter:
        return "-1"
    return max(counter, key=lambda item: counter[item])


def m3ule_sync_source_index_names(entries) -> dict:
    """把校对文件按编号归类：编号 → [名称...]（含空名称条目，便于提示「这个编号还没填名称」）。"""
    table: dict = {}
    for entry in (entries or []):
        number = m3ule_sync_entry_index(entry)
        if number is None:
            continue
        names = m3ule_sync_entry_names(entry)
        table.setdefault(int(number), []).append(names[0] if names else "")
    return table


def m3ule_sync_similar_names(name: str, target_names: list, limit: int = 2) -> list:
    """在目标名字里找出与新名字「互相包含」的（用于提示可能是同一个台、名字写法不同）。"""
    key = m3ule_sync_normalize_name(name, True, True)
    if len(key) < 2:
        return []
    found: list = []
    for candidate in target_names:
        other = m3ule_sync_normalize_name(candidate, True, True)
        if not other or other == key or len(other) < 2:
            continue
        if key in other or other in key:
            if candidate not in found:
                found.append(candidate)
        if len(found) >= limit:
            break
    return found


# ----------------------------------------------------------------------------
# 台标自动匹配（纯函数）：从各种来源学「频道名 → 台标地址」，再按名字匹配到条目
# ----------------------------------------------------------------------------

M3ULE_LOGO_IMAGE_EXTS = (".png", ".jpg", ".jpeg", ".webp", ".svg", ".gif", ".bmp", ".ico")
M3ULE_LOGO_IPTV_ORG_URL = "https://iptv-org.github.io/iptv/countries/cn.m3u"
M3ULE_LOGO_FUZZY_RATIO = 0.86
M3ULE_LOGO_FUZZY_MIN_LEN = 3
M3ULE_LOGO_FUZZY_CANDIDATES = 1500
M3ULE_LOGO_FUZZY_BUDGET = 60000
M3ULE_LOGO_DB_LIMIT = 20000
# 随程序分发的「网络台标库」文件名（放在 data 目录里，第一次打开对话框会作为默认来源）
M3ULE_LOGO_BUNDLED_NAMES = ("台标库-网络汇总.csv", "台标库.csv")
# JSON 台标库里「频道名」「台标地址」可能用到的键名
M3ULE_LOGO_MAP_NAME_KEYS = ("name", "频道名", "channel", "title", "tvg-name", "display-name")
M3ULE_LOGO_MAP_LOGO_KEYS = ("logo", "logo_url", "tvg-logo", "icon", "台标地址", "url")
# 宽松键要去掉的噪声词（同一台的不同写法：`CCTV1 综合高清` ↔ `CCTV-1`）
M3ULE_LOGO_LOOSE_TOKENS = ("高清", "超清", "蓝光", "标清", "4k", "8k", "1080p", "720p",
                           "hd", "sd", "plus", "＋", "+")
M3ULE_LOGO_LOOSE_SUFFIXES = ("高清频道", "频道", "电视台", "卫视", "直播", "综合", "台")
M3ULE_LOGO_KEY_NOISE = r"[\s\-_·、,，.。:：;；()（）\[\]【】<>《》“”\"'&?？!！/~|]"
M3ULE_LOGO_SOURCE_KINDS = (
    ("file", "参考文件"), ("url", "参考地址"), ("folder", "台标文件夹"),
    ("epg", "EPG 节目单"), ("db", "台标库"),
)
M3ULE_LOGO_STATE_HAS = "已有台标"
M3ULE_LOGO_STATE_SAME = "已是同一台标"
M3ULE_LOGO_STATE_EXACT = "精确匹配"
M3ULE_LOGO_STATE_LOOSE = "去噪匹配"
M3ULE_LOGO_STATE_FUZZY = "相似建议"
M3ULE_LOGO_STATE_MISS = "未匹配"
M3ULE_LOGO_STATE_NAMELESS = "无名条目"
M3ULE_LOGO_APPLY_STATES = (M3ULE_LOGO_STATE_EXACT, M3ULE_LOGO_STATE_LOOSE)
M3ULE_LOGO_STATE_ORDER = (M3ULE_LOGO_STATE_EXACT, M3ULE_LOGO_STATE_LOOSE,
                          M3ULE_LOGO_STATE_FUZZY, M3ULE_LOGO_STATE_SAME,
                          M3ULE_LOGO_STATE_HAS, M3ULE_LOGO_STATE_MISS,
                          M3ULE_LOGO_STATE_NAMELESS)
M3ULE_LOGO_STATE_COLORS = {
    M3ULE_LOGO_STATE_EXACT: "#137333",
    M3ULE_LOGO_STATE_LOOSE: "#137333",
    M3ULE_LOGO_STATE_FUZZY: "#9a6b00",
    M3ULE_LOGO_STATE_SAME: "#5f6368",
    M3ULE_LOGO_STATE_HAS: "#5f6368",
    M3ULE_LOGO_STATE_MISS: "#c5221f",
    M3ULE_LOGO_STATE_NAMELESS: "#9aa0a6",
}
M3ULE_LOGO_FETCH_TIMEOUT = 60
M3ULE_LOGO_FETCH_LIMIT = 40 * 1024 * 1024
M3ULE_LOGO_PREVIEW_LIMIT = 2000


def m3ule_logo_source_label(kind: str) -> str:
    """来源类型的中文名（file / url / folder / epg / db）。"""
    return dict(M3ULE_LOGO_SOURCE_KINDS).get(kind, kind or "")


def m3ule_logo_key(text: str) -> str:
    """台标匹配的严格键：去掉 `[编号]`、全角转半角、去掉空白与常见标点、忽略大小写。"""
    name = m3ule_sync_clean_name(text)
    if not name:
        return ""
    name = unicodedata.normalize("NFKC", name)
    return re.sub(M3ULE_LOGO_KEY_NOISE, "", name).casefold()


def m3ule_logo_loose_key(text: str) -> str:
    """宽松键：在严格键基础上再去掉「高清 / HD / 频道 / 卫视 / 综合」等噪声后缀。"""
    key = m3ule_logo_key(text)
    if not key:
        return ""
    for token in M3ULE_LOGO_LOOSE_TOKENS:
        key = key.replace(token, "")
    trimmed = True
    while trimmed and key:
        trimmed = False
        for suffix in M3ULE_LOGO_LOOSE_SUFFIXES:
            if key != suffix and key.endswith(suffix):
                key = key[: -len(suffix)]
                trimmed = True
    return key


def m3ule_logo_looks_nameless(name: str) -> bool:
    """只有编号没有名称的条目（`[008]`）—— 没有名字就没法按名字匹配台标。"""
    rest = m3ule_sync_clean_name(name)
    return not re.search(r"[0-9a-z\u4e00-\u9fff\u3040-\u30ff\uac00-\ud7af]", rest, re.I)


def m3ule_logo_looks_like_image(url: str) -> bool:
    """地址看起来像图片（`file:///x.png`、`http://…/logo.png?v=1`、`data:image/…`）。"""
    text = (url or "").strip().lower()
    if not text:
        return False
    if text.startswith("data:image/"):
        return True
    path = urllib.parse.urlsplit(text).path or text
    return os.path.splitext(path)[1] in M3ULE_LOGO_IMAGE_EXTS


def m3ule_logo_file_url(path: str) -> str:
    """本机图片路径 → `file:///…` 地址（可直接写进 tvg-logo）。"""
    text = os.path.abspath(path).replace("\\", "/")
    if not text.startswith("/"):
        text = "/" + text
    return "file://" + urllib.parse.quote(text, safe="/:")


def m3ule_logo_learn_from_entries(entries) -> dict:
    """从 m3u 条目里学「频道名 → 台标」：标题 / tvg-name / channelID 都作为名字索引。"""
    learned: "OrderedDict[str, str]" = OrderedDict()
    for entry in list(entries or []):
        logo = (entry.entry_get_attr("tvg-logo") or "").strip()
        if not logo:
            continue
        for name in (entry.title, entry.entry_get_attr("tvg-name"),
                     entry.entry_get_attr("channelID")):
            name = (name or "").strip()
            if name:
                learned.setdefault(name, logo)
    return learned


def m3ule_logo_learn_from_m3u_text(text: str) -> dict:
    """从 m3u 文本里学「频道名 → 台标」（用主程序自己的解析器，兼容各种写法与编码）。"""
    document = M3ULiveEditorDocument()
    document.doc_parse_text(text or "")
    return m3ule_logo_learn_from_entries(document.entries)


def m3ule_logo_learn_from_xmltv_text(text: str) -> dict:
    """从 XMLTV（EPG）里学「频道名 → 台标」：`<display-name>` 配 `<icon src="…"/>`。"""
    learned: "OrderedDict[str, str]" = OrderedDict()
    for block in re.findall(r"<channel\b[^>]*>(.*?)</channel>", text or "", re.S | re.I):
        icon = re.search(r"<icon\b[^>]*\bsrc\s*=\s*\"([^\"]+)\"", block, re.I)
        if not icon:
            continue
        logo = html.unescape(icon.group(1)).strip()
        if not logo:
            continue
        for raw in re.findall(r"<display-name\b[^>]*>([^<]*)</display-name>", block, re.I):
            name = html.unescape(raw).strip()
            if name:
                learned.setdefault(name, logo)
    return learned


def m3ule_logo_looks_like_map_csv(text: str) -> bool:
    """像不像「台标库映射 CSV」：首行是含「频道 / name」的表头，或第二列直接就是图片地址。

    以 `#` 开头的首行一律不算 —— m3u 头部 `#EXTM3U x-tvg-url="a,b"` 里的逗号不能被当成 CSV。
    """
    lines = [line for line in (text or "").splitlines() if line.strip()][:5]
    if not lines or lines[0].lstrip().startswith("#"):
        return False
    try:
        first = next(csv.reader([lines[0]]), [])
    except (csv.Error, ValueError):
        return False
    if len(first) < 2:
        return False
    header = [(cell or "").strip().lower() for cell in first]
    if any("频道" in cell or "name" in cell for cell in header):
        return True
    name, logo = (first[0] or "").strip(), (first[1] or "").strip()
    return (bool(name) and "://" not in name and not name.startswith("<")
            and (m3ule_logo_looks_like_image(logo)
                 or bool(re.match(r"^(https?://|file:|data:image)", logo, re.I))))


def m3ule_logo_learn_from_csv_text(text: str) -> dict:
    """从「台标库映射 CSV」（频道名, 台标地址[, 来源]）里学台标映射。"""
    learned: "OrderedDict[str, str]" = OrderedDict()
    for record in m3ule_logo_map_parse_csv(text):
        name = (record.get("name") or "").strip()
        logo = (record.get("logo") or "").strip()
        if name.startswith("#") or "://" in name:
            continue
        if name and logo:
            learned.setdefault(name, logo)
    return learned


def m3ule_logo_learn_from_json_text(text: str) -> dict:
    """从 JSON 台标库学台标映射：`{"频道名": "台标地址"}` 与 `[{"name": …, "logo": …}]` 都行。"""
    learned: "OrderedDict[str, str]" = OrderedDict()
    try:
        data = json.loads(text or "")
    except (ValueError, TypeError):
        return learned
    rows: list = []
    if isinstance(data, dict):
        for key in ("data", "logos", "list", "channels", "items", "result"):
            if isinstance(data.get(key), list):
                rows = data[key]
                break
        if not rows:
            for name, logo in data.items():
                if isinstance(logo, dict):
                    row = dict(logo)
                    row["name"] = name
                    rows.append(row)
                else:
                    rows.append({"name": name, "logo": logo})
    elif isinstance(data, list):
        rows = data
    for row in rows:
        name = logo = ""
        if isinstance(row, dict):
            for key in M3ULE_LOGO_MAP_NAME_KEYS:
                value = row.get(key)
                if isinstance(value, str) and value.strip():
                    name = value.strip()
                    break
            for key in M3ULE_LOGO_MAP_LOGO_KEYS:
                value = row.get(key)
                if isinstance(value, str) and value.strip():
                    logo = value.strip()
                    break
        elif isinstance(row, (list, tuple)) and len(row) >= 2:
            name, logo = str(row[0]).strip(), str(row[1]).strip()
        if name and logo:
            learned.setdefault(name, logo)
    return learned


def m3ule_logo_learn_from_text(text: str) -> dict:
    """自动识别内容类型（XMLTV / JSON / 台标库 CSV / m3u）并学出台标映射。"""
    head = (text or "")[:4000].lstrip()
    low = head.lower()
    if low.startswith("<?xml") or "<tv" in low or "<channel" in low:
        learned = m3ule_logo_learn_from_xmltv_text(text)
        if learned:
            return learned
    if head[:1] in ("{", "["):
        learned = m3ule_logo_learn_from_json_text(text)
        if learned:
            return learned
    if m3ule_logo_looks_like_map_csv(text):
        learned = m3ule_logo_learn_from_csv_text(text)
        if learned:
            return learned
    return m3ule_logo_learn_from_m3u_text(text)


def m3ule_logo_learn_from_folder(path: str, url_prefix: str = "") -> dict:
    """把一个文件夹里的图片文件名当作频道名（`CCTV1.png` → 频道 `CCTV1`）。

    `url_prefix` 非空时写出「前缀 + 文件名」的网络地址（例如图片目录已由 xteve 之类的
    服务器挂在 `http://主机:端口/data_images/`），否则写出本机 `file:///…` 地址。
    """
    learned: "OrderedDict[str, str]" = OrderedDict()
    prefix = (url_prefix or "").strip().rstrip("/")
    try:
        names = sorted(os.listdir(path))
    except OSError:
        return learned
    for name in names:
        stem, ext = os.path.splitext(name)
        if ext.lower() not in M3ULE_LOGO_IMAGE_EXTS or not stem.strip():
            continue
        logo = (f"{prefix}/{urllib.parse.quote(name)}" if prefix
                else m3ule_logo_file_url(os.path.join(path, name)))
        learned.setdefault(stem.strip(), logo)
    return learned


def m3ule_logo_learn_from_path(path: str, url_prefix: str = "") -> dict:
    """按路径类型学习：文件夹 → 看文件名；文件 → 读进来按 XMLTV / m3u / 台标库 CSV / JSON 解析。"""
    if not path:
        return {}
    if os.path.isdir(path):
        return m3ule_logo_learn_from_folder(path, url_prefix)
    try:
        with open(path, "rb") as handle:
            data = handle.read()
    except OSError:
        return {}
    text, _encoding = M3ULiveEditorDocument.doc_decode_bytes(data)
    return m3ule_logo_learn_from_text(text)


def m3ule_logo_bundled_library_path() -> str:
    """随程序分发的「网络台标库」CSV 路径（data 目录优先，其次程序目录；都没有返回空串）。"""
    for folder in (m3ule_get_data_dir(), m3ule_get_program_dir()):
        for name in M3ULE_LOGO_BUNDLED_NAMES:
            path = os.path.join(folder, name)
            if os.path.isfile(path):
                return path
    return ""


def m3ule_logo_index_add(index: dict, name: str, logo: str, source: str) -> None:
    """把「名字 → 台标」放进索引：严格键与宽松键各占一格，先到者优先（来源顺序=优先级）。

    每个格子里都记着这份来源自己的严格键与宽松键，用来判断命中的是「精确」还是「去噪」。
    """
    logo = (logo or "").strip()
    if not logo:
        return
    info = {"logo": logo, "source": source, "name": name,
            "strict": m3ule_logo_key(name), "loose": m3ule_logo_loose_key(name)}
    for key in (info["strict"], info["loose"]):
        if key and key not in index:
            index[key] = info


def m3ule_logo_build_index(groups) -> dict:
    """把多个来源的「名字 → 台标」合成索引：按传入顺序，先到的来源优先。"""
    index: dict = {}
    for source, learned in list(groups or []):
        for name, logo in (learned or {}).items():
            m3ule_logo_index_add(index, name, logo, source)
    return index


def m3ule_logo_records_to_learned(records) -> dict:
    """台标库记录 → 「名字 → 台标」（用库里的原名字，重复名字先到的优先）。"""
    learned: "OrderedDict[str, str]" = OrderedDict()
    for record in list(records or []):
        name = (record.get("name") or "").strip()
        logo = (record.get("logo") or "").strip()
        if name and logo:
            learned.setdefault(name, logo)
    return learned


def m3ule_logo_fuzzy_lookup(key: str, index: dict, ratio: float = M3ULE_LOGO_FUZZY_RATIO,
                            budget=None) -> dict:
    """在索引里找「相似名」建议：先按首字符 + 长度相近筛掉大部分，再算相似度。

    `budget` 是单元素列表（多条目共享的相似度计算次数上限），用完就停止，避免上千条时卡住。
    """
    if len(key) < M3ULE_LOGO_FUZZY_MIN_LEN:
        return {}
    head = key[:1]
    candidates = [other for other in (index or {})
                  if other[:1] == head and abs(len(other) - len(key)) <= 3]
    if len(candidates) > M3ULE_LOGO_FUZZY_CANDIDATES:
        candidates = candidates[:M3ULE_LOGO_FUZZY_CANDIDATES]
    best: dict = {}
    best_score = 0.0
    for other in candidates:
        if budget is not None:
            if budget[0] <= 0:
                break
            budget[0] -= 1
        score = difflib.SequenceMatcher(None, key, other).ratio()
        if score >= ratio and score > best_score:
            best_score = score
            best = {"logo": index[other]["logo"], "source": index[other]["source"],
                    "name": index[other]["name"], "score": score}
    return best


def m3ule_logo_match_entry(entry, index: dict, fuzzy: bool = False, budget=None) -> dict:
    """给一条条目找台标：严格键 → 宽松键 →（可选）相似建议；不改动任何数据。

    「精确匹配」= 参考来源里的**严格键**就和它一样（编号/空格/标点/大小写之外完全同名）；
    「去噪匹配」= 要去掉「高清 / HD / 频道 / 卫视 / 综合」这类噪声才算同名。
    """
    current = (entry.entry_get_attr("tvg-logo") or "").strip()
    name = entry.entry_effective_name()
    row = {"uid": entry.uid, "name": name, "current": current, "logo": "",
           "source": "", "matched_name": "", "score": 0.0,
           "state": M3ULE_LOGO_STATE_MISS}
    if m3ule_logo_looks_nameless(name):
        row["state"] = M3ULE_LOGO_STATE_NAMELESS
        return row
    index = index or {}
    strict = m3ule_logo_key(name)
    loose = m3ule_logo_loose_key(name)
    info = index.get(strict) if strict else None
    looked_up = strict
    if info is None and loose:
        info = index.get(loose)
        looked_up = loose
    if info is not None:
        row.update({"state": (M3ULE_LOGO_STATE_EXACT if info.get("strict") == looked_up
                              else M3ULE_LOGO_STATE_LOOSE),
                    "logo": info["logo"], "source": info.get("source", ""),
                    "matched_name": info.get("name", "")})
        return row
    if fuzzy:
        found = m3ule_logo_fuzzy_lookup(loose or strict, index, budget=budget)
        if found:
            row.update({"state": M3ULE_LOGO_STATE_FUZZY, "logo": found["logo"],
                        "source": found.get("source", ""),
                        "matched_name": found.get("name", ""),
                        "score": round(found.get("score", 0.0), 3)})
    return row


def m3ule_logo_plan(entries, index: dict, fill_missing_only: bool = True,
                    fuzzy: bool = False) -> dict:
    """做台标匹配计划（只读，不改数据）：返回逐行结果 + 分类计数，供预览与勾选。

    `fill_missing_only=True` 时，已经有台标的条目直接算「已有台标」跳过，不参与覆盖。
    """
    budget = [M3ULE_LOGO_FUZZY_BUDGET]
    rows: list = []
    counts = {state: 0 for state in M3ULE_LOGO_STATE_ORDER}
    for entry in list(entries or []):
        row = m3ule_logo_match_entry(entry, index, fuzzy=fuzzy, budget=budget)
        current = row["current"]
        if current and fill_missing_only:
            row["state"] = M3ULE_LOGO_STATE_HAS
            row["logo"] = ""
            row["note"] = "本来就有台标（按设置跳过；关掉「只补没有台标的条目」可以覆盖）"
        elif row["state"] in M3ULE_LOGO_APPLY_STATES and row["logo"] == current:
            row["state"] = M3ULE_LOGO_STATE_SAME
            row["note"] = "参考里的台标与现有的一样，不用改"
        elif row["state"] == M3ULE_LOGO_STATE_FUZZY:
            row["note"] = "名字只是相似，需人工确认后再勾选"
        elif row["state"] in M3ULE_LOGO_APPLY_STATES:
            row["note"] = "将覆盖原台标" if current else ""
        elif row["state"] == M3ULE_LOGO_STATE_MISS:
            row["note"] = "参考来源里没有同名的频道"
        else:
            row["note"] = "只有编号、没有名称，无法按名字匹配"
        row["apply"] = row["state"] in M3ULE_LOGO_APPLY_STATES and bool(row["logo"])
        row["ok_url"] = m3ule_logo_looks_like_image(row["logo"]) if row["logo"] else False
        if row["logo"] and not row["ok_url"]:
            row["note"] = (row["note"] + "；地址看着不像图片（缺少图片扩展名），写入前先确认"
                           if row["note"] else "地址看着不像图片（缺少图片扩展名），写入前先确认")
        counts[row["state"]] = counts.get(row["state"], 0) + 1
        rows.append(row)
    apply_count = sum(1 for row in rows if row["apply"])
    return {"rows": rows, "counts": counts, "total": len(rows), "apply": apply_count}


def m3ule_logo_summary_text(plan: dict) -> str:
    """预览摘要：可补多少条、哪些没法补。"""
    counts = plan.get("counts", {}) or {}
    text = (f"可补台标 {plan.get('apply', 0)} 条"
            f"（精确 {counts.get(M3ULE_LOGO_STATE_EXACT, 0)}"
            f" / 去噪 {counts.get(M3ULE_LOGO_STATE_LOOSE, 0)}）"
            f"，共 {plan.get('total', 0)} 条")
    extras = []
    for state in (M3ULE_LOGO_STATE_FUZZY, M3ULE_LOGO_STATE_SAME, M3ULE_LOGO_STATE_HAS,
                  M3ULE_LOGO_STATE_MISS, M3ULE_LOGO_STATE_NAMELESS):
        if counts.get(state):
            extras.append(f"{state} {counts[state]}")
    if extras:
        text += "；" + " / ".join(extras)
    return text


def m3ule_logo_apply_rows(document, rows) -> int:
    """按计划写 `tvg-logo`（只写 `apply` 为真的行），返回真正改动的条数。"""
    by_uid: dict = {}
    for row in list(rows or []):
        if row.get("apply") and (row.get("logo") or "").strip():
            by_uid[row.get("uid")] = row["logo"].strip()
    if not by_uid or document is None:
        return 0
    changed = 0
    for entry in document.entries:
        logo = by_uid.pop(entry.uid, "")
        if not logo or entry.entry_get_attr("tvg-logo") == logo:
            continue
        entry.entry_set_attr("tvg-logo", logo)
        changed += 1
    return changed


def m3ule_logo_db_rows(rows, source_label: str = "") -> list:
    """把计划里要采用的匹配结果整理成入库行（name_key / name / logo / source）。"""
    output: list = []
    seen: set = set()
    for row in list(rows or []):
        if not row.get("apply"):
            continue
        logo = (row.get("logo") or "").strip()
        name = (row.get("matched_name") or row.get("name") or "").strip()
        key = m3ule_logo_key(name)
        if not logo or not key or key in seen:
            continue
        seen.add(key)
        output.append({"name_key": key, "name": name, "logo": logo,
                       "source": source_label or row.get("source", "")})
    return output


def m3ule_logo_plan_csv_rows(plan: dict) -> list:
    """预览结果的 CSV 行（表头 + 数据）。"""
    rows = [["序号", "频道名称", "状态", "台标地址", "来源", "参考里的名字", "相似度", "说明"]]
    for index, row in enumerate(plan.get("rows", []) or []):
        rows.append([index + 1, row.get("name", ""), row.get("state", ""),
                     row.get("logo", ""), row.get("source", ""),
                     row.get("matched_name", ""), row.get("score") or "", row.get("note", "")])
    return rows


def m3ule_logo_head_epg_urls(document) -> list:
    """从 m3u 头部（`#EXTM3U` 行）取出声明的 EPG 地址：`x-tvg-url` / `url-tvg` / `tvg-url`。"""
    urls: list = []
    for line in list(getattr(document, "header_lines", []) or []):
        if not line.strip().upper().startswith("#EXTM3U"):
            continue
        for match in re.finditer(r"(?:x-tvg-url|url-tvg|tvg-url)\s*=\s*\"([^\"]+)\"", line, re.I):
            for part in re.split(r"[,\s]+", match.group(1)):
                part = part.strip()
                if part and part not in urls:
                    urls.append(part)
    return urls


def m3ule_logo_fetch_text_source(url, requests_module=None,
                                 timeout: int = M3ULE_LOGO_FETCH_TIMEOUT,
                                 stop_cb=None) -> tuple:
    """抓一个台标来源（m3u / XMLTV）：返回 (文本或 None, 说明)。

    带大小上限与取消支持；`Content-Encoding: gzip` 由 requests 自动解开，
    另有裸 gzip（`.xml.gz`）兜底。
    """
    requests_module = requests_module or m3ule_get_requests_module()
    if not requests_module:
        return None, "缺少 requests 库，无法联网读取"
    try:
        response = requests_module.get(
            url, timeout=timeout, stream=True,
            headers={"User-Agent": M3ULE_DEFAULT_USER_AGENT})
    except Exception as exc:  # noqa: BLE001
        return None, f"无法访问：{type(exc).__name__}: {exc}"
    total = 0
    try:
        status = int(getattr(response, "status_code", 0) or 0)
        if status != 200:
            return None, f"HTTP {status}"
        chunks: list = []
        for chunk in response.iter_content(65536):
            if stop_cb is not None and stop_cb():
                return None, "已取消"
            if not chunk:
                continue
            chunks.append(chunk)
            total += len(chunk)
            if total >= M3ULE_LOGO_FETCH_LIMIT:
                break
        raw = b"".join(chunks)
    except Exception as exc:  # noqa: BLE001
        return None, f"读取失败：{type(exc).__name__}: {exc}"
    finally:
        try:
            response.close()
        except Exception:
            pass
    if raw[:2] == b"\x1f\x8b":
        try:
            raw = gzip.decompress(raw)
        except Exception:
            pass
    text, _encoding = M3ULiveEditorDocument.doc_decode_bytes(raw)
    size_text = f"{total / 1048576:.1f} MB" if total >= 1048576 else f"{total} 字节"
    note = f"读到 {size_text}"
    if total >= M3ULE_LOGO_FETCH_LIMIT:
        note += "（已到读取上限，只解析前一段）"
    return text, note


def m3ule_logo_map_csv_rows(records) -> list:
    """台标库的 CSV 行（表头 + 数据）。"""
    rows = [["频道名", "台标地址", "来源", "命中次数", "更新时间"]]
    for record in list(records or []):
        rows.append([record.get("name", ""), record.get("logo", ""), record.get("source", ""),
                     record.get("hits", ""), record.get("updated_at", "")])
    return rows


def m3ule_logo_map_parse_csv(text: str) -> list:
    """解析台标库 CSV：支持带表头，也支持纯「频道名, 台标地址」两列。"""
    raw_rows = [row for row in csv.reader((text or "").splitlines())
                if any((cell or "").strip() for cell in row)]
    if not raw_rows:
        return []
    name_index, logo_index, source_index = 0, 1, 2
    body = raw_rows
    header = [(cell or "").strip().lower() for cell in raw_rows[0]]
    if any("频道" in cell or "name" in cell for cell in header):
        body = raw_rows[1:]
        for index, cell in enumerate(header):
            if "频道" in cell or "name" in cell:
                name_index = index
            elif "台标" in cell or "logo" in cell or "icon" in cell:
                logo_index = index
            elif "来源" in cell or "source" in cell:
                source_index = index
    output: list = []
    for row in body:
        if len(row) <= max(name_index, logo_index):
            continue
        name = (row[name_index] or "").strip()
        logo = (row[logo_index] or "").strip()
        source = (row[source_index] or "").strip() if len(row) > source_index else ""
        key = m3ule_logo_key(name)
        if key and logo:
            output.append({"name_key": key, "name": name, "logo": logo, "source": source})
    return output


def m3ule_sync_mode_is_rebuild(mode: str) -> bool:
    """同步方式是不是「整表替换（用来源重建，旧频道清除）」。"""
    return (mode or "").strip() == M3ULE_SYNC_MODES[1]


def m3ule_sync_channel_id_prefix(entries, fallback: str = "") -> str:
    """从目标文件里认出 channelID 的写法前缀：`x-ID.129` → `x-ID.`。

    全部 channelID 都是纯数字时返回 fallback（默认空串，表示「编号直接当 channelID」）。
    """
    counter: dict = {}
    for entry in (entries or []):
        value = (entry.entry_get_attr("channelID") or "").strip()
        match = re.match(r"^(.*?)(\d+)$", value) if value else None
        if match and match.group(1):
            counter[match.group(1)] = counter.get(match.group(1), 0) + 1
    if not counter:
        return (fallback or "").strip()
    return max(counter, key=lambda item: counter[item])


def m3ule_sync_index_attrs(prefix: str, number: int) -> "OrderedDict[str, str]":
    """编号 → channelID / 频道号(tvg-chno) / tvg-id 三个字段（都跟着链接里的编号走）。"""
    digits = str(int(number))
    attrs: "OrderedDict[str, str]" = OrderedDict()
    attrs["channelID"] = f"{prefix or ''}{digits}"
    attrs["tvg-chno"] = digits
    attrs["tvg-id"] = digits
    return attrs


def m3ule_sync_entry_attr_changes(entry, name: str, number: int, prefix: str,
                                 options=None) -> "OrderedDict[str, str]":
    """算出目标里某条同频道名要改写的字段（值 = 新值；`@title` 表示标题）。

    只算「真的不一样」的字段，界面上就能一眼看出这条会不会被改。
    """
    opts = dict(options or {})
    write_name = bool(opts.get("write_tvg_name", True))
    write_title = bool(opts.get("write_title", True))
    write_ids = bool(opts.get("write_ids", True))
    title_mode = str(opts.get("new_title_mode") or M3ULE_SYNC_NEW_TITLE_MODES[0])
    width = m3ule_safe_int(opts.get("pad_width"), 0)
    changes: "OrderedDict[str, str]" = OrderedDict()
    if write_ids:
        for key, value in m3ule_sync_index_attrs(prefix, number).items():
            if (entry.entry_get_attr(key) or "").strip() != value:
                changes[key] = value
    if name and write_name:
        if (entry.entry_get_attr("tvg-name") or "").strip() != name:
            changes["tvg-name"] = name
    if name and write_title:
        new_title = (f"[{m3ule_sync_pad_number(number, width)}] {name}"
                     if title_mode == M3ULE_SYNC_NEW_TITLE_MODES[1] else name)
        if (entry.title or "").strip() != new_title:
            changes["@title"] = new_title
    return changes


def m3ule_sync_change_texts(changes) -> list:
    """把字段改动转成给人看的文字（预览「说明」列用）。"""
    texts: list = []
    for key, value in (changes or {}).items():
        if key == "@title":
            texts.append(f"标题→{value}")
        else:
            texts.append(f"{key}→{value}")
    return texts


def m3ule_sync_source_channels(source_entries, states=None, options=None) -> dict:
    """把来源整理成「重建目标文件」要写入的频道列表（保持来源顺序）。

    · 跳过并列出：链接里没有编号、已确认无信号（可关）、编号重复；
    · 只有编号没有名称的条目（如 `[048]`）：默认**照样写入**（标题写成 `[048]`，稍后补名字），
      关掉 keep_unnamed 才跳过；
    · states：{链接规范化键: True 有信号 / False 无信号 / None 未测}，用于「跳过已确认无信号」
    · options：skip_dead / keep_unnamed / template + pad_width（来源没有链接时按目标模板拼地址）/
      named_pairs
    """
    opts = dict(options or {})
    skip_dead = bool(opts.get("skip_dead", True))
    keep_unnamed = bool(opts.get("keep_unnamed", True))
    template = str(opts.get("template") or "")
    width = m3ule_safe_int(opts.get("pad_width"), 0)
    state_table = dict(states or {})
    channels: list = []
    skipped: list = []
    used_numbers: dict = {}

    def add_row(name: str, number, url: str, logo: str, source_title: str, uid=None) -> None:
        clean = (name or "").strip()
        if number is None:
            skipped.append({"name": clean or "(没有名称)", "number": None, "uid": uid,
                            "reason": "链接里没有编号，无法确定 channelID / 频道号，不写入"})
            return
        number = int(number)
        if not clean and not keep_unnamed:
            skipped.append({"name": "(没有名称)", "number": number, "uid": uid,
                            "reason": f"来源里编号 {m3ule_sync_pad_number(number, width)} "
                                      "只有编号没有名称（待确认），按设置不写入"})
            return
        if skip_dead and state_table.get(m3ule_probe_cache_key(url or "")) is False:
            skipped.append({"name": clean or f"[{m3ule_sync_pad_number(number, width)}]",
                            "number": number, "uid": uid,
                            "reason": "已确认无信号（数据库里最新结果是失败/无节目），跳过"})
            return
        if number in used_numbers:
            skipped.append({"name": clean or f"[{m3ule_sync_pad_number(number, width)}]",
                            "number": number, "uid": uid,
                            "reason": f"编号 {m3ule_sync_pad_number(number, width)} 已由"
                                      f"「{used_numbers[number]}」占用（同一编号只保留一个），跳过"})
            return
        final_url = url or ""
        if not final_url and template:
            final_url = m3ule_sync_url_from_template(template, number, width)
        used_numbers[number] = clean or f"[{m3ule_sync_pad_number(number, width)}]"
        channels.append({
            "name": clean, "number": number,
            "number_text": m3ule_sync_pad_number(number, width),
            "url": final_url, "logo": (logo or "").strip(),
            "source_title": source_title or "", "uid": uid,
            "unnamed": not clean,
            "placeholder": (source_title or "").strip() if not clean else "",
        })

    for entry in (source_entries or []):
        names = m3ule_sync_entry_names(entry)
        add_row(names[0] if names else "", m3ule_sync_entry_index(entry),
                entry.url or "", entry.entry_get_attr("tvg-logo") or "",
                entry.title or "", getattr(entry, "uid", None))
    for pair in (opts.get("named_pairs") or []):
        name = pair.get("name") if isinstance(pair, dict) else pair[0]
        number = pair.get("number") if isinstance(pair, dict) else pair[1]
        add_row(name, number, (pair.get("url") if isinstance(pair, dict) else "") or "",
                (pair.get("logo") if isinstance(pair, dict) else "") or "", "", None)
    return {"channels": channels, "skipped": skipped}


def m3ule_sync_plan(source_entries, target_entries, options=None) -> dict:
    """算出同步计划（纯函数，便于测试与预览）：

    · updates  ：目标里同名频道要改的字段（链接编号、标题里的 `[NNN]`、channelID / 频道号 /
      tvg-id / tvg-name 等，只列真正不一样的）
    · same     ：目标里同名、什么都不用改
    · adds     ：源里确认过、目标里没有的名字 → 追加（分组留空）
    · mode=整表替换（rebuild）：以来源频道列表重建目标文件的频道区（旧频道清除、
      同名频道沿用原分组与台标），`rebuild` 给要写入的频道、`removes` 给要删掉的旧频道
    · conflicts：源里同名对应多个编号，且目标里真的有这个名字 → 不自动改
    · no_index ：目标链接里没有编号参数 → 无法安全改写，保持原样
    · unmatched：目标里找不到同名频道 → 保持原样（并尽量说明「校对文件里那个编号是什么」）
    """
    opts = dict(options or {})
    match = {
        "ignore_case": bool(opts.get("ignore_case", True)),
        "ignore_space": bool(opts.get("ignore_space", True)),
    }
    confirmed = m3ule_sync_build_confirmed(
        entries=opts.get("confirmed_entries", source_entries),
        remarks=opts.get("remarks"), match=match)
    source_numbers = m3ule_sync_source_index_names(source_entries)
    template_info = m3ule_sync_dominant_template(target_entries)
    target_names = [name for entry in (target_entries or [])
                    for name in m3ule_sync_entry_names(entry)]
    width = m3ule_safe_int(opts.get("pad_width"), template_info["width"])
    duration = str(opts.get("new_duration") or m3ule_sync_dominant_duration(target_entries))
    new_title_mode = str(opts.get("new_title_mode") or M3ULE_SYNC_NEW_TITLE_MODES[0])
    id_prefix = str(opts.get("id_prefix") or "").strip()
    prefix_info = {"prefix": id_prefix or m3ule_sync_channel_id_prefix(target_entries),
                   "auto": not bool(id_prefix)}
    attr_options = {
        "write_tvg_name": bool(opts.get("write_tvg_name", True)),
        "write_title": bool(opts.get("write_title", True)),
        "write_ids": bool(opts.get("write_ids", True)),
        "new_title_mode": new_title_mode,
        "pad_width": width,
    }
    plan = {
        "updates": [], "same": [], "adds": [], "conflicts": [], "no_index": [],
        "unmatched": [], "warnings": [], "add_conflicts": [],
        "template": template_info["template"], "template_count": template_info["count"],
        "pad_width": width, "duration": duration, "match": match,
        "confirmed_count": confirmed["count"], "confirmed_conflicts": confirmed["conflicts"],
        "new_group": str(opts.get("new_group") or ""),
        "mode": (M3ULE_SYNC_MODES[1] if m3ule_sync_mode_is_rebuild(
            str(opts.get("mode") or "")) else M3ULE_SYNC_MODES[0]),
        "rebuild": {"channels": [], "skipped": [], "kept_meta": 0, "fresh": 0, "unnamed": 0},
        "removes": [], "id_prefix": prefix_info["prefix"], "id_prefix_auto": prefix_info["auto"],
        "source_entries": list(source_entries or []),
        "target_entries": list(target_entries or []),
        "attr_options": attr_options,
    }
    if m3ule_sync_mode_is_rebuild(plan["mode"]):
        m3ule_sync_plan_rebuild(plan, opts, confirmed, template_info, duration, attr_options)
        plan["stats"] = m3ule_sync_plan_summary(plan)
        return plan
    matched_keys: set = set()
    final_numbers: dict = {}
    for position, entry in enumerate(target_entries or []):
        names = m3ule_sync_entry_names(entry)
        record = None
        for name in names:
            key = m3ule_sync_normalize_name(
                name, match["ignore_case"], match["ignore_space"])
            if key and key in confirmed["names"]:
                record = confirmed["names"][key]
                matched_keys.add(key)
                break
        row = {
            "position": position, "uid": getattr(entry, "uid", None),
            "name": (names[0] if names else (entry.title or "").strip()),
            "old_number": m3ule_sync_entry_index(entry), "old_url": entry.url or "",
            "group": entry.entry_effective_group(), "extinf": entry.extinf_raw,
            "old_channel_id": (entry.entry_get_attr("channelID") or "").strip(),
        }
        if record is None:
            row["source_names"] = source_numbers.get(row["old_number"]) if row["old_number"] is not None else None
            plan["unmatched"].append(row)
            if row["old_number"] is not None:
                final_numbers.setdefault(int(row["old_number"]), []).append(row["name"])
            continue
        if record["conflict"]:
            row["candidates"] = record["numbers"]
            plan["conflicts"].append(row)
            if row["old_number"] is not None:
                final_numbers.setdefault(int(row["old_number"]), []).append(row["name"])
            continue
        new_number = int(record["number"])
        row["new_number"] = new_number
        row["confirmed_name"] = record["name"] or row["name"]
        row["index_attrs"] = m3ule_sync_index_attrs(plan["id_prefix"], new_number)
        row["channel_id"] = row["index_attrs"]["channelID"]
        final_numbers.setdefault(new_number, []).append(row["name"])
        if row["old_number"] is None:
            plan["no_index"].append(row)
            continue
        row["new_extinf"] = m3ule_sync_retitle_index(row["extinf"], new_number, width)
        # 更新时按「该链接自身原来的位数」补零：不同模板的链接未必和主流模板位数一样
        row["new_url"] = m3ule_sync_url_with_index(row["old_url"], new_number, 0)
        row["number_changed"] = int(row["old_number"]) != new_number
        if not row["number_changed"]:
            row["new_url"] = row["old_url"]
        row["changes"] = m3ule_sync_entry_attr_changes(
            entry, row["confirmed_name"], new_number, plan["id_prefix"], attr_options)
        if row["number_changed"] or row["new_extinf"] or row["changes"]:
            plan["updates"].append(row)
            continue
        plan["same"].append(row)

    if bool(opts.get("add_missing", True)):
        for key, record in confirmed["names"].items():
            if key in matched_keys:
                continue
            if record["conflict"]:
                # 同名对应多个编号：不猜，列出来让用户先修校对文件
                plan["add_conflicts"].append({
                    "name": record["name"] or key, "numbers": record["numbers"]})
                continue
            name = record["name"] or key
            number = int(record["number"])
            template = template_info["template"]
            title = (f"[{m3ule_sync_pad_number(number, width)}] {name}"
                     if new_title_mode == M3ULE_SYNC_NEW_TITLE_MODES[1] else name)
            index_attrs = (m3ule_sync_index_attrs(plan["id_prefix"], number)
                           if attr_options["write_ids"] else OrderedDict())
            plan["adds"].append({
                "name": name, "number": number,
                "number_text": m3ule_sync_pad_number(number, width),
                "url": m3ule_sync_url_from_template(template, number, width) if template else "",
                "group": plan["new_group"], "duration": duration, "title": title,
                "tvg_name": name if opts.get("new_tvg_name", True) else "",
                "index_attrs": index_attrs, "channel_id": index_attrs.get("channelID", ""),
                "template": template,
                "similar": m3ule_sync_similar_names(name, target_names),
            })
            final_numbers.setdefault(number, []).append(name)

    for number in sorted(final_numbers):
        names = [item for item in final_numbers[number] if item]
        if len({m3ule_sync_normalize_name(item, True, True) for item in names}) > 1:
            plan["warnings"].append(
                "编号 %s 同步后会同时被：%s —— 请确认是否有意如此"
                % (m3ule_sync_pad_number(number, width), "、".join(f"「{item}」" for item in names)))
    m3ule_sync_plan_channel_id_warnings(plan)
    plan["stats"] = m3ule_sync_plan_summary(plan)
    return plan


def m3ule_sync_plan_channel_id_warnings(plan) -> None:
    """channelID 撞车提醒：新生成的 channelID 不能和「本次没被同步的频道」重复。"""
    plan = plan or {}
    generated: dict = {}
    for row in (plan.get("updates") or []) + (plan.get("adds") or []):
        channel_id = str(row.get("channel_id") or "").strip()
        if channel_id:
            generated.setdefault(channel_id, []).append(row.get("name") or "")
    if not generated:
        return
    clashes: dict = {}
    for row in ((plan.get("unmatched") or []) + (plan.get("conflicts") or [])
                + (plan.get("no_index") or [])):
        channel_id = str(row.get("old_channel_id") or "").strip()
        if channel_id and channel_id in generated:
            clashes.setdefault(channel_id, []).append(row.get("name") or "")
    for channel_id, names in sorted(clashes.items()):
        plan.setdefault("warnings", []).append(
            "channelID「%s」会和本次没同步的频道 %s 重复 —— 请确认是否有意如此"
            % (channel_id, "、".join(f"「{item}」" for item in names)))


def m3ule_sync_plan_rebuild(plan, opts, confirmed, template_info, duration,
                            attr_options) -> None:
    """「整表替换」计划：以来源频道列表重建目标文件的频道区。

    · 写入顺序 = 来源文件里的顺序（校对顺序）；旧文件里**不在新列表里的频道全部删除**；
    · 同名频道沿用原来的 group-title（分组）与 tvg-logo（台标）——台标跟着频道走，
      不因编号变化而丢；
    · channelID / 频道号(tvg-chno) / tvg-id 一律对应该链接里的编号，名称写入 tvg-name 与标题；
    · 来源里没有名称 / 没有编号 / 已确认无信号 / 编号重复的条目会**跳过并列出来**。
    """
    target_entries = plan["target_entries"]
    match = plan["match"]
    keep_meta = bool(opts.get("keep_meta", True))
    skip_dead = bool(opts.get("skip_dead", True))
    keep_unnamed = bool(opts.get("keep_unnamed", True))
    width = plan["pad_width"]
    title_mode = attr_options["new_title_mode"]

    target_index: dict = {}
    target_by_number: dict = {}
    for position, entry in enumerate(target_entries):
        for name in m3ule_sync_entry_names(entry):
            key = m3ule_sync_normalize_name(name, match["ignore_case"], match["ignore_space"])
            if key and key not in target_index:
                target_index[key] = position
        number = m3ule_sync_entry_index(entry)
        if number is not None and int(number) not in target_by_number:
            target_by_number[int(number)] = position

    source_rows = m3ule_sync_source_channels(
        opts.get("confirmed_entries", plan.get("source_entries")),
        states=opts.get("states"), options={
            "skip_dead": skip_dead, "keep_unnamed": keep_unnamed,
            "template": template_info["template"],
            "pad_width": width, "named_pairs": opts.get("named_pairs"),
        })
    plan["rebuild"]["skipped"] = source_rows["skipped"]
    matched_positions: set = set()
    final_numbers: dict = {}
    for channel in source_rows["channels"]:
        name = channel["name"]
        unnamed = bool(channel.get("unnamed"))
        number = int(channel["number"])
        key = (m3ule_sync_normalize_name(name, match["ignore_case"], match["ignore_space"])
               if name else "")
        position = target_index.get(key) if key else None
        old_entry = target_entries[position] if position is not None else None
        placeholder = channel.get("placeholder") or f"[{channel['number_text']}]"
        # 只有编号没有名称：没法确认旧文件里哪条是同一个台，所以只提示、不沿用分组与台标
        same_index_entry = None
        if old_entry is None and unnamed:
            index_position = target_by_number.get(number)
            if index_position is not None:
                same_index_entry = target_entries[index_position]
        row = {
            "name": name or placeholder, "number": number,
            "number_text": channel["number_text"],
            "old_number": m3ule_sync_entry_index(old_entry) if old_entry is not None else None,
            "old_url": (old_entry.url or "") if old_entry is not None else "",
            "position": position, "uid": channel.get("uid"),
            "url": channel["url"] or (m3ule_sync_url_from_template(
                template_info["template"], number, width) if template_info["template"] else ""),
            "duration": duration,
            "title": ((f"[{m3ule_sync_pad_number(number, width)}] {name}"
                       if title_mode == M3ULE_SYNC_NEW_TITLE_MODES[1] else name)
                      if name else placeholder),
            "source_title": channel.get("source_title") or "",
            "tvg_name": name if (attr_options["write_tvg_name"] and name) else "",
            "unnamed": unnamed, "placeholder": placeholder,
            "same_index_name": (same_index_entry.entry_effective_name()
                                or (same_index_entry.title or "").strip())
            if same_index_entry is not None else "",
            "old_group": old_entry.entry_effective_group() if old_entry is not None else "",
            "old_logo": (old_entry.entry_get_attr("tvg-logo") or "")
            if old_entry is not None else "",
            "old_title": (old_entry.title or "") if old_entry is not None else "",
            "old_channel_id": (old_entry.entry_get_attr("channelID") or "")
            if old_entry is not None else "",
        }
        row["index_attrs"] = m3ule_sync_index_attrs(plan["id_prefix"], number)
        row["channel_id"] = row["index_attrs"]["channelID"]
        row["group"] = (row["old_group"] if (keep_meta and old_entry is not None)
                        else plan["new_group"])
        row["logo"] = (row["old_logo"] if (keep_meta and old_entry is not None)
                       else channel.get("logo") or "")
        row["reused_meta"] = bool(keep_meta and old_entry is not None
                                  and (row["old_group"] or row["old_logo"]))
        if old_entry is not None:
            matched_positions.add(position)
            if row["reused_meta"]:
                plan["rebuild"]["kept_meta"] += 1
        else:
            plan["rebuild"]["fresh"] += 1
        if unnamed:
            plan["rebuild"]["unnamed"] += 1
        plan["rebuild"]["channels"].append(row)
        if row["old_number"] is not None and int(row["old_number"]) != number:
            row["number_changed"] = True
        final_numbers.setdefault(number, []).append(row["name"])

    for position, entry in enumerate(target_entries):
        if position in matched_positions:
            continue
        plan["removes"].append({
            "position": position, "uid": getattr(entry, "uid", None),
            "name": entry.entry_effective_name() or (entry.title or "").strip(),
            "old_number": m3ule_sync_entry_index(entry), "old_url": entry.url or "",
            "group": entry.entry_effective_group(),
        })

    for number in sorted(final_numbers):
        names = [item for item in final_numbers[number] if item]
        if len({m3ule_sync_normalize_name(item, True, True) for item in names}) > 1:
            plan["warnings"].append(
                "编号 %s 会被多条频道使用：%s —— 请确认是否有意如此"
                % (m3ule_sync_pad_number(number, width), "、".join(f"「{item}」" for item in names)))
    names_counter: dict = {}
    for channel in plan["rebuild"]["channels"]:
        if channel.get("unnamed"):
            continue
        names_counter.setdefault(
            m3ule_sync_normalize_name(channel["name"], True, True), []).append(channel["name"])
    for names in names_counter.values():
        if len(names) > 1:
            plan["warnings"].append(
                "来源里有多个同名频道「%s」（%d 条）—— 会写多份，请确认" % (names[0], len(names)))
    if plan["rebuild"]["unnamed"]:
        plan["warnings"].append(
            "来源里有 %d 条只有编号没有名称（会照样写入，标题写成 [编号]，"
            "tvg-name 留空）—— 建议后续在校对文件里补齐名称，补齐后再同步一次即可"
            % plan["rebuild"]["unnamed"])
    if plan["removes"]:
        plan["warnings"].append(
            "整表替换会删除目标文件里 %d 条旧频道（不在新列表里的）—— 写盘前会自动备份"
            % len(plan["removes"]))
    m3ule_sync_plan_channel_id_warnings(plan)


def m3ule_sync_plan_summary(plan) -> dict:
    """计划条数统计（预览摘要与日志用）。"""
    plan = plan or {}
    rebuild = plan.get("rebuild") or {}
    return {
        "update": len(plan.get("updates") or []),
        "same": len(plan.get("same") or []),
        "add": len(plan.get("adds") or []),
        "unmatched": len(plan.get("unmatched") or []),
        "conflict": len(plan.get("conflicts") or []),
        "no_index": len(plan.get("no_index") or []),
        "warning": len(plan.get("warnings") or []),
        "add_conflict": len(plan.get("add_conflicts") or []),
        "remove": len(plan.get("removes") or []),
        "skip": len(rebuild.get("skipped") or []),
        "write": len(rebuild.get("channels") or []),
        "kept_meta": m3ule_safe_int(rebuild.get("kept_meta"), 0),
        "fresh": m3ule_safe_int(rebuild.get("fresh"), 0),
        "unnamed": m3ule_safe_int(rebuild.get("unnamed"), 0),
        "rebuild": 1 if m3ule_sync_mode_is_rebuild(str(plan.get("mode") or "")) else 0,
    }


def m3ule_sync_skip_reason_counts(plan) -> dict:
    """跳过原因分类统计（摘要里用，让用户知道为什么少了频道）。"""
    counter: dict = {}
    for row in ((plan or {}).get("rebuild") or {}).get("skipped") or []:
        reason = str(row.get("reason") or "其它")
        key = "无名称" if "没有名称" in reason else (
            "无编号" if "没有编号" in reason else (
                "无信号" if "无信号" in reason else (
                    "编号重复" if "占用" in reason else "其它")))
        counter[key] = counter.get(key, 0) + 1
    return counter


def m3ule_sync_summary_text(plan) -> str:
    """一句话摘要（预览区与日志共用，保证口径一致）。"""
    stats = m3ule_sync_plan_summary(plan)
    if stats["rebuild"]:
        parts = [f"整表替换：写入 {stats['write']} 条频道"
                 f"（沿用原分组/台标 {stats['kept_meta']} 条、新增 {stats['fresh']} 条）"]
        if stats["unnamed"]:
            parts.append(f"其中名称待确认 {stats['unnamed']} 条（标题写成 [编号]）")
        parts.append(f"删除旧频道 {stats['remove']} 条")
        if stats["skip"]:
            counts = m3ule_sync_skip_reason_counts(plan)
            detail = " / ".join(f"{key} {counts[key]}" for key in
                                ("无信号", "无编号", "无名称", "编号重复", "其它") if counts.get(key))
            parts.append(f"跳过 {stats['skip']} 条（{detail}）")
        parts.append("写盘前会自动备份目标文件")
        return "；".join(parts)
    parts = [f"将更新 {stats['update']} 条", f"新增 {stats['add']} 条",
             f"已一致 {stats['same']} 条"]
    if stats["conflict"]:
        parts.append(f"冲突 {stats['conflict']} 条（不改）")
    if stats["add_conflict"]:
        parts.append(f"无法新增 {stats['add_conflict']} 条（源里同名多编号）")
    if stats["no_index"]:
        parts.append(f"链接无编号 {stats['no_index']} 条（不改）")
    parts.append(f"未匹配 {stats['unmatched']} 条（保持原样）")
    return "；".join(parts)


def m3ule_sync_unmatched_note(row) -> str:
    """未匹配行的说明：尽量告诉用户「校对文件里那个编号是什么」，方便下一步修改。"""
    names = row.get("source_names")
    if names is None:
        return "校对文件里没有同名频道，保持原样"
    filled = [item for item in names if item]
    if not filled:
        return "校对文件里这个编号还没有填名称，保持原样"
    return ("校对文件里这个编号是「%s」，与本条名字不同，保持原样"
            % "、".join(filled[:3]))


def m3ule_sync_plan_rows(plan) -> list:
    """预览表格的行：动作 / 频道名 / 原编号 / 新编号 / 说明 / 地址。"""
    plan = plan or {}
    rows: list = []
    width = int(plan.get("pad_width") or 0)
    rebuild = m3ule_sync_mode_is_rebuild(str(plan.get("mode") or ""))

    def number_text(value):
        if value is None or value == "":
            return ""
        return m3ule_sync_pad_number(int(value), width)

    if rebuild:
        for row in (plan.get("rebuild") or {}).get("channels") or []:
            changed = "编号 %s→%s" % (number_text(row.get("old_number")),
                                     number_text(row.get("number"))) if row.get("number_changed") \
                else "编号 " + number_text(row.get("number"))
            if row.get("position") is not None:
                note = (f"整表替换：{changed}；channelID→{row['index_attrs']['channelID']}、"
                        f"频道号→{row['index_attrs']['tvg-chno']}、tvg-id→{row['index_attrs']['tvg-id']}、"
                        f"名称→{row['name']}")
                if row.get("group"):
                    note += f"；沿用分组「{row['group']}」"
                if row.get("logo"):
                    note += "；沿用台标"
                if not row.get("group") and not row.get("logo"):
                    note += "；旧文件里没有同名频道，分组留空（可稍后自行分组）"
                rows.append([M3ULE_SYNC_ACTION_UPDATE, row["name"],
                             number_text(row.get("old_number")), number_text(row.get("number")),
                             note, row.get("url", "")])
            else:
                note = (f"整表替换：新增（旧文件里没有同名频道）；channelID→"
                        f"{row['index_attrs']['channelID']}、频道号→{row['index_attrs']['tvg-chno']}、"
                        f"tvg-id→{row['index_attrs']['tvg-id']}")
                if row.get("unnamed"):
                    note = (f"整表替换：名称待确认（只有编号，标题写成 {row.get('placeholder')}，"
                            f"tvg-name 留空）；channelID→{row['index_attrs']['channelID']}、"
                            f"频道号→{row['index_attrs']['tvg-chno']}、tvg-id→"
                            f"{row['index_attrs']['tvg-id']}")
                    if row.get("same_index_name"):
                        note += (f"；旧文件里这个编号是「{row['same_index_name']}」，"
                                 "名字没填之前不沿用它的分组与台标（避免张冠李戴）")
                    else:
                        note += "；分组留空（可稍后自行分组）"
                elif row.get("logo"):
                    note += "；带上来源里的台标"
                else:
                    note += "；分组留空（可稍后自行分组）"
                rows.append([M3ULE_SYNC_ACTION_ADD, row["name"], "",
                             number_text(row.get("number")), note, row.get("url", "")])
        for row in (plan.get("rebuild") or {}).get("skipped") or []:
            rows.append([M3ULE_SYNC_ACTION_SKIP, row.get("name") or "",
                         number_text(row.get("number")), "",
                         "整表替换：不写入 —— " + str(row.get("reason") or ""), ""])
        for row in (plan.get("removes") or []):
            rows.append([M3ULE_SYNC_ACTION_REMOVE, row.get("name") or "",
                         number_text(row.get("old_number")), "",
                         "旧文件里的频道不在新列表里，会被清除"
                         + (f"（原分组「{row['group']}」）" if row.get("group") else ""),
                         row.get("old_url", "")])
        order = {name: index for index, name in enumerate(M3ULE_SYNC_ACTION_ORDER)}
        rows.sort(key=lambda item: order.get(item[0], len(order)))
        return rows

    for row in (plan.get("updates") or []):
        note = "只改链接里的编号，其它信息不动" if row.get("number_changed") else "编号已经一致"
        if row.get("number_changed") and row.get("new_extinf"):
            note += "；标题里的 [编号] 也一并更新"
        change_texts = m3ule_sync_change_texts(row.get("changes"))
        if change_texts:
            note += "；同时更新 " + "、".join(change_texts)
        rows.append([M3ULE_SYNC_ACTION_UPDATE, row["name"], number_text(row.get("old_number")),
                     number_text(row.get("new_number")), note, row.get("new_url", "")])
    for row in (plan.get("adds") or []):
        note = "目标文件里没有这个频道，追加到末尾"
        note += (f"（分组：{row['group']}）" if row.get("group") else "（分组留空，可稍后自行分组）")
        index_attrs = row.get("index_attrs") or {}
        if index_attrs:
            note += "；channelID→%s、频道号→%s、tvg-id→%s" % (
                index_attrs.get("channelID", ""), index_attrs.get("tvg-chno", ""),
                index_attrs.get("tvg-id", ""))
        if row.get("similar"):
            note += "；注意目标里已有相似频道「%s」，若要合并请先统一名字" % "、".join(row["similar"])
        rows.append([M3ULE_SYNC_ACTION_ADD, row["name"], "", row.get("number_text", ""),
                     note, row.get("url", "")])
    for row in (plan.get("conflicts") or []):
        rows.append([M3ULE_SYNC_ACTION_CONFLICT, row["name"], number_text(row.get("old_number")), "",
                     "校对文件里同名对应多个编号：" + "、".join(
                         str(m3ule_sync_pad_number(item, width)) for item in row.get("candidates") or [])
                     + "（不自动改，请先在校对文件里确认）", row.get("old_url", "")])
    for row in (plan.get("add_conflicts") or []):
        rows.append([M3ULE_SYNC_ACTION_CONFLICT, row["name"], "", "",
                     "校对文件里同名对应多个编号：" + "、".join(
                         str(m3ule_sync_pad_number(item, width)) for item in row.get("numbers") or [])
                     + "（未新增，请先在校对文件里确认）", ""])
    for row in (plan.get("no_index") or []):
        rows.append([M3ULE_SYNC_ACTION_NO_INDEX, row["name"], number_text(row.get("old_number")),
                     number_text(row.get("new_number")), "目标文件的链接里没有编号参数，未改动",
                     row.get("old_url", "")])
    for row in (plan.get("unmatched") or []):
        rows.append([M3ULE_SYNC_ACTION_UNMATCHED, row["name"], number_text(row.get("old_number")), "",
                     m3ule_sync_unmatched_note(row), row.get("old_url", "")])
    for row in (plan.get("same") or []):
        rows.append([M3ULE_SYNC_ACTION_SAME, row["name"], number_text(row.get("old_number")),
                     number_text(row.get("new_number")), "编号已经一致，无需改动", row.get("old_url", "")])
    order = {name: index for index, name in enumerate(M3ULE_SYNC_ACTION_ORDER)}
    rows.sort(key=lambda item: order.get(item[0], len(order)))
    return rows


def m3ule_sync_compose_attrs(index_attrs=None, tvg_name: str = "", logo: str = "",
                            group: str = "") -> "OrderedDict[str, str]":
    """按目标文件常见顺序拼 #EXTINF 属性：channelID / 频道号 / tvg-name / tvg-id / tvg-logo / 分组。"""
    attrs: "OrderedDict[str, str]" = OrderedDict()
    for key in ("channelID", "tvg-chno", "tvg-name", "tvg-id", "tvg-logo", "group-title"):
        value = ""
        if index_attrs and key in index_attrs:
            value = index_attrs[key]
        elif key == "tvg-name":
            value = tvg_name
        elif key == "tvg-logo":
            value = logo
        elif key == "group-title":
            value = group
        if str(value).strip():
            attrs[key] = str(value).strip()
    return attrs


def m3ule_sync_rebuild_entry_lines(row) -> str:
    """按整表替换的规则拼一条全新的 `#EXTINF`（channelID / 频道号 / tvg-id / 名称 / 台标 / 分组）。"""
    attrs = m3ule_sync_compose_attrs(
        row.get("index_attrs"), row.get("tvg_name") or "", row.get("logo") or "",
        row.get("group") or "")
    return m3ule_format_extinf_line(
        str(row.get("duration") or "0"), attrs, row.get("title") or row.get("name") or "")


def m3ule_sync_keep_lines(document) -> list:
    """整表替换时保留哪些非频道行：文件头之后的注释行（去重）+ 一个空行（原来就有的话）。

    旧文件的注释（例如 `#EXTM3U x-tvg-url=…` 之外的说明）不会被丢掉，
    重复出现的同一行注释只保留一条；空行只在原来有分隔空行时补一个。
    """
    comments: list = []
    blank = False
    for entry in (document.entries or []):
        for line in list(entry.pre_lines) + list(entry.between_lines):
            stripped = line.strip()
            if not stripped:
                blank = True
                continue
            if stripped.startswith("#") and not stripped[:7].upper() == "#EXTINF":
                if line not in comments:
                    comments.append(line)
    kept: list = list(comments)
    if blank:
        kept.append("")
    return kept


def m3ule_sync_apply_plan(document, plan, progress=None) -> dict:
    """把计划应用到目标文档。

    · 只更新编号（默认）：同名频道只改链接里的编号（必要时连标题里的编号）以及按选项对齐的
      channelID / 频道号 / tvg-id / tvg-name 字段 —— 分组、台标、其它字段与注释行一律不动；
    · 整表替换：清空旧频道，按来源顺序写入新频道（同名频道沿用原分组与台标）。
    """
    plan = plan or {}
    if m3ule_sync_mode_is_rebuild(str(plan.get("mode") or "")):
        return m3ule_sync_apply_rebuild(document, plan, progress)
    updates = plan.get("updates") or []
    adds = plan.get("adds") or []
    total = max(1, len(updates) + len(adds))
    done = 0
    changed = 0
    entries = document.entries
    for row in updates:
        position = m3ule_safe_int(row.get("position"), -1)
        if 0 <= position < len(entries):
            entry = entries[position]
            new_extinf = row.get("new_extinf")
            if new_extinf:
                entry.extinf_raw = new_extinf
                entry.entry_parse_from_raw()
            if row.get("new_url"):
                entry.url = row["new_url"]
                entry.entry_invalidate_test_if_url_changed(entry.url)
            m3ule_sync_apply_entry_changes(entry, row.get("changes"))
            changed += 1
        done += 1
        if progress:
            progress(int(done * 100 / total), f"正在更新编号 {done}/{total}")
    new_entries: list = []
    for row in adds:
        attrs = m3ule_sync_compose_attrs(
            row.get("index_attrs"), row.get("tvg_name") or "", "", row.get("group") or "")
        extinf = m3ule_format_extinf_line(
            str(row.get("duration") or "0"), attrs, row.get("title") or row.get("name") or "")
        new_entries.append(M3ULiveEditorEntry(extinf_raw=extinf, url=row.get("url") or ""))
        done += 1
        if progress:
            progress(int(done * 100 / total), f"正在追加新频道 {done}/{total}")
    if new_entries:
        document.doc_insert_entries(new_entries)
    if changed or new_entries:
        document.modified = True
    return {"updated": changed, "added": len(new_entries), "removed": 0}


def m3ule_sync_apply_entry_changes(entry, changes) -> int:
    """把字段改动写进条目（`@title` 表示标题），返回改了几个字段。"""
    applied = 0
    for key, value in (changes or {}).items():
        if key == "@title":
            entry.title = str(value)
            entry.entry_rebuild_extinf_line()
        else:
            entry.entry_set_attr(key, str(value))
        applied += 1
    return applied


def m3ule_sync_apply_rebuild(document, plan, progress=None) -> dict:
    """整表替换：清空目标文件的频道区，按来源顺序写成新频道（保留文件头 / 注释 / 末尾行）。

    没有可写入的频道时**什么都不做**（绝不把目标文件清空）。
    """
    plan = plan or {}
    rows = (plan.get("rebuild") or {}).get("channels") or []
    if not rows:
        return {"updated": 0, "added": 0, "removed": 0, "written": 0, "kept_lines": 0}
    total = max(1, len(rows) + 1)
    keep_lines = m3ule_sync_keep_lines(document)
    new_entries: list = []
    for index, row in enumerate(rows):
        extinf = m3ule_sync_rebuild_entry_lines(row)
        entry = M3ULiveEditorEntry(extinf_raw=extinf, url=row.get("url") or "")
        if index == 0:
            entry.pre_lines = list(keep_lines)
        new_entries.append(entry)
        if progress:
            progress(int((index + 1) * 100 / total), f"正在重写频道 {index + 1}/{len(rows)}")
    removed = len(document.entries)
    document.entries = list(new_entries)
    document.modified = True
    if progress:
        progress(100, f"已重写 {len(new_entries)} 条频道")
    return {"updated": 0, "added": len(new_entries), "removed": removed,
            "written": len(new_entries), "kept_lines": len(keep_lines)}


def m3ule_sync_plan_csv_rows(plan) -> list:
    """导出预览 CSV 的行（表头 + 明细）。"""
    rows = [["动作", "频道名称", "原编号", "新编号", "说明", "地址"]]
    rows.extend(m3ule_sync_plan_rows(plan))
    return rows


# ----------------------------------------------------------------------------
# 历史数据库（SQLite）
# ----------------------------------------------------------------------------

class M3ULiveEditorHistoryStore:
    """保存测试历史、扫描记录与 ID 备注，保证重启后仍可追溯。"""

    def __init__(self, path: str = ""):
        self.db_path = path or m3ule_get_db_path()
        self.available = False
        self.error = ""
        self._last_error = ""
        self._lock = threading.Lock()
        try:
            m3ule_ensure_dir(os.path.dirname(self.db_path))
            self._connection = sqlite3.connect(self.db_path, check_same_thread=False)
            self._connection.execute("PRAGMA journal_mode=WAL")
            self._create_tables()
            self.available = True
        except Exception as exc:  # noqa: BLE001
            self.error = f"{type(exc).__name__}: {exc}"
            self._connection = None

    def dbh_last_error(self) -> str:
        """最近一次写库失败的描述（空表示没失败过）。

        写库函数以前静默 `return 0`，出问题时完全看不出原因，故保留最近错误供界面/测试诊断。
        """
        return self._last_error

    def _create_tables(self) -> None:
        cursor = self._connection.cursor()
        cursor.execute(
            "CREATE TABLE IF NOT EXISTS test_history ("
            " id INTEGER PRIMARY KEY AUTOINCREMENT,"
            " ts TEXT NOT NULL,"
            " url TEXT, channel TEXT,"
            " state TEXT, http_status INTEGER, ms INTEGER,"
            " kind TEXT, detail TEXT)"
        )
        cursor.execute(
            "CREATE TABLE IF NOT EXISTS scan_runs ("
            " id INTEGER PRIMARY KEY AUTOINCREMENT,"
            " ts TEXT NOT NULL,"
            " template TEXT, start_id INTEGER, end_id INTEGER, step INTEGER,"
            " total INTEGER, alive INTEGER, note TEXT)"
        )
        cursor.execute(
            "CREATE TABLE IF NOT EXISTS id_remarks ("
            " id_key TEXT PRIMARY KEY,"
            " channel_name TEXT, remark TEXT, updated_at TEXT)"
        )
        cursor.execute(
            "CREATE TABLE IF NOT EXISTS logo_map ("
            " name_key TEXT PRIMARY KEY,"
            " name TEXT, logo TEXT, source TEXT,"
            " hits INTEGER DEFAULT 0, updated_at TEXT)"
        )
        cursor.execute(
            "CREATE TABLE IF NOT EXISTS probe_cache ("
            " url_key TEXT PRIMARY KEY,"
            " url TEXT, channel TEXT, source_file TEXT,"
            " state TEXT, level TEXT, has_program INTEGER,"
            " http_status INTEGER, ms INTEGER,"
            " kind TEXT, content_type TEXT, segments INTEGER,"
            " detail TEXT, first_segment TEXT, variant_url TEXT, error TEXT,"
            " payload TEXT,"
            " live_delay_s INTEGER DEFAULT -1, real_kbps INTEGER DEFAULT -1,"
            " stream_id TEXT DEFAULT '', variant_count INTEGER DEFAULT -1,"
            " encrypted INTEGER DEFAULT 0,"
            " checked_at TEXT, first_seen TEXT, last_hit TEXT,"
            " hits INTEGER DEFAULT 0)"
        )
        cursor.execute(
            "CREATE INDEX IF NOT EXISTS idx_probe_cache_checked"
            " ON probe_cache(checked_at)")
        self.dbh_migrate_probe_cache_columns()
        self._connection.commit()

    def dbh_migrate_probe_cache_columns(self) -> None:
        """为旧库补上后续版本新增的列（SQLite 不支持 IF NOT EXISTS 加列）。"""
        wanted = (
            ("live_delay_s", "INTEGER DEFAULT -1"),
            ("real_kbps", "INTEGER DEFAULT -1"),
            ("stream_id", "TEXT DEFAULT ''"),
            ("variant_count", "INTEGER DEFAULT -1"),
            ("encrypted", "INTEGER DEFAULT 0"),
        )
        try:
            existing = {row[1] for row in
                        self._connection.execute("PRAGMA table_info(probe_cache)")}
        except Exception:
            return
        for name, definition in wanted:
            if name in existing:
                continue
            try:
                self._connection.execute(
                    f"ALTER TABLE probe_cache ADD COLUMN {name} {definition}")
            except Exception:
                pass

    def dbh_record_test_results(self, document, uids=None) -> int:
        if not self.available or self._connection is None:
            return 0
        entries = document.entries
        if uids is not None:
            target = set(uids)
            entries = [entry for entry in entries if entry.uid in target]
        rows = []
        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        for entry in entries:
            if not entry.test_state:
                continue
            rows.append((now, entry.url or "", entry.entry_effective_name(),
                         entry.test_state, entry.test_http, entry.test_ms,
                         entry.test_first_segment, entry.test_detail))
        if not rows:
            return 0
        with self._lock:
            try:
                self._connection.executemany(
                    "INSERT INTO test_history (ts, url, channel, state, http_status, ms, kind, detail)"
                    " VALUES (?,?,?,?,?,?,?,?)", rows)
                self._connection.commit()
            except Exception:
                return 0
        return len(rows)

    def dbh_record_scan_run(self, template: str, start_id: int, end_id: int,
                            step: int, total: int, alive: int, note: str = "") -> None:
        if not self.available or self._connection is None:
            return
        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        with self._lock:
            try:
                self._connection.execute(
                    "INSERT INTO scan_runs (ts, template, start_id, end_id, step, total, alive, note)"
                    " VALUES (?,?,?,?,?,?,?,?)",
                    (now, template, start_id, end_id, step, total, alive, note))
                self._connection.commit()
            except Exception:
                pass

    def dbh_recent_scan_runs(self, limit: int = 30) -> list:
        if not self.available or self._connection is None:
            return []
        try:
            cursor = self._connection.execute(
                "SELECT ts, template, start_id, end_id, total, alive, note"
                " FROM scan_runs ORDER BY id DESC LIMIT ?", (limit,))
            return cursor.fetchall()
        except Exception:
            return []

    def dbh_set_id_remark(self, id_key: str, channel_name: str, remark: str) -> None:
        if not self.available or self._connection is None:
            return
        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        with self._lock:
            try:
                self._connection.execute(
                    "INSERT INTO id_remarks (id_key, channel_name, remark, updated_at)"
                    " VALUES (?,?,?,?) ON CONFLICT(id_key) DO UPDATE SET"
                    " channel_name=excluded.channel_name, remark=excluded.remark,"
                    " updated_at=excluded.updated_at",
                    (id_key, channel_name, remark, now))
                self._connection.commit()
            except Exception:
                pass

    def dbh_get_id_remarks(self) -> dict:
        if not self.available or self._connection is None:
            return {}
        try:
            cursor = self._connection.execute(
                "SELECT id_key, channel_name, remark FROM id_remarks")
            return {row[0]: {"channel_name": row[1], "remark": row[2]}
                    for row in cursor.fetchall()}
        except Exception:
            return {}

    # -- 台标库（跨启动累积的「频道名 → 台标地址」，v1.8.2）------------------
    def dbh_upsert_logo_map(self, rows, source: str = "") -> int:
        """写入/更新台标库（按规范化频道名覆盖旧记录）。返回写入条数。"""
        if not self.available or self._connection is None:
            return 0
        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        payload: list = []
        for row in list(rows or []):
            if not isinstance(row, dict):
                continue
            name = (row.get("name") or "").strip()
            key = (row.get("name_key") or m3ule_logo_key(name)).strip()
            logo = (row.get("logo") or "").strip()
            if not key or not logo:
                continue
            payload.append((key, name, logo, (row.get("source") or source or "").strip(), now))
        if not payload:
            return 0
        with self._lock:
            try:
                self._connection.executemany(
                    "INSERT INTO logo_map (name_key, name, logo, source, hits, updated_at)"
                    " VALUES (?,?,?,?,1,?) ON CONFLICT(name_key) DO UPDATE SET"
                    " name=excluded.name, logo=excluded.logo, source=excluded.source,"
                    " hits=logo_map.hits+1, updated_at=excluded.updated_at",
                    payload)
                self._connection.commit()
                return len(payload)
            except Exception as exc:  # noqa: BLE001
                self._last_error = f"{type(exc).__name__}: {exc}"
                return 0

    def dbh_get_logo_map(self, limit: int = 0) -> list:
        """读出台标库（命中次数多的优先）。"""
        if not self.available or self._connection is None:
            return []
        try:
            sql = ("SELECT name_key, name, logo, source, hits, updated_at FROM logo_map"
                   " ORDER BY hits DESC, updated_at DESC")
            params: tuple = ()
            if limit and limit > 0:
                sql += " LIMIT ?"
                params = (int(limit),)
            cursor = self._connection.execute(sql, params)
            return [{"name_key": row[0], "name": row[1], "logo": row[2], "source": row[3],
                     "hits": row[4], "updated_at": row[5]} for row in cursor.fetchall()]
        except Exception:
            return []

    def dbh_count_logo_map(self) -> int:
        if not self.available or self._connection is None:
            return 0
        try:
            return int(self._connection.execute(
                "SELECT COUNT(*) FROM logo_map").fetchone()[0])
        except Exception:
            return 0

    def dbh_delete_logo_map(self, name_keys) -> int:
        keys = [key for key in (name_keys or []) if key]
        if not keys or not self.available or self._connection is None:
            return 0
        with self._lock:
            try:
                self._connection.executemany(
                    "DELETE FROM logo_map WHERE name_key=?", [(key,) for key in keys])
                self._connection.commit()
                return len(keys)
            except Exception:
                return 0

    def dbh_clear_logo_map(self) -> int:
        count = self.dbh_count_logo_map()
        if not count or self._connection is None:
            return 0
        with self._lock:
            try:
                self._connection.execute("DELETE FROM logo_map")
                self._connection.commit()
            except Exception:
                return 0
        return count

    # -- 检测结果缓存（跨启动复用）------------------------------------------
    def dbh_upsert_probe_cache(self, payloads, source_file: str = "") -> int:
        """写入/更新检测缓存（按规范化链接覆盖旧结果）。返回写入条数。"""
        if not self.available or self._connection is None:
            return 0
        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        rows = []
        for payload in payloads or []:
            if not isinstance(payload, dict):
                continue
            url = (payload.get("url") or "").strip()
            key = m3ule_probe_cache_key(url)
            state = str(payload.get("state") or "").strip()
            if not key or not state:
                continue
            record = dict(payload)
            record.pop("uid", None)
            record.pop("label", None)
            try:
                payload_text = json.dumps(record, ensure_ascii=False)
            except (TypeError, ValueError):
                payload_text = ""
            rows.append((
                key, url,
                str(payload.get("label") or payload.get("channel") or "").strip(),
                source_file or str(payload.get("source_file") or ""),
                state,
                str(payload.get("level") or ""),
                1 if payload.get("has_program") else 0,
                m3ule_safe_int(payload.get("http_status", -1), -1),
                m3ule_safe_int(payload.get("ms", -1), -1),
                str(payload.get("kind") or ""),
                str(payload.get("content_type") or ""),
                m3ule_safe_int(payload.get("segments", -1), -1),
                str(payload.get("detail") or ""),
                str(payload.get("first_segment") or ""),
                str(payload.get("variant_url") or ""),
                str(payload.get("error") or ""),
                payload_text,
                m3ule_safe_int(payload.get("live_delay_s", -1), -1),
                m3ule_safe_int(payload.get("real_kbps", -1), -1),
                str(payload.get("stream_id") or ""),
                m3ule_safe_int(payload.get("variant_count", -1), -1),
                1 if payload.get("encrypted") else 0,
                now, now,
            ))
        if not rows:
            return 0
        with self._lock:
            try:
                self._connection.executemany(
                    "INSERT INTO probe_cache (url_key, url, channel, source_file, state, level,"
                    " has_program, http_status, ms, kind, content_type, segments, detail,"
                    " first_segment, variant_url, error, payload,"
                    " live_delay_s, real_kbps, stream_id, variant_count, encrypted,"
                    " checked_at, first_seen, hits)"
                    " VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,0)"
                    " ON CONFLICT(url_key) DO UPDATE SET"
                    " url=excluded.url, channel=excluded.channel,"
                    " source_file=excluded.source_file, state=excluded.state,"
                    " level=excluded.level, has_program=excluded.has_program,"
                    " http_status=excluded.http_status, ms=excluded.ms, kind=excluded.kind,"
                    " content_type=excluded.content_type, segments=excluded.segments,"
                    " detail=excluded.detail, first_segment=excluded.first_segment,"
                    " variant_url=excluded.variant_url, error=excluded.error,"
                    " payload=excluded.payload,"
                    " live_delay_s=excluded.live_delay_s, real_kbps=excluded.real_kbps,"
                    " stream_id=excluded.stream_id, variant_count=excluded.variant_count,"
                    " encrypted=excluded.encrypted, checked_at=excluded.checked_at",
                    rows)
                self._connection.commit()
            except Exception as exc:  # noqa: BLE001
                self._last_error = f"{type(exc).__name__}: {exc}"
                return 0
        return len(rows)

    def dbh_get_probe_cache(self, url_keys, touch: bool = False) -> dict:
        """按规范化键批量读取缓存，返回 {url_key: 记录字典}。"""
        if not self.available or self._connection is None:
            return {}
        keys = [str(key) for key in (url_keys or []) if key]
        if not keys:
            return {}
        found: dict = {}
        with self._lock:
            for start in range(0, len(keys), 400):
                chunk = keys[start:start + 400]
                placeholders = ",".join("?" * len(chunk))
                try:
                    cursor = self._connection.execute(
                        "SELECT url_key, url, channel, source_file, state, level, has_program,"
                        " http_status, ms, kind, content_type, segments, detail, first_segment,"
                        " variant_url, error, payload, checked_at, hits,"
                        " live_delay_s, real_kbps, stream_id, variant_count, encrypted"
                        f" FROM probe_cache WHERE url_key IN ({placeholders})", chunk)
                except Exception as exc:  # noqa: BLE001
                    self._last_error = f"{type(exc).__name__}: {exc}"
                    return found
                for row in cursor.fetchall():
                    record = {}
                    if row[16]:
                        try:
                            loaded = json.loads(row[16])
                        except (TypeError, ValueError):
                            loaded = None
                        if isinstance(loaded, dict):
                            record = loaded
                    # 用列里的值兜底，保证老缓存/损坏 JSON 也能用
                    record.setdefault("url", row[1] or "")
                    record["state"] = record.get("state") or row[4] or ""
                    record["level"] = record.get("level") or row[5] or ""
                    record["has_program"] = bool(record.get("has_program")
                                                 or m3ule_safe_int(row[6], 0))
                    if m3ule_safe_int(record.get("http_status", -1), -1) < 0:
                        record["http_status"] = m3ule_safe_int(row[7], -1)
                    if m3ule_safe_int(record.get("ms", -1), -1) < 0:
                        record["ms"] = m3ule_safe_int(row[8], -1)
                    record["kind"] = record.get("kind") or row[9] or ""
                    record["content_type"] = record.get("content_type") or row[10] or ""
                    if m3ule_safe_int(record.get("segments", -1), -1) < 0:
                        record["segments"] = m3ule_safe_int(row[11], -1)
                    record["detail"] = record.get("detail") or row[12] or ""
                    record["first_segment"] = record.get("first_segment") or row[13] or ""
                    record["variant_url"] = record.get("variant_url") or row[14] or ""
                    record["error"] = record.get("error") or row[15] or ""
                    # v1.3 新增元信息：优先取列值，兼容老缓存（列缺失则退回 JSON）
                    if m3ule_safe_int(record.get("live_delay_s", -1), -1) < 0:
                        record["live_delay_s"] = m3ule_safe_int(row[19], -1)
                    if m3ule_safe_int(record.get("real_kbps", -1), -1) < 0:
                        record["real_kbps"] = m3ule_safe_int(row[20], -1)
                    record["stream_id"] = record.get("stream_id") or row[21] or ""
                    if m3ule_safe_int(record.get("variant_count", -1), -1) < 0:
                        record["variant_count"] = m3ule_safe_int(row[22], -1)
                    record["encrypted"] = bool(record.get("encrypted")
                                               or m3ule_safe_int(row[23], 0))
                    found[row[0]] = {
                        "payload": record,
                        "url": row[1] or "",
                        "channel": row[2] or "",
                        "source_file": row[3] or "",
                        "state": row[4] or "",
                        "checked_at": row[17] or "",
                        "hits": m3ule_safe_int(row[18], 0) + (1 if touch else 0),
                    }
            if touch and found:
                now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                try:
                    self._connection.executemany(
                        "UPDATE probe_cache SET hits = hits + 1, last_hit = ? WHERE url_key = ?",
                        [(now, key) for key in found.keys()])
                    self._connection.commit()
                except Exception:
                    pass
        return found

    def dbh_probe_history_states(self, urls, earliest: bool = True) -> dict:
        """从 `test_history` 里取这些链接最**早**（或最晚）的一次实测状态。

        用途：编号双列对比里「旧（以前）」一侧。检测缓存只保留每个链接的**最新**结果，
        若新旧文件用的是同一批链接，两侧都会落到同一个最新结果，导致永远看不出「以前有信号、
        现在没了」。历史表按时间累积，正好可以回答「这个链接以前是什么状态」。
        返回 {规范化键: {"state": 状态, "ts": 时间}}。
        """
        if not self.available or self._connection is None:
            return {}
        raw_urls = [str(url) for url in (urls or []) if url]
        if not raw_urls:
            return {}
        unique = sorted(set(raw_urls))
        collected: dict = {}
        # 同一秒内写入的多条记录靠自增 id 保持先后（时间戳只到秒，单看 ts 无法确定先后）
        order = "ts ASC, id ASC" if earliest else "ts DESC, id DESC"
        with self._lock:
            for start in range(0, len(unique), 400):
                chunk = unique[start:start + 400]
                placeholders = ",".join("?" * len(chunk))
                try:
                    cursor = self._connection.execute(
                        "SELECT url, state, ts FROM test_history"
                        f" WHERE url IN ({placeholders}) ORDER BY {order}", chunk)
                except Exception as exc:  # noqa: BLE001
                    self._last_error = f"{type(exc).__name__}: {exc}"
                    return collected
                for url, state, ts in cursor.fetchall():
                    key = m3ule_probe_cache_key(url or "")
                    if not key or key in collected:
                        continue
                    collected[key] = {"state": state or "", "ts": ts or ""}
        return collected

    def dbh_count_probe_cache(self) -> int:
        return self.dbh_count_rows("probe_cache")

    def dbh_delete_probe_cache(self, url_keys) -> int:
        if not self.available or self._connection is None:
            return 0
        keys = [str(key) for key in (url_keys or []) if key]
        if not keys:
            return 0
        removed = 0
        with self._lock:
            try:
                for start in range(0, len(keys), 400):
                    chunk = keys[start:start + 400]
                    placeholders = ",".join("?" * len(chunk))
                    cursor = self._connection.execute(
                        f"DELETE FROM probe_cache WHERE url_key IN ({placeholders})", chunk)
                    removed += cursor.rowcount if cursor.rowcount > 0 else 0
                self._connection.commit()
            except Exception:
                return 0
        return removed

    def dbh_clear_probe_cache(self) -> None:
        if not self.available or self._connection is None:
            return
        with self._lock:
            try:
                self._connection.execute("DELETE FROM probe_cache")
                self._connection.commit()
            except Exception:
                pass

    def dbh_prune_probe_cache(self, ttl_hours) -> int:
        """删除超出有效期的缓存（ttl_hours <= 0 时不删除）。返回删除条数。"""
        ttl = m3ule_safe_int(ttl_hours, 0)
        if ttl <= 0 or not self.available or self._connection is None:
            return 0
        boundary = (datetime.now() - timedelta(hours=ttl)).strftime("%Y-%m-%d %H:%M:%S")
        with self._lock:
            try:
                cursor = self._connection.execute(
                    "DELETE FROM probe_cache WHERE checked_at < ?", (boundary,))
                removed = cursor.rowcount if cursor.rowcount > 0 else 0
                self._connection.commit()
            except Exception:
                return 0
        return removed

    def dbh_clear_all_history(self) -> None:
        if not self.available or self._connection is None:
            return
        with self._lock:
            try:
                self._connection.execute("DELETE FROM test_history")
                self._connection.execute("DELETE FROM scan_runs")
                self._connection.commit()
            except Exception:
                pass

    def dbh_count_rows(self, table: str) -> int:
        if not self.available or self._connection is None:
            return 0
        if table not in ("test_history", "scan_runs", "id_remarks", "probe_cache"):
            return 0
        try:
            cursor = self._connection.execute(f"SELECT COUNT(*) FROM {table}")
            return int(cursor.fetchone()[0])
        except Exception:
            return 0

    def dbh_close(self) -> None:
        try:
            if self._connection is not None:
                self._connection.close()
        except Exception:
            pass


# ----------------------------------------------------------------------------
# 对话框：单条链接编辑
# ----------------------------------------------------------------------------

class M3ULiveEditorLinkEditDialog(QDialog):
    """新增 / 编辑单条频道链接。"""

    M3ULE_DIALOG_FIELDS = [
        ("name", "频道名称", ""),
        ("tvg-name", "tvg 名称", ""),
        ("group-title", "分组", ""),
        ("tvg-id", "tvg-id", ""),
        ("channelID", "channelID", ""),
        ("tvg-chno", "频道号", ""),
        ("tvg-logo", "台标地址", ""),
        ("duration", "时长", "0"),
        ("url", "链接地址", ""),
        ("remark", "备注", ""),
    ]

    def __init__(self, title: str, entry=None, defaults=None, parent=None):
        super().__init__(parent)
        self.setWindowTitle(title)
        self.setMinimumWidth(680)
        self._editors = {}
        self._probe_thread = None

        root = QVBoxLayout(self)
        root.setContentsMargins(10, 10, 10, 10)
        root.setSpacing(6)
        form = QFormLayout()
        form.setLabelAlignment(Qt.AlignRight | Qt.AlignVCenter)
        form.setSpacing(6)
        values = {}
        if defaults:
            values.update({key: str(value) for key, value in defaults.items()})
        if entry is not None:
            values["name"] = entry.title
            values["duration"] = entry.duration
            values["url"] = entry.url or ""
            values["remark"] = entry.remark or ""
            for attr_key in ("tvg-name", "group-title", "tvg-id", "channelID", "tvg-chno", "tvg-logo"):
                values[attr_key] = entry.entry_get_attr(attr_key)
        for key, label, default in self.M3ULE_DIALOG_FIELDS:
            if key == "url":
                editor = QPlainTextEdit()
                editor.setPlainText(values.get(key, default) or "")
                editor.setFixedHeight(64)
                editor.setPlaceholderText("http://…/live.m3u8  (每行一个链接则视为批量，请用批量添加)")
            else:
                editor = QLineEdit(values.get(key, default) or "")
                if key in ("tvg-logo", "url"):
                    editor.setClearButtonEnabled(True)
            self._editors[key] = editor
            form.addRow(f"{label}：", editor)
        root.addLayout(form)

        hint = QLabel("提示：编辑不会破坏原文件中未涉及的属性与顺序。")
        hint.setStyleSheet("color:#5f6368;")
        root.addWidget(hint)

        self._probe_label = QLabel("")
        self._probe_label.setWordWrap(True)
        root.addWidget(self._probe_label)

        buttons = QDialogButtonBox()
        self._btn_probe = buttons.addButton("测试该链接", QDialogButtonBox.ActionRole)
        self._btn_probe.clicked.connect(self.dlg_run_single_probe)
        buttons.addButton("确定", QDialogButtonBox.AcceptRole)
        buttons.addButton("取消", QDialogButtonBox.RejectRole)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        root.addWidget(buttons)

    def dlg_collect_fields(self) -> dict:
        result = {}
        for key, editor in self._editors.items():
            if isinstance(editor, QPlainTextEdit):
                result[key] = editor.toPlainText().strip()
            else:
                result[key] = editor.text().strip()
        return result

    def dlg_url_value(self) -> str:
        return self._editors["url"].toPlainText().strip()

    def dlg_build_entry(self):
        fields = self.dlg_collect_fields()
        attrs: "OrderedDict[str, str]" = OrderedDict()
        for key in ("channelID", "tvg-chno", "tvg-name", "tvg-id", "tvg-logo", "group-title"):
            value = fields.get(key, "")
            if value:
                attrs[key] = value
        entry = M3ULiveEditorEntry(
            pre_lines=[], extinf_raw=None, between_lines=[], url=fields.get("url", ""),
            duration=fields.get("duration", "0") or "0", attrs=attrs,
            title=fields.get("name", ""), remark=fields.get("remark", ""))
        # 新增记录一律生成 #EXTINF 行，保证播放器能正确识别频道信息
        entry.extinf_raw = m3ule_format_extinf_line(entry.duration, entry.attrs, entry.title)
        return entry

    def dlg_run_single_probe(self) -> None:
        url = self.dlg_url_value()
        if not url:
            self._probe_label.setText("请先填写链接地址。")
            return
        if self._probe_thread is not None and self._probe_thread.isRunning():
            return
        config = self.parent().wnd_config_manager() if hasattr(self.parent(), "wnd_config_manager") else None
        options = {
            "timeout": config.cfg_get("probe/timeout") if config else 8.0,
            "retries": config.cfg_get("probe/retries") if config else 1,
            "deep": config.cfg_get("probe/deep") if config else True,
            "user_agent": config.cfg_get_user_agent() if config else M3ULE_DEFAULT_USER_AGENT,
            "proxy": config.cfg_get_proxy() if config else "",
            "ignore_ssl": config.cfg_get("probe/ignore_ssl") if config else True,
            "workers": 1,
        }
        self._btn_probe.setEnabled(False)
        self._probe_label.setText("正在测试…")
        self._probe_thread = M3ULiveEditorProbeWorker(
            [{"uid": 0, "url": url, "label": "dialog"}], options, parent=self)
        self._probe_thread.sig_worker_results.connect(self.dlg_on_probe_results)
        self._probe_thread.sig_worker_finished.connect(self.dlg_on_probe_finished)
        self._probe_thread.start()

    @Slot(object)
    def dlg_on_probe_results(self, payloads: list) -> None:
        if not payloads:
            return
        payload = payloads[0]
        state = payload.get("state", "")
        color = M3ULE_TEST_STATE_COLORS.get(state, QColor("#5f6368")).name()
        self._probe_label.setText(
            f"<span style='color:{color};font-weight:bold'>{state}</span> · "
            f"{payload.get('ms', -1)} ms · {payload.get('detail', '')}")

    @Slot(dict)
    def dlg_on_probe_finished(self, summary: dict) -> None:
        self._btn_probe.setEnabled(True)
        self._probe_thread = None


# ----------------------------------------------------------------------------
# 对话框：批量添加链接
# ----------------------------------------------------------------------------

class M3ULiveEditorBatchAddDialog(QDialog):
    """批量添加链接：支持 m3u 片段、纯链接列表、名称+链接。"""

    def __init__(self, existing_urls=None, group_names=None, parent=None):
        super().__init__(parent)
        self.setWindowTitle("批量添加链接")
        self.resize(900, 640)
        self._existing_urls = set()
        for url in (existing_urls or []):
            self._existing_urls.add((url or "").strip())
        self._parsed_entries: list = []

        root = QVBoxLayout(self)
        root.setContentsMargins(10, 10, 10, 10)
        root.setSpacing(6)

        tip = QLabel(
            "每行一条，支持三种写法：<b>完整 m3u 片段</b>（含 #EXTINF）、"
            "<b>名称,链接</b>、<b>仅链接</b>。空行与 # 注释行会被忽略。")
        tip.setWordWrap(True)
        root.addWidget(tip)

        self._input_edit = QPlainTextEdit()
        self._input_edit.setPlaceholderText(
            "翡翠台高清,http://116.199.5.51:8114/hls/Fsv_chan_hls_se_idx=031&...m3u8\n"
            "http://116.199.5.51:8114/hls/Fsv_chan_hls_se_idx=078&...m3u8")
        root.addWidget(self._input_edit, 3)

        options = QGridLayout()
        options.setHorizontalSpacing(8)
        options.setVerticalSpacing(4)
        options.addWidget(QLabel("统一分组："), 0, 0)
        self._group_combo = QComboBox()
        self._group_combo.setEditable(True)
        self._group_combo.addItem("")
        for name in (group_names or []):
            self._group_combo.addItem(name)
        options.addWidget(self._group_combo, 0, 1)

        self._chk_number = QCheckBox("自动编号")
        self._chk_number.setChecked(True)
        options.addWidget(self._chk_number, 0, 2)
        options.addWidget(QLabel("起始："), 0, 3)
        self._spin_start = QSpinBox()
        self._spin_start.setRange(0, 999999)
        self._spin_start.setValue(1000)
        options.addWidget(self._spin_start, 0, 4)
        options.addWidget(QLabel("步长："), 0, 5)
        self._spin_step = QSpinBox()
        self._spin_step.setRange(1, 1000)
        options.addWidget(self._spin_step, 0, 6)

        self._chk_id_attr = QCheckBox("同时填写 tvg-id 与 channelID")
        self._chk_id_attr.setChecked(True)
        options.addWidget(self._chk_id_attr, 0, 7)
        options.addWidget(QLabel("channelID 前缀："), 1, 0)
        self._edit_prefix = QLineEdit("x-ID.")
        options.addWidget(self._edit_prefix, 1, 1)
        self._chk_skip_dup = QCheckBox("跳过已存在的相同链接")
        self._chk_skip_dup.setChecked(True)
        options.addWidget(self._chk_skip_dup, 1, 2, 1, 3)
        self._chk_autotest = QCheckBox("导入后立即测试")
        options.addWidget(self._chk_autotest, 1, 5, 1, 3)
        options.setColumnStretch(7, 1)
        root.addLayout(options)

        preview_row = QHBoxLayout()
        self._btn_preview = QPushButton("解析预览")
        self._btn_preview.clicked.connect(self.dlg_refresh_preview)
        preview_row.addWidget(self._btn_preview)
        self._lbl_preview = QLabel("尚未解析")
        self._lbl_preview.setStyleSheet("color:#5f6368;")
        preview_row.addWidget(self._lbl_preview)
        preview_row.addStretch(1)
        root.addLayout(preview_row)

        self._preview_table = QTableWidget(0, 4)
        self._preview_table.setHorizontalHeaderLabels(["序号", "频道名称", "分组", "链接"])
        self._preview_table.horizontalHeader().setSectionResizeMode(0, QHeaderView.ResizeToContents)
        self._preview_table.horizontalHeader().setSectionResizeMode(1, QHeaderView.Interactive)
        self._preview_table.horizontalHeader().setSectionResizeMode(2, QHeaderView.ResizeToContents)
        self._preview_table.horizontalHeader().setSectionResizeMode(3, QHeaderView.Stretch)
        self._preview_table.verticalHeader().setVisible(False)
        self._preview_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self._preview_table.setColumnWidth(1, 200)
        root.addWidget(self._preview_table, 2)

        buttons = QDialogButtonBox()
        buttons.addButton("导入", QDialogButtonBox.AcceptRole).clicked.connect(self.dlg_accept_import)
        buttons.addButton("关闭", QDialogButtonBox.RejectRole).clicked.connect(self.reject)
        root.addWidget(buttons)

    def dlg_parse_entries(self) -> list:
        text = self._input_edit.toPlainText()
        default_group = self._group_combo.currentText().strip()
        start_number = self._spin_start.value()
        step_number = self._spin_step.value()
        prefix = self._edit_prefix.text().strip()
        number_enabled = self._chk_number.isChecked()
        id_attr_enabled = self._chk_id_attr.isChecked()
        skip_dup = self._chk_skip_dup.isChecked()

        raw_entries: list = []
        lines = text.splitlines()
        index = 0
        total_lines = len(lines)
        while index < total_lines:
            stripped = lines[index].strip()
            if not stripped:
                index += 1
                continue
            if stripped.upper().startswith("#EXTM3U"):
                index += 1
                continue
            if stripped[:7].upper() == "#EXTINF":
                extinf_line = lines[index]
                index += 1
                url = ""
                while index < total_lines:
                    candidate = lines[index].strip()
                    if not candidate:
                        index += 1
                        continue
                    if candidate.startswith("#"):
                        index += 1
                        continue
                    url = candidate
                    index += 1
                    break
                duration, attrs, title = m3ule_parse_extinf_line(extinf_line)
                raw_entries.append(M3ULiveEditorEntry(
                    pre_lines=[], extinf_raw=extinf_line, between_lines=[], url=url,
                    duration=duration, attrs=attrs, title=title))
                continue
            if stripped.startswith("#"):
                index += 1
                continue
            name = ""
            url = stripped
            lowered = stripped.lower()
            is_scheme = lowered.startswith(
                ("http://", "https://", "rtmp://", "rtsp://", "udp://", "rtp://", "file://"))
            if not is_scheme:
                if "," in stripped:
                    name, _, url = stripped.partition(",")
                    name, url = name.strip(), url.strip()
                elif "|" in stripped:
                    name, _, url = stripped.partition("|")
                    name, url = name.strip(), url.strip()
                elif " " in stripped:
                    first, _, rest = stripped.partition(" ")
                    if first and rest.strip():
                        name, url = first.strip(), rest.strip()
            raw_entries.append(M3ULiveEditorEntry(
                pre_lines=[], extinf_raw=None, between_lines=[], url=url,
                duration="0", attrs=OrderedDict(), title=name))
            index += 1

        counter = 0
        result_entries: list = []
        for entry in raw_entries:
            if not (entry.url or "").strip():
                continue
            if skip_dup and entry.url.strip() in self._existing_urls:
                continue
            group = entry.entry_get_attr("group-title") or default_group
            if group:
                entry.entry_set_attr("group-title", group)
            name = entry.title or entry.entry_get_attr("tvg-name")
            if name and not entry.entry_get_attr("tvg-name"):
                entry.entry_set_attr("tvg-name", name)
            if number_enabled:
                number = start_number + counter * step_number
                entry.entry_set_attr("tvg-chno", str(number))
                if id_attr_enabled:
                    entry.entry_set_attr("tvg-id", str(number))
                    entry.entry_set_attr("channelID", f"{prefix}{number}")
                counter += 1
            entry.entry_rebuild_extinf_line()
            self._existing_urls.add(entry.url.strip())
            result_entries.append(entry)
        return result_entries

    def dlg_refresh_preview(self) -> None:
        self._parsed_entries = self.dlg_parse_entries()
        self._preview_table.setRowCount(0)
        limit = min(len(self._parsed_entries), 300)
        self._preview_table.setRowCount(limit)
        for row in range(limit):
            entry = self._parsed_entries[row]
            values = [row + 1, entry.entry_effective_name(),
                      entry.entry_effective_group(), entry.url or ""]
            for column, value in enumerate(values):
                item = QTableWidgetItem("" if value is None else str(value))
                item.setFlags(Qt.ItemIsEnabled | Qt.ItemIsSelectable)
                self._preview_table.setItem(row, column, item)
        self._lbl_preview.setText(
            f"共解析 {len(self._parsed_entries)} 条" +
            (f"（预览前 {limit} 条）" if len(self._parsed_entries) > limit else ""))

    def dlg_accept_import(self) -> None:
        if not self._parsed_entries:
            self.dlg_refresh_preview()
        if not self._parsed_entries:
            QMessageBox.warning(self, "提示", "没有可导入的有效链接。")
            return
        self.accept()

    def dlg_result_entries(self) -> list:
        return list(self._parsed_entries)

    def dlg_should_autotest(self) -> bool:
        return self._chk_autotest.isChecked()


# ----------------------------------------------------------------------------
# 对话框：批量删除
# ----------------------------------------------------------------------------

class M3ULiveEditorBatchDeleteDialog(QDialog):
    """按分组 / 状态 / 关键词 / 重复链接 批量删除条目。"""

    M3ULE_STATE_CHOICES = [
        ("失败", [M3ULE_STATUS_FAIL]),
        ("超时", [M3ULE_STATUS_TIMEOUT]),
        ("错误", [M3ULE_STATUS_ERROR]),
        ("部分可用", [M3ULE_STATUS_PARTIAL]),
        ("成功", [M3ULE_STATUS_OK]),
        ("未测试", [M3ULE_STATUS_NONE, ""]),
        ("失败 + 超时 + 错误", [M3ULE_STATUS_FAIL, M3ULE_STATUS_TIMEOUT, M3ULE_STATUS_ERROR]),
    ]

    def __init__(self, document, group_names=None, parent=None):
        super().__init__(parent)
        self.setWindowTitle("批量删除")
        self.resize(620, 480)
        self._document = document

        root = QVBoxLayout(self)
        root.setContentsMargins(10, 10, 10, 10)
        root.setSpacing(6)

        self._chk_group = QCheckBox("按分组删除：")
        self._combo_group = QComboBox()
        self._combo_group.setEditable(False)
        for name in (group_names or []):
            self._combo_group.addItem(name)
        row = QHBoxLayout()
        row.addWidget(self._chk_group)
        row.addWidget(self._combo_group, 1)
        root.addLayout(row)

        self._chk_state = QCheckBox("按测试状态删除：")
        self._combo_state = QComboBox()
        for label, _ in self.M3ULE_STATE_CHOICES:
            self._combo_state.addItem(label)
        row = QHBoxLayout()
        row.addWidget(self._chk_state)
        row.addWidget(self._combo_state, 1)
        root.addLayout(row)

        self._chk_keyword = QCheckBox("关键词匹配：")
        self._edit_keyword = QLineEdit()
        self._edit_keyword.setPlaceholderText("匹配频道名称 / 链接 / 分组 / ID / 备注")
        self._combo_keyword_scope = QComboBox()
        self._combo_keyword_scope.addItems(["全部字段", "仅频道名称", "仅链接", "仅分组"])
        row = QHBoxLayout()
        row.addWidget(self._chk_keyword)
        row.addWidget(self._edit_keyword, 1)
        row.addWidget(self._combo_keyword_scope)
        root.addLayout(row)

        self._chk_duplicate = QCheckBox("删除重复链接（保留第一条）")
        root.addWidget(self._chk_duplicate)
        self._chk_empty_url = QCheckBox("删除空链接条目")
        root.addWidget(self._chk_empty_url)

        mode_box = QGroupBox("多条件组合方式")
        mode_layout = QHBoxLayout(mode_box)
        self._radio_any = QRadioButton("满足任一条件")
        self._radio_all = QRadioButton("同时满足全部条件")
        self._radio_any.setChecked(True)
        mode_layout.addWidget(self._radio_any)
        mode_layout.addWidget(self._radio_all)
        mode_layout.addStretch(1)
        root.addWidget(mode_box)

        self._lbl_preview = QLabel("点击“预览匹配”查看将删除的条目数。")
        self._lbl_preview.setWordWrap(True)
        self._lbl_preview.setStyleSheet("color:#c5221f;")
        root.addWidget(self._lbl_preview)

        self._preview_table = QTableWidget(0, 3)
        self._preview_table.setHorizontalHeaderLabels(["序号", "频道名称", "链接"])
        self._preview_table.horizontalHeader().setSectionResizeMode(0, QHeaderView.ResizeToContents)
        self._preview_table.horizontalHeader().setSectionResizeMode(1, QHeaderView.Interactive)
        self._preview_table.horizontalHeader().setSectionResizeMode(2, QHeaderView.Stretch)
        self._preview_table.verticalHeader().setVisible(False)
        self._preview_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self._preview_table.setColumnWidth(1, 180)
        root.addWidget(self._preview_table, 1)

        buttons = QDialogButtonBox()
        btn_preview = buttons.addButton("预览匹配", QDialogButtonBox.ActionRole)
        btn_preview.clicked.connect(self.dlg_refresh_preview)
        buttons.addButton("确定删除", QDialogButtonBox.AcceptRole).clicked.connect(self.dlg_accept_delete)
        buttons.addButton("取消", QDialogButtonBox.RejectRole).clicked.connect(self.reject)
        root.addWidget(buttons)

    def dlg_compute_delete_uids(self) -> list:
        conditions = []
        if self._chk_group.isChecked():
            group = self._combo_group.currentText()
            conditions.append(lambda entry, g=group: entry.entry_effective_group() == g)
        if self._chk_state.isChecked():
            states = dict(self.M3ULE_STATE_CHOICES)[self._combo_state.currentText()]
            conditions.append(lambda entry, s=states: entry.test_state in s)
        if self._chk_keyword.isChecked():
            keyword = self._edit_keyword.text().strip()
            scope = self._combo_keyword_scope.currentText()
            if keyword:
                def keyword_match(entry, kw=keyword, sc=scope):
                    if sc == "仅频道名称":
                        return kw.lower() in entry.entry_effective_name().lower()
                    if sc == "仅链接":
                        return kw.lower() in (entry.url or "").lower()
                    if sc == "仅分组":
                        return kw.lower() in entry.entry_effective_group().lower()
                    return entry.entry_matches_keyword(kw)
                conditions.append(keyword_match)
        if self._chk_duplicate.isChecked():
            conditions.append(lambda entry: entry.uid in self._duplicate_uid_set())
        if self._chk_empty_url.isChecked():
            conditions.append(lambda entry: not (entry.url or "").strip())

        if not conditions:
            return []
        combine_all = self._radio_all.isChecked()
        matched = []
        for entry in self._document.entries:
            if combine_all:
                if all(condition(entry) for condition in conditions):
                    matched.append(entry.uid)
            else:
                if any(condition(entry) for condition in conditions):
                    matched.append(entry.uid)
        return matched

    def _duplicate_uid_set(self) -> set:
        seen: set = set()
        duplicates: set = set()
        for entry in self._document.entries:
            url = (entry.url or "").strip().lower()
            if not url:
                continue
            if url in seen:
                duplicates.add(entry.uid)
            else:
                seen.add(url)
        return duplicates

    def dlg_refresh_preview(self) -> None:
        uids = self.dlg_compute_delete_uids()
        uid_set = set(uids)
        self._preview_table.setRowCount(0)
        rows = [entry for entry in self._document.entries if entry.uid in uid_set]
        limit = min(len(rows), 300)
        self._preview_table.setRowCount(limit)
        for row in range(limit):
            entry = rows[row]
            values = [row + 1, entry.entry_effective_name(), entry.url or ""]
            for column, value in enumerate(values):
                item = QTableWidgetItem("" if value is None else str(value))
                item.setFlags(Qt.ItemIsEnabled | Qt.ItemIsSelectable)
                self._preview_table.setItem(row, column, item)
        self._lbl_preview.setText(
            f"将删除 {len(rows)} 条" +
            (f"（预览前 {limit} 条）" if len(rows) > limit else "") +
            ("" if rows else "  —— 当前条件没有匹配到任何条目"))

    def dlg_accept_delete(self) -> None:
        uids = self.dlg_compute_delete_uids()
        if not uids:
            QMessageBox.information(self, "提示", "当前条件没有匹配到任何条目。")
            return
        reply = QMessageBox.question(
            self, "确认删除", f"确定要删除 {len(uids)} 条频道记录吗？此操作不可撤销（可先保存原文件备份）。",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if reply != QMessageBox.Yes:
            return
        self._computed_uids = uids
        self.accept()

    def dlg_result_uids(self) -> list:
        return list(getattr(self, "_computed_uids", []))


# ----------------------------------------------------------------------------
# 批量修改分组（纯函数：便于测试与复用）
# ----------------------------------------------------------------------------

M3ULE_GROUP_SCOPE_SELECTED = "选中条目"
M3ULE_GROUP_SCOPE_VISIBLE = "当前列表全部"
M3ULE_GROUP_SCOPES = (M3ULE_GROUP_SCOPE_SELECTED, M3ULE_GROUP_SCOPE_VISIBLE)
M3ULE_GROUP_MODES = ("设为新的分组名称", "添加到已有分组", "清除分组（删除 group-title）")
M3ULE_GROUP_QUICK_MENU_LIMIT = 30


def m3ule_group_scope_entries(document, scope=M3ULE_GROUP_SCOPE_SELECTED,
                              selected_uids=None, visible_uids=None) -> list:
    """按范围取出待改分组的条目（顺序沿用传入的 uid 顺序，即列表里的视图顺序）。"""
    entries = list(getattr(document, "entries", []) or [])
    if scope == M3ULE_GROUP_SCOPE_SELECTED:
        order = {uid: position for position, uid in enumerate(selected_uids or [])}
        if not order:
            return []
        picked = [entry for entry in entries if entry.uid in order]
        picked.sort(key=lambda entry: order[entry.uid])
        return picked
    if visible_uids is None:
        return entries
    allowed = set(visible_uids)
    return [entry for entry in entries if entry.uid in allowed]


def m3ule_group_batch_plan(entries, target: str) -> dict:
    """算出「把这些条目的分组改成 target」会动到哪些条目（已是目标值的跳过）。"""
    items = list(entries or [])
    group = (target or "").strip()
    rows: list = []
    unchanged = 0
    for entry in items:
        old = entry.entry_effective_group()
        if old == group:
            unchanged += 1
            continue
        rows.append({"uid": entry.uid, "name": entry.entry_effective_name(),
                     "old": old, "new": group})
    return {"target": group, "total": len(items), "rows": rows,
            "changed": len(rows), "unchanged": unchanged}


def m3ule_group_batch_apply(entries, target: str) -> int:
    """把条目分组改成 target（空串＝删掉 group-title），返回真正改动的条数。"""
    group = (target or "").strip()
    changed = 0
    for entry in list(entries or []):
        if entry.entry_effective_group() == group:
            continue
        entry.entry_set_attr("group-title", group)
        changed += 1
    return changed


def m3ule_group_batch_summary_text(plan: dict) -> str:
    """预览摘要：命中多少条、实际要改多少条、多少条已经是目标值。"""
    group = plan.get("target") or ""
    head = f"分组 → 「{group}」" if group else "分组 → 清除（删除 group-title）"
    text = f"{head}：命中 {plan.get('total', 0)} 条，将修改 {plan.get('changed', 0)} 条"
    if plan.get("unchanged"):
        text += f"，另有 {plan['unchanged']} 条分组本来就是目标值（跳过）"
    if not plan.get("changed"):
        text += "　—— 目标范围内没有需要修改的条目"
    return text


# ----------------------------------------------------------------------------
# 对话框：批量修改分组
# ----------------------------------------------------------------------------

class M3ULiveEditorBatchGroupDialog(QDialog):
    """把多条频道一次改成同一个分组：设为新分组、加入已有分组，或清除分组。

    先决定「改哪些」（选中的多条 / 当前列表全部），再决定「改成什么」。
    """

    def __init__(self, document=None, selected_uids=None, visible_uids=None, parent=None):
        super().__init__(parent)
        self.setWindowTitle("批量修改分组")
        self.resize(660, 520)
        self._document = None
        self._selected_uids: list = []
        self._visible_uids = None

        root = QVBoxLayout(self)
        root.setContentsMargins(10, 10, 10, 10)
        root.setSpacing(6)

        scope_box = QGroupBox("① 要改哪些条目")
        scope_layout = QVBoxLayout(scope_box)
        self._scope_radios: dict = {}
        for label in M3ULE_GROUP_SCOPES:
            radio = QRadioButton(label)
            radio.setChecked(label == M3ULE_GROUP_SCOPE_SELECTED)
            scope_layout.addWidget(radio)
            self._scope_radios[label] = radio
        self._radio_scope_selected = self._scope_radios[M3ULE_GROUP_SCOPE_SELECTED]
        self._radio_scope_visible = self._scope_radios[M3ULE_GROUP_SCOPE_VISIBLE]
        scope_hint = QLabel("提示：在列表里按住 Ctrl / Shift 可多选；一条都没选中时会自动改成「当前列表全部」。")
        scope_hint.setWordWrap(True)
        scope_hint.setStyleSheet("color:#5f6368;")
        scope_layout.addWidget(scope_hint)
        root.addWidget(scope_box)

        group_box = QGroupBox("② 分组改成什么")
        group_layout = QGridLayout(group_box)
        self._radio_new = QRadioButton(M3ULE_GROUP_MODES[0])
        self._edit_new_group = QLineEdit()
        self._edit_new_group.setPlaceholderText("新的分组名称，例如：广东-高清")
        self._edit_new_group.setClearButtonEnabled(True)
        group_layout.addWidget(self._radio_new, 0, 0)
        group_layout.addWidget(self._edit_new_group, 0, 1)
        self._radio_existing = QRadioButton(M3ULE_GROUP_MODES[1])
        self._combo_existing = QComboBox()
        self._combo_existing.setMinimumWidth(200)
        self._combo_existing.setToolTip("只列出当前文件里已有的分组；想要新名字请用上面那一项")
        group_layout.addWidget(self._radio_existing, 1, 0)
        group_layout.addWidget(self._combo_existing, 1, 1)
        self._radio_clear = QRadioButton(M3ULE_GROUP_MODES[2])
        group_layout.addWidget(self._radio_clear, 2, 0, 1, 2)
        group_layout.setColumnStretch(1, 1)
        self._radio_new.setChecked(True)
        root.addWidget(group_box)

        self._lbl_preview = QLabel("点击「预览」查看将修改的条目。")
        self._lbl_preview.setWordWrap(True)
        self._lbl_preview.setStyleSheet("color:#1a73e8;")
        root.addWidget(self._lbl_preview)

        self._preview_table = QTableWidget(0, 4)
        self._preview_table.setHorizontalHeaderLabels(["序号", "频道名称", "原分组", "新分组"])
        self._preview_table.horizontalHeader().setSectionResizeMode(0, QHeaderView.ResizeToContents)
        self._preview_table.horizontalHeader().setSectionResizeMode(1, QHeaderView.Interactive)
        self._preview_table.horizontalHeader().setSectionResizeMode(2, QHeaderView.Interactive)
        self._preview_table.horizontalHeader().setSectionResizeMode(3, QHeaderView.Stretch)
        self._preview_table.verticalHeader().setVisible(False)
        self._preview_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self._preview_table.setColumnWidth(1, 200)
        self._preview_table.setColumnWidth(2, 140)
        root.addWidget(self._preview_table, 1)

        buttons = QDialogButtonBox()
        btn_preview = buttons.addButton("预览", QDialogButtonBox.ActionRole)
        btn_preview.clicked.connect(self.dlg_refresh_preview)
        buttons.addButton("确定应用", QDialogButtonBox.AcceptRole).clicked.connect(self.dlg_accept)
        buttons.addButton("取消", QDialogButtonBox.RejectRole).clicked.connect(self.reject)
        root.addWidget(buttons)

        self._radio_new.toggled.connect(self.dlg_on_mode_changed)
        self._radio_existing.toggled.connect(self.dlg_on_mode_changed)
        self._radio_clear.toggled.connect(self.dlg_on_mode_changed)
        self._edit_new_group.textChanged.connect(self.dlg_on_input_changed)
        self._combo_existing.currentIndexChanged.connect(self.dlg_on_input_changed)
        self._radio_scope_selected.toggled.connect(self.dlg_on_input_changed)

        self.dlg_set_context(document, selected_uids, visible_uids)

    # -- 上下文 --------------------------------------------------------------
    @Slot()
    def dlg_on_mode_changed(self, *_args) -> None:
        self._edit_new_group.setEnabled(self._radio_new.isChecked())
        self._combo_existing.setEnabled(self._radio_existing.isChecked())
        self.dlg_refresh_preview()

    @Slot()
    def dlg_on_input_changed(self, *_args) -> None:
        self.dlg_refresh_preview()

    def dlg_set_context(self, document, selected_uids=None, visible_uids=None) -> None:
        """给定文档与「选中的 / 列表里可见的」条目 uid，刷新范围与已有分组下拉。"""
        self._document = document
        self._selected_uids = list(selected_uids or [])
        self._visible_uids = None if visible_uids is None else list(visible_uids)

        names = list(document.doc_group_names()) if document is not None else []
        self._combo_existing.blockSignals(True)
        self._combo_existing.clear()
        for name in names:
            self._combo_existing.addItem(name, name)
        self._combo_existing.blockSignals(False)

        has_selection = bool(self._selected_uids)
        self._radio_scope_selected.setEnabled(has_selection)
        if has_selection:
            self._radio_scope_selected.setChecked(True)
        else:
            self._radio_scope_visible.setChecked(True)
        self._edit_new_group.setEnabled(self._radio_new.isChecked())
        self._combo_existing.setEnabled(self._radio_existing.isChecked())
        visible_count = len(self.dlg_scope_entries(M3ULE_GROUP_SCOPE_VISIBLE))
        self._radio_scope_selected.setText(
            f"{M3ULE_GROUP_SCOPE_SELECTED}（{len(self._selected_uids)} 条）")
        self._radio_scope_visible.setText(
            f"{M3ULE_GROUP_SCOPE_VISIBLE}（{visible_count} 条）")
        self.dlg_refresh_preview()

    # -- 取值 ----------------------------------------------------------------
    def dlg_scope_name(self) -> str:
        if self._radio_scope_selected.isEnabled() and self._radio_scope_selected.isChecked():
            return M3ULE_GROUP_SCOPE_SELECTED
        return M3ULE_GROUP_SCOPE_VISIBLE

    def dlg_scope_entries(self, scope=None) -> list:
        return m3ule_group_scope_entries(
            self._document, scope or self.dlg_scope_name(),
            self._selected_uids, self._visible_uids)

    def dlg_scope_uids(self) -> list:
        return [entry.uid for entry in self.dlg_scope_entries()]

    def dlg_group_names(self) -> list:
        return [self._combo_existing.itemData(index)
                for index in range(self._combo_existing.count())]

    def dlg_target_group(self) -> str:
        """目标分组名；清除分组返回空串。"""
        if self._radio_clear.isChecked():
            return ""
        if self._radio_existing.isChecked():
            data = self._combo_existing.currentData()
            if data is None:
                data = self._combo_existing.currentText()
            return (data or "").strip()
        return self._edit_new_group.text().strip()

    def dlg_plan(self) -> dict:
        return m3ule_group_batch_plan(self.dlg_scope_entries(), self.dlg_target_group())

    # -- 预览 / 应用 ---------------------------------------------------------
    def dlg_new_group_missing(self) -> bool:
        """选了「新分组名称」却还没填名字。"""
        return self._radio_new.isChecked() and not self._edit_new_group.text().strip()

    def dlg_existing_missing(self) -> bool:
        """选了「添加到已有分组」但文件里一个分组都没有。"""
        return self._radio_existing.isChecked() and self._combo_existing.count() == 0

    def dlg_blocked_hint(self) -> str:
        if self.dlg_existing_missing():
            return "当前文件里还没有任何分组，请改用「设为新的分组名称」。"
        if self.dlg_new_group_missing():
            return "请输入新的分组名称；若要清空分组，请选择「清除分组（删除 group-title）」。"
        return ""

    def dlg_refresh_preview(self) -> None:
        hint = self.dlg_blocked_hint()
        if hint:
            self._preview_table.setRowCount(0)
            self._lbl_preview.setText(hint)
            return
        plan = self.dlg_plan()
        rows = plan["rows"]
        limit = min(len(rows), 300)
        self._preview_table.setRowCount(limit)
        for row in range(limit):
            item = rows[row]
            values = [row + 1, item["name"], item["old"] or "（无分组）",
                      item["new"] or "（清除分组）"]
            for column, value in enumerate(values):
                cell = QTableWidgetItem("" if value is None else str(value))
                cell.setFlags(Qt.ItemIsEnabled | Qt.ItemIsSelectable)
                self._preview_table.setItem(row, column, cell)
        text = m3ule_group_batch_summary_text(plan)
        if len(rows) > limit:
            text += f"（预览前 {limit} 条）"
        self._lbl_preview.setText(text)

    def dlg_accept(self) -> None:
        hint = self.dlg_blocked_hint()
        if hint:
            QMessageBox.information(self, "提示", hint)
            return
        if not self.dlg_plan()["changed"]:
            QMessageBox.information(self, "提示", "目标范围内没有需要修改的条目（分组已经是目标值）。")
            return
        self.accept()

    def dlg_apply_group(self, document=None, selected_uids=None, visible_uids=None) -> int:
        """套用当前设置，返回真正改动的条数（传入 document 时先用它刷新上下文）。"""
        if document is not None:
            self.dlg_set_context(document, selected_uids, visible_uids)
        return m3ule_group_batch_apply(self.dlg_scope_entries(), self.dlg_target_group())


# ----------------------------------------------------------------------------
# 后台线程：读取台标来源（本机文件 / 网址 / 文件夹 / EPG）
# ----------------------------------------------------------------------------

M3ULE_LOGO_ORPHAN_WORKERS = []


def m3ule_logo_orphan_worker(worker) -> None:
    """把关窗时还在跑的读来源线程「脱管」：先清掉已结束的，再挂到一个全局列表里。

    不这样做的话，线程会随对话框一起被销毁（Qt 会警告 "QThread: Destroyed while
    thread is still running"），严重时崩溃。
    """
    if worker is None:
        return
    try:
        worker.setParent(None)
    except Exception:
        pass
    M3ULE_LOGO_ORPHAN_WORKERS[:] = [item for item in M3ULE_LOGO_ORPHAN_WORKERS
                                    if item is not worker and item.isRunning()]
    M3ULE_LOGO_ORPHAN_WORKERS.append(worker)
    try:
        worker.finished.connect(worker.deleteLater)
    except Exception:
        pass


class M3ULiveEditorLogoSourceWorker(QThread):
    """后台读取台标来源，学出「频道名 → 台标」，避免抓大文件（EPG 常有十几 MB）卡界面。"""
    sig_source = Signal(int, str, str, bool, str, int)   # 序号 / 类型 / 值 / 成功 / 说明 / 条数
    sig_done = Signal(bool, str)

    def __init__(self, sources, parent=None):
        super().__init__(parent)
        self._sources = [dict(source or {}) for source in (sources or [])]
        self._results: dict = {}
        self._notes: dict = {}
        self._cancel = False
        self._timeout = M3ULE_LOGO_FETCH_TIMEOUT

    def lsw_sources(self) -> list:
        return [dict(source) for source in self._sources]

    def lsw_results(self) -> dict:
        return {index: dict(learned) for index, learned in self._results.items()}

    def lsw_notes(self) -> dict:
        return dict(self._notes)

    def lsw_request_cancel(self) -> None:
        self._cancel = True

    def lsw_is_cancelled(self) -> bool:
        return self._cancel

    def lsw_should_stop(self) -> bool:
        return self._cancel or self.isInterruptionRequested()

    def run(self) -> None:
        requests_module = m3ule_get_requests_module()
        total = 0
        failed = 0
        for index, source in enumerate(self._sources):
            if self.lsw_should_stop():
                break
            kind = str(source.get("kind") or "")
            value = str(source.get("value") or "")
            ok, note, learned = self.lsw_load_source(
                kind, value, str(source.get("prefix") or ""), requests_module)
            self._notes[index] = note
            if ok:
                self._results[index] = learned
                total += len(learned)
            else:
                failed += 1
            self.sig_source.emit(index, kind, value, ok, note, len(learned))
        cancelled = self.lsw_should_stop()
        summary = "已取消读取台标来源" if cancelled else f"读取完成：共学到 {total} 条台标映射"
        if failed and not cancelled:
            summary += f"，{failed} 个来源没读到台标"
        self.sig_done.emit(not cancelled, summary)

    def lsw_load_source(self, kind: str, value: str, prefix: str, requests_module):
        """读一个来源并学出台标映射，返回 (是否成功, 说明, {名字: 台标})。"""
        if kind == "folder":
            if not os.path.isdir(value):
                return False, "文件夹不存在", {}
            learned = m3ule_logo_learn_from_folder(value, prefix)
            if not learned:
                return False, "文件夹里没有图片文件（png/jpg/webp/svg…）", {}
            return True, f"文件夹里读到 {len(learned)} 张图片", learned
        if kind == "file":
            if not os.path.isfile(value):
                return False, "文件不存在", {}
            learned = m3ule_logo_learn_from_path(value)
            if not learned:
                return False, "文件里没有带台标的频道", {}
            return True, f"学到 {len(learned)} 条", learned
        text, note = m3ule_logo_fetch_text_source(
            value, requests_module, self._timeout, self.lsw_should_stop)
        if text is None:
            return False, note, {}
        learned = m3ule_logo_learn_from_text(text)
        if not learned:
            return False, f"{note}，但里面没有台标", {}
        return True, f"{note}，学到 {len(learned)} 条", learned


# ----------------------------------------------------------------------------
# 对话框：台标自动匹配
# ----------------------------------------------------------------------------

class M3ULiveEditorLogoMatchDialog(QDialog):
    """台标自动匹配：从参考 m3u / 台标库 / EPG / 台标文件夹学「频道名 → 台标」，按名字补 tvg-logo。

    流程与项目其它批量工具一致：先看（预览表 + 分类计数）再改（勾选后写回，只标未保存不写盘）。
    """

    M3ULE_SOURCE_SETTING_KEYS = (
        ("logo/sources", "sources"), ("logo/use_db", "db"),
        ("logo/use_head_epg", "head_epg"), ("logo/fill_missing", "fill_missing"),
        ("logo/fuzzy", "fuzzy"), ("logo/store", "store"),
    )
    M3ULE_SOURCE_DEFAULTS = {"db": True, "head_epg": True, "fill_missing": True,
                             "fuzzy": False, "store": True}

    def __init__(self, document=None, history_store=None, config=None,
                 selected_uids=None, only_selected=False, parent=None):
        super().__init__(parent)
        self.setWindowTitle("台标自动匹配")
        self.resize(1020, 700)
        self._document = document
        self._history = history_store
        self._config = config
        self._selected_uids = list(selected_uids or [])
        self._only_selected = bool(only_selected)
        self._sources: list = []
        self._learned: dict = {}
        self._notes: dict = {}
        self._index: dict = {}
        self._plan: dict = {"rows": [], "counts": {}, "total": 0, "apply": 0}
        self._applied = 0
        self._worker = None
        self._loading = False

        root = QVBoxLayout(self)
        root.setContentsMargins(10, 10, 10, 10)
        root.setSpacing(6)

        scope_row = QHBoxLayout()
        scope_row.addWidget(QLabel("作用范围："))
        self._radio_scope_all = QRadioButton("当前文件全部")
        self._radio_scope_selected = QRadioButton("选中的条目")
        scope_row.addWidget(self._radio_scope_all)
        scope_row.addWidget(self._radio_scope_selected)
        scope_row.addStretch(1)
        root.addLayout(scope_row)

        source_box = QGroupBox("① 台标来源（按顺序取，先到的优先）")
        source_layout = QVBoxLayout(source_box)
        self._list_sources = QListWidget()
        self._list_sources.setMinimumHeight(96)
        self._list_sources.setToolTip(
            "参考 m3u / 台标库 CSV(JSON) / EPG / 台标文件夹都行：\n"
            "· 参考 m3u（文件或网址）：学「频道名 → tvg-logo」，自己的其它文件最省事；\n"
            "· 台标库 CSV / JSON：两列「频道名, 台标地址」即可（也可带表头）；\n"
            "· EPG(XMLTV)：取每个频道的 <icon src=…>，按频道名匹配；\n"
            "· 台标文件夹：把图片文件名当频道名（CCTV1.png → 频道 CCTV1）。")
        source_layout.addWidget(self._list_sources, 1)
        source_buttons = QHBoxLayout()
        for text, slot, tip in (
                ("添加文件…", self.dlg_choose_source_file,
                 "添加已带台标的 m3u / 台标库 CSV(JSON) / EPG 节目单作为参考"),
                ("添加网址…", self.dlg_choose_source_url, "添加参考 m3u、台标库或 EPG(XMLTV) 的网络地址"),
                ("添加文件夹…", self.dlg_choose_source_folder, "添加装满图片的台标文件夹"),
                ("导入网络台标库", self.dlg_import_bundled_library,
                 "把随程序的「台标库-网络汇总.csv」一次性存进数据库台标库\n"
                 "存好后勾上「用已保存的台标库」就能直接给任何文件补台标"),
                ("内置推荐", self.dlg_add_recommended_source,
                 "添加随程序的网络台标库 + iptv-org 中国频道列表（含台标）\n"
                 f"{M3ULE_LOGO_IPTV_ORG_URL}"),
                ("移除所选", self.dlg_remove_selected_sources, "移除选中的来源"),
                ("清空", self.dlg_clear_sources, "清空来源列表")):
            button = QPushButton(text)
            button.setToolTip(tip)
            button.clicked.connect(slot)
            source_buttons.addWidget(button)
        source_buttons.addStretch(1)
        source_layout.addLayout(source_buttons)
        option_row = QHBoxLayout()
        self._chk_db = QCheckBox("用已保存的台标库")
        self._chk_db.setToolTip("跨启动累积的「频道名 → 台标」，每次成功匹配都会存进去，下次直接命中")
        self._chk_head_epg = QCheckBox("用文件头部声明的 EPG")
        self._chk_head_epg.setToolTip("m3u 头部的 x-tvg-url / url-tvg 地址（XMLTV 里带台标就一起取）")
        option_row.addWidget(self._chk_db)
        option_row.addWidget(self._chk_head_epg)
        self._lbl_library = QLabel("台标库：—")
        self._lbl_library.setStyleSheet("color:#5f6368;")
        option_row.addWidget(self._lbl_library)
        option_row.addStretch(1)
        source_layout.addLayout(option_row)
        root.addWidget(source_box)

        option_box = QGroupBox("② 匹配选项")
        option_layout = QHBoxLayout(option_box)
        self._chk_fill_missing = QCheckBox("只补没有台标的条目")
        self._chk_fill_missing.setToolTip("关掉后，参考里的台标会覆盖同名频道的现有台标")
        self._chk_fuzzy = QCheckBox("给出相似名建议（需人工确认）")
        self._chk_fuzzy.setToolTip("名字只是相似（如「北京卫视高清」↔「北京卫视」）的也会列出来，默认不勾选")
        self._chk_store = QCheckBox("把用上的匹配存进台标库")
        self._chk_store.setToolTip("下次打开别的文件可以直接命中，不用再读参考文件")
        for widget in (self._chk_fill_missing, self._chk_fuzzy, self._chk_store):
            option_layout.addWidget(widget)
        option_layout.addStretch(1)
        root.addWidget(option_box)

        action_row = QHBoxLayout()
        self._btn_match = QPushButton("开始匹配")
        self._btn_match.setDefault(True)
        self._btn_match.clicked.connect(self.dlg_start_match)
        action_row.addWidget(self._btn_match)
        self._progress = QProgressBar()
        self._progress.setRange(0, 100)
        self._progress.setValue(0)
        self._progress.setMaximumWidth(140)
        action_row.addWidget(self._progress)
        self._lbl_summary = QLabel("点「开始匹配」读取来源并预览结果。")
        self._lbl_summary.setWordWrap(True)
        self._lbl_summary.setStyleSheet("color:#1a73e8;")
        action_row.addWidget(self._lbl_summary, 1)
        root.addLayout(action_row)

        check_row = QHBoxLayout()
        btn_all = QPushButton("全选")
        btn_all.clicked.connect(lambda: self.dlg_set_all_checked(True))
        btn_none = QPushButton("全不选")
        btn_none.clicked.connect(lambda: self.dlg_set_all_checked(False))
        btn_auto = QPushButton("只选可自动应用的")
        btn_auto.clicked.connect(lambda: self.dlg_set_all_checked(True, only_auto=True))
        for button in (btn_all, btn_none, btn_auto):
            check_row.addWidget(button)
        check_row.addStretch(1)
        root.addLayout(check_row)

        self._preview_table = QTableWidget(0, 6)
        self._preview_table.setHorizontalHeaderLabels(
            ["应用", "序号", "频道名称", "状态", "台标地址", "来源"])
        header = self._preview_table.horizontalHeader()
        header.setSectionResizeMode(0, QHeaderView.ResizeToContents)
        header.setSectionResizeMode(1, QHeaderView.ResizeToContents)
        header.setSectionResizeMode(2, QHeaderView.Interactive)
        header.setSectionResizeMode(3, QHeaderView.ResizeToContents)
        header.setSectionResizeMode(4, QHeaderView.Stretch)
        header.setSectionResizeMode(5, QHeaderView.Interactive)
        self._preview_table.verticalHeader().setVisible(False)
        self._preview_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self._preview_table.setColumnWidth(2, 200)
        self._preview_table.setColumnWidth(5, 180)
        root.addWidget(self._preview_table, 1)

        buttons = QDialogButtonBox()
        buttons.addButton("导出预览 CSV", QDialogButtonBox.ActionRole).clicked.connect(
            self.dlg_export_preview_csv)
        buttons.addButton("导出台标库 CSV", QDialogButtonBox.ActionRole).clicked.connect(
            self.dlg_export_logo_map_csv)
        buttons.addButton("导入台标库 CSV", QDialogButtonBox.ActionRole).clicked.connect(
            self.dlg_import_logo_map_csv)
        buttons.addButton("清空台标库", QDialogButtonBox.ActionRole).clicked.connect(
            self.dlg_clear_logo_map)
        buttons.addButton("应用到列表", QDialogButtonBox.AcceptRole).clicked.connect(self.dlg_accept)
        buttons.addButton("关闭", QDialogButtonBox.RejectRole).clicked.connect(self.reject)
        root.addWidget(buttons)

        self._radio_scope_all.setChecked(not self._only_selected)
        self._radio_scope_selected.setChecked(self._only_selected)
        self._radio_scope_selected.setEnabled(bool(self._selected_uids))
        for widget in (self._chk_fill_missing, self._chk_fuzzy, self._chk_store,
                       self._chk_db, self._chk_head_epg):
            widget.toggled.connect(self.dlg_persist_config)
        self._chk_head_epg.toggled.connect(self.dlg_refresh_head_epg_label)
        for widget in (self._radio_scope_all, self._radio_scope_selected):
            widget.toggled.connect(self.dlg_refresh_preview)
        self._chk_fill_missing.toggled.connect(self.dlg_refresh_preview)
        self._chk_fuzzy.toggled.connect(self.dlg_refresh_preview)
        self._chk_db.toggled.connect(self.dlg_refresh_preview)

        self.dlg_reload_from_config()
        self.dlg_refresh_library_stats()
        self.dlg_refresh_head_epg_label()
        self.dlg_refresh_scope_labels()

    # -- 来源列表 ------------------------------------------------------------
    def dlg_add_source(self, kind: str, value: str, prefix: str = "") -> bool:
        """加一个来源（同类型同地址不重复加）。"""
        value = (value or "").strip()
        if not value:
            return False
        source = {"kind": kind, "value": value}
        if prefix:
            source["prefix"] = prefix.strip()
        for existing in self._sources:
            if (existing.get("kind") == kind and existing.get("value") == value
                    and existing.get("prefix", "") == source.get("prefix", "")):
                return False
        self._sources.append(source)
        item = QListWidgetItem(f"{m3ule_logo_source_label(kind)}："
                               f"{m3ule_shorten_url_text(value, 70)}")
        item.setData(Qt.UserRole, source)
        item.setToolTip(value)
        self._list_sources.addItem(item)
        self.dlg_persist_config()
        return True

    def dlg_source_list(self) -> list:
        return [dict(source) for source in self._sources]

    def dlg_remove_selected_sources(self) -> int:
        rows = sorted({index.row() for index in self._list_sources.selectedIndexes()},
                      reverse=True)
        for row in rows:
            self._list_sources.takeItem(row)
            if 0 <= row < len(self._sources):
                del self._sources[row]
        if rows:
            self.dlg_persist_config()
        return len(rows)

    def dlg_clear_sources(self) -> None:
        self._list_sources.clear()
        self._sources = []
        self.dlg_persist_config()

    def dlg_choose_source_file(self) -> None:
        start = ""
        if self._config is not None:
            start = str(self._config.cfg_get("logo/last_source_dir", "") or "")
        path, _filter = QFileDialog.getOpenFileName(
            self, "选择参考文件（已带台标的 m3u / 台标库 CSV(JSON) / EPG）", start,
            "台标库映射 (*.csv *.json);;m3u 文件 (*.m3u *.m3u8 *.txt);;"
            "XMLTV 节目单 (*.xml *.xmltv);;所有文件 (*.*)")
        if not path:
            return
        if self._config is not None:
            self._config.cfg_set("logo/last_source_dir", os.path.dirname(path))
        self.dlg_add_source("file", path)

    def dlg_choose_source_url(self) -> None:
        text, ok = QInputDialog.getText(
            self, "添加网址", "参考 m3u 或 EPG(XMLTV) 地址：", text=M3ULE_LOGO_IPTV_ORG_URL)
        if ok and text.strip():
            self.dlg_add_source("url", text.strip())

    def dlg_choose_source_folder(self) -> None:
        start = ""
        if self._config is not None:
            start = str(self._config.cfg_get("logo/last_dir", "") or "")
        path = QFileDialog.getExistingDirectory(self, "选择台标文件夹（图片文件名=频道名）", start)
        if not path:
            return
        if self._config is not None:
            self._config.cfg_set("logo/last_dir", path)
        prefix = ""
        if self._config is not None:
            prefix = str(self._config.cfg_get("logo/dir_url_prefix", "") or "")
        self.dlg_add_source("folder", path, prefix)

    def dlg_add_recommended_source(self, *, notify: bool = True) -> int:
        """一键加「内置推荐来源」：随程序的网络台标库 + iptv-org 中国频道列表。返回新增个数。"""
        added = 0
        bundled = m3ule_logo_bundled_library_path()
        if bundled and self.dlg_add_source("file", bundled):
            added += 1
        if self.dlg_add_source("url", M3ULE_LOGO_IPTV_ORG_URL):
            added += 1
        if added:
            self._lbl_summary.setText(
                f"已加入 {added} 个内置推荐来源（当前共 {len(self.dlg_source_list())} 个）。")
        elif notify:
            QMessageBox.information(
                self, "提示",
                "内置推荐来源都已经在列表里了。"
                + ("" if bundled else "\n（没找到随程序的台标库文件：data 目录里的「台标库-网络汇总.csv」）"))
        return added

    def dlg_offer_bundled_library(self) -> bool:
        """第一次打开对话框时，把随程序的网络台标库作为默认来源（用户删掉后不再自动加）。"""
        if self._sources or self._config is None:
            return False
        if bool(self._config.cfg_get("logo/bundled_added", False)):
            return False
        path = m3ule_logo_bundled_library_path()
        if not path:
            return False
        self._config.cfg_set("logo/bundled_added", True)
        return self.dlg_add_source("file", path)

    def dlg_import_bundled_library(self, *, notify: bool = True) -> int:
        """把随程序的「网络台标库」CSV 一次性导入数据库台标库。返回导入条数。"""
        path = m3ule_logo_bundled_library_path()
        if not path:
            if notify:
                QMessageBox.information(
                    self, "提示", "没找到随程序的台标库文件（data 目录里的「台标库-网络汇总.csv」）。")
            return 0
        return self.dlg_import_logo_map_path(path, "网络台标库", notify=notify)

    def dlg_source_caption(self, source) -> str:
        label = m3ule_logo_source_label(str(source.get("kind") or ""))
        value = str(source.get("value") or "")
        if source.get("prefix"):
            return f"{label}：{value}（网络前缀）"
        return f"{label}：{m3ule_shorten_url_text(value, 60)}"

    def dlg_head_epg_urls(self) -> list:
        return m3ule_logo_head_epg_urls(self._document)

    def dlg_refresh_head_epg_label(self) -> None:
        urls = self.dlg_head_epg_urls()
        if urls:
            self._chk_head_epg.setText(f"用文件头部声明的 EPG（{m3ule_shorten_url_text(urls[0], 46)}"
                                       + ("…）" if len(urls) > 1 else "）"))
            self._chk_head_epg.setEnabled(True)
        else:
            self._chk_head_epg.setText("用文件头部声明的 EPG（本文件没声明）")
            self._chk_head_epg.setEnabled(False)
            self._chk_head_epg.setChecked(False)

    def dlg_set_source_status(self, index: int, text: str) -> None:
        item = self._list_sources.item(index)
        if item is None:
            return
        source = self._sources[index] if index < len(self._sources) else {}
        value = str(source.get("value") or "")
        item.setText(f"{m3ule_logo_source_label(str(source.get('kind') or ''))}："
                     f"{m3ule_shorten_url_text(value, 70)}　·　{text}")
        item.setToolTip(f"{value}\n{text}")

    def dlg_worker_sources(self) -> list:
        """真正交给后台线程读的来源：列表里的 + （勾选时）文件头部声明的 EPG。"""
        sources = self.dlg_source_list()
        if self._chk_head_epg.isChecked() and self._chk_head_epg.isEnabled():
            for url in self.dlg_head_epg_urls():
                sources.append({"kind": "epg", "value": url})
        return sources

    # -- 范围 / 库 -----------------------------------------------------------
    def dlg_scope_selected(self) -> bool:
        return self._radio_scope_selected.isChecked() and bool(self._selected_uids)

    def dlg_target_entries(self) -> list:
        if self._document is None:
            return []
        if self.dlg_scope_selected():
            wanted = set(self._selected_uids)
            return [entry for entry in self._document.entries if entry.uid in wanted]
        return list(self._document.entries)

    def dlg_refresh_scope_labels(self) -> None:
        total = len(self._document.entries) if self._document is not None else 0
        self._radio_scope_all.setText(f"当前文件全部（{total} 条）")
        self._radio_scope_selected.setText(f"选中的条目（{len(self._selected_uids)} 条）")

    def dlg_refresh_library_stats(self) -> None:
        if self._history is None:
            self._chk_db.setEnabled(False)
            self._lbl_library.setText("台标库：不可用（数据库没打开）")
            return
        count = self._history.dbh_count_logo_map()
        self._chk_db.setText(f"用已保存的台标库（{count} 条）")
        self._lbl_library.setText(f"台标库：{count} 条")

    def dlg_library_records(self) -> list:
        if self._history is None:
            return []
        return self._history.dbh_get_logo_map(M3ULE_LOGO_DB_LIMIT)

    # -- 读取来源 / 匹配 -----------------------------------------------------
    def dlg_start_match(self, *, notify: bool = True) -> bool:
        """读来源 + 匹配（执行与提示分离：`notify=False` 时不弹框，便于自动化）。"""
        sources = self.dlg_worker_sources()
        if not sources:
            if notify:
                QMessageBox.information(
                    self, "提示",
                    "请先添加至少一个台标来源：参考 m3u 文件 / 网址（m3u 或 EPG）/ 台标文件夹。")
            return False
        self.dlg_persist_config()
        self._learned = {}
        self._notes = {}
        self._index = {}
        self._plan = {"rows": [], "counts": {}, "total": 0, "apply": 0}
        self._preview_table.setRowCount(0)
        for index in range(self._list_sources.count()):
            source = self._sources[index] if index < len(self._sources) else {}
            self.dlg_set_source_status(index, "读取中…" if index < len(sources) else "")
        self._progress.setRange(0, 0)
        self._btn_match.setEnabled(False)
        self._lbl_summary.setText(f"正在读取 {len(sources)} 个台标来源…")
        self._worker = M3ULiveEditorLogoSourceWorker(sources, self)
        self._worker.sig_source.connect(self.dlg_on_source_loaded)
        self._worker.sig_done.connect(self.dlg_on_sources_done)
        self._worker.start()
        return True

    @Slot(int, str, str, bool, str, int)
    def dlg_on_source_loaded(self, index: int, kind: str, value: str, ok: bool,
                             note: str, count: int) -> None:
        self._notes[index] = note
        self.dlg_set_source_status(index, ("✔ " if ok else "✘ ") + note)

    @Slot(bool, str)
    def dlg_on_sources_done(self, ok: bool, note: str) -> None:
        if self._worker is not None:
            self._learned = self._worker.lsw_results()
            self._worker = None
        self._progress.setRange(0, 100)
        self._progress.setValue(100 if ok else 0)
        self._btn_match.setEnabled(True)
        self.dlg_build_index()
        self.dlg_refresh_preview()
        self.dlg_refresh_library_stats()
        self._lbl_summary.setText(f"{note}｜{self._lbl_summary.text()}")

    def dlg_build_index(self) -> dict:
        """把各来源（列表顺序 + 台标库）合成匹配索引。"""
        groups: list = []
        for index, source in enumerate(self.dlg_worker_sources()):
            learned = self._learned.get(index) or {}
            if learned:
                groups.append((self.dlg_source_caption(source), learned))
        if self._chk_db.isChecked():
            learned = m3ule_logo_records_to_learned(self.dlg_library_records())
            if learned:
                groups.append(("台标库", learned))
        self._index = m3ule_logo_build_index(groups)
        return self._index

    def dlg_index_size(self) -> int:
        return len(self._index)

    def dlg_plan(self) -> dict:
        return self._plan

    def dlg_state_color(self, state: str):
        return QColor(M3ULE_LOGO_STATE_COLORS.get(state, "#202124"))

    def dlg_refresh_preview(self) -> None:
        self._plan = m3ule_logo_plan(
            self.dlg_target_entries(), self._index,
            fill_missing_only=self._chk_fill_missing.isChecked(),
            fuzzy=self._chk_fuzzy.isChecked())
        rows = self._plan["rows"][:M3ULE_LOGO_PREVIEW_LIMIT]
        self._preview_table.setRowCount(len(rows))
        for position, row in enumerate(rows):
            checker = QTableWidgetItem()
            checker.setFlags(Qt.ItemIsEnabled | Qt.ItemIsUserCheckable | Qt.ItemIsSelectable)
            checker.setCheckState(Qt.Checked if row.get("apply") else Qt.Unchecked)
            checker.setToolTip(row.get("note", ""))
            self._preview_table.setItem(position, 0, checker)
            values = [position + 1, row.get("name", ""),
                      row.get("state", "") + (" ⚠" if row.get("logo") and not row.get("ok_url")
                                              else ""),
                      row.get("logo", ""), row.get("source", "")]
            for column, value in enumerate(values, start=1):
                cell = QTableWidgetItem("" if value is None else str(value))
                cell.setFlags(Qt.ItemIsEnabled | Qt.ItemIsSelectable)
                if column == 4:
                    cell.setToolTip(row.get("note", ""))
                if column == 5:
                    cell.setToolTip(str(row.get("logo", "")))
                self._preview_table.setItem(position, column, cell)
            state_cell = self._preview_table.item(position, 3)
            if state_cell is not None:
                state_cell.setForeground(self.dlg_state_color(row.get("state", "")))
                state_cell.setToolTip(str(row.get("note", "")))
            if row.get("logo") and not row.get("ok_url"):
                logo_cell = self._preview_table.item(position, 4)
                if logo_cell is not None:
                    logo_cell.setText("⚠ " + str(row.get("logo")))
                    logo_cell.setForeground(QColor("#9a6b00"))
        text = m3ule_logo_summary_text(self._plan)
        if len(self._plan["rows"]) > len(rows):
            text += f"（预览前 {len(rows)} 条）"
        self._lbl_summary.setText(text)

    def dlg_set_all_checked(self, checked: bool, only_auto: bool = False) -> None:
        rows = self._plan.get("rows", [])[:self._preview_table.rowCount()]
        for position, row in enumerate(rows):
            item = self._preview_table.item(position, 0)
            if item is None or (only_auto and not row.get("apply")):
                continue
            item.setCheckState(Qt.Checked if checked else Qt.Unchecked)

    def dlg_checked_count(self) -> int:
        count = 0
        for position in range(self._preview_table.rowCount()):
            item = self._preview_table.item(position, 0)
            if item is not None and item.checkState() == Qt.Checked:
                count += 1
        return count

    def dlg_effective_rows(self) -> list:
        """预览里勾选的行（没显示出来的行沿用默认结论）。"""
        rows: list = []
        for index, row in enumerate(self._plan.get("rows", [])):
            checked = bool(row.get("apply"))
            item = (self._preview_table.item(index, 0)
                    if index < self._preview_table.rowCount() else None)
            if item is not None:
                checked = item.checkState() == Qt.Checked
            rows.append(dict(row, apply=bool(checked and (row.get("logo") or "").strip())))
        return rows

    def dlg_accept(self, *, notify: bool = True) -> None:
        if not self._plan.get("rows"):
            if notify:
                QMessageBox.information(self, "提示", "请先点「开始匹配」读取来源并预览结果。")
            return
        if not self.dlg_checked_count():
            if notify:
                QMessageBox.information(
                    self, "提示", "当前没有勾选任何要写入的台标（勾选「应用」列的第一栏即可）。")
            return
        self.accept()

    def dlg_apply_to_document(self, document=None) -> int:
        """把勾选的行写进 tvg-logo，返回真正改动的条数；按设置顺手存进台标库。"""
        rows = self.dlg_effective_rows()
        changed = m3ule_logo_apply_rows(document if document is not None else self._document, rows)
        if changed and self._chk_store.isChecked() and self._history is not None:
            self._history.dbh_upsert_logo_map(m3ule_logo_db_rows(rows), "自动匹配")
            self.dlg_refresh_library_stats()
        self._applied = changed
        return changed

    def dlg_last_applied(self) -> int:
        return self._applied

    # -- 导入导出 ------------------------------------------------------------
    def dlg_export_preview_csv(self) -> bool:
        if not self._plan.get("rows"):
            QMessageBox.information(self, "提示", "还没有预览结果。")
            return False
        path, _filter = QFileDialog.getSaveFileName(
            self, "导出预览结果", "台标匹配预览.csv", "CSV 文件 (*.csv)")
        if not path:
            return False
        with open(path, "w", encoding="utf-8-sig", newline="") as handle:
            writer = csv.writer(handle)
            writer.writerows(m3ule_logo_plan_csv_rows(self._plan))
        self._lbl_summary.setText(f"已导出预览：{path}")
        return True

    def dlg_export_logo_map_csv(self) -> bool:
        records = self.dlg_library_records()
        if not records:
            QMessageBox.information(self, "提示", "台标库还是空的。")
            return False
        path, _filter = QFileDialog.getSaveFileName(
            self, "导出台标库", "台标库.csv", "CSV 文件 (*.csv)")
        if not path:
            return False
        with open(path, "w", encoding="utf-8-sig", newline="") as handle:
            writer = csv.writer(handle)
            writer.writerows(m3ule_logo_map_csv_rows(records))
        self._lbl_summary.setText(f"已导出台标库 {len(records)} 条：{path}")
        return True

    def dlg_logo_map_rows_for_text(self, text: str, path: str, label: str) -> list:
        """台标库文件内容 → 入库行：JSON 走 JSON 解析，其余按 CSV（两列或带表头）解析。"""
        if os.path.splitext(path)[1].lower() == ".json":
            learned = m3ule_logo_learn_from_json_text(text)
            return [{"name": name, "logo": logo, "source": label}
                    for name, logo in learned.items()]
        return m3ule_logo_map_parse_csv(text)

    def dlg_import_logo_map_path(self, path: str, label: str = "CSV 导入",
                                 *, notify: bool = True) -> int:
        """把一个台标库文件（CSV / JSON）导进数据库台标库，返回导入条数。"""
        try:
            with open(path, "rb") as handle:
                text, _encoding = M3ULiveEditorDocument.doc_decode_bytes(handle.read())
        except OSError as exc:
            if notify:
                QMessageBox.information(self, "提示", f"读取失败：{exc}")
            return 0
        rows = self.dlg_logo_map_rows_for_text(text, path, label)
        if not rows or self._history is None:
            if notify:
                QMessageBox.information(
                    self, "提示", "这个文件里没有可用的「频道名, 台标地址」记录。")
            return 0
        count = self._history.dbh_upsert_logo_map(rows, label)
        self.dlg_refresh_library_stats()
        self._lbl_summary.setText(
            f"已导入 {count} 条到台标库（当前 {self._history.dbh_count_logo_map()} 条）。")
        return count

    def dlg_import_logo_map_csv(self, *, notify: bool = True) -> int:
        path, _filter = QFileDialog.getOpenFileName(
            self, "导入台标库（CSV / JSON，两列「频道名, 台标地址」即可）",
            m3ule_get_data_dir(), "台标库文件 (*.csv *.json *.txt);;所有文件 (*.*)")
        if not path:
            return 0
        label = "JSON 导入" if os.path.splitext(path)[1].lower() == ".json" else "CSV 导入"
        return self.dlg_import_logo_map_path(path, label, notify=notify)

    def dlg_clear_logo_map(self, *, notify: bool = True) -> int:
        if self._history is None:
            return 0
        if notify:
            reply = QMessageBox.question(
                self, "清空台标库",
                "确定清空已保存的台标库吗？（只影响程序里的台标库，不动任何 m3u 文件）",
                QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
            if reply != QMessageBox.Yes:
                return 0
        count = self._history.dbh_clear_logo_map()
        self.dlg_refresh_library_stats()
        self._lbl_summary.setText(f"已清空台标库（{count} 条）。")
        return count

    # -- 设置持久化 ----------------------------------------------------------
    def dlg_persist_config(self) -> None:
        if self._config is None or self._loading:
            return
        self._config.cfg_set("logo/sources",
                             json.dumps(self.dlg_source_list(), ensure_ascii=False))
        for key, attribute in self.M3ULE_SOURCE_SETTING_KEYS:
            if attribute == "sources":
                continue
            widget = getattr(self, f"_chk_{attribute}")
            self._config.cfg_set(key, bool(widget.isChecked()))

    def dlg_reload_from_config(self) -> None:
        """读回上次的来源列表与选项。

        读的过程中要挂起「改动即落盘」（`_loading`），否则加来源时会把还没填好的
        勾选状态（默认未勾）写回去，把上次的设置冲掉。
        """
        self._loading = True
        try:
            for key, attribute in self.M3ULE_SOURCE_SETTING_KEYS:
                if attribute == "sources":
                    continue
                widget = getattr(self, f"_chk_{attribute}")
                default = self.M3ULE_SOURCE_DEFAULTS[attribute]
                value = (bool(self._config.cfg_get(key, default))
                         if self._config is not None else default)
                widget.blockSignals(True)
                widget.setChecked(value)
                widget.blockSignals(False)
            raw = ""
            if self._config is not None:
                raw = str(self._config.cfg_get("logo/sources", "") or "")
            sources: list = []
            if raw:
                try:
                    loaded = json.loads(raw)
                except (ValueError, TypeError):
                    loaded = None
                if isinstance(loaded, list):
                    sources = [item for item in loaded if isinstance(item, dict)]
            for source in sources:
                kind = str(source.get("kind") or "")
                value = str(source.get("value") or "")
                if kind in dict(M3ULE_LOGO_SOURCE_KINDS) and value:
                    self.dlg_add_source(kind, value, str(source.get("prefix") or ""))
        finally:
            self._loading = False
        self.dlg_refresh_head_epg_label()

    def dlg_close_worker(self) -> None:
        """关窗/取消时请求停止后台读取；还在跑的线程先摘掉父级，避免被销毁在运行中。"""
        worker = self._worker
        self._worker = None
        if worker is None:
            return
        worker.lsw_request_cancel()
        worker.requestInterruption()
        if worker.isRunning() and not worker.wait(3000):
            m3ule_logo_orphan_worker(worker)

    def closeEvent(self, event) -> None:  # noqa: N802 - Qt 命名
        self.dlg_close_worker()
        super().closeEvent(event)


# ----------------------------------------------------------------------------
# 对话框：批量查找替换
# ----------------------------------------------------------------------------

class M3ULiveEditorBatchReplaceDialog(QDialog):
    """在指定字段中批量查找替换（支持正则）。"""

    M3ULE_SCOPE_FIELDS = [
        ("全部字段", ["name", "tvg-name", "group-title", "tvg-id", "channelID",
                     "tvg-chno", "tvg-logo", "url"]),
        ("频道名称", ["name"]),
        ("分组", ["group-title"]),
        ("链接", ["url"]),
        ("tvg-id", ["tvg-id"]),
        ("channelID", ["channelID"]),
        ("频道号", ["tvg-chno"]),
        ("台标", ["tvg-logo"]),
        ("备注", ["remark"]),
    ]

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("批量查找替换")
        self.resize(600, 380)
        root = QVBoxLayout(self)
        root.setContentsMargins(10, 10, 10, 10)
        root.setSpacing(6)

        form = QFormLayout()
        self._combo_scope = QComboBox()
        for label, _ in self.M3ULE_SCOPE_FIELDS:
            self._combo_scope.addItem(label)
        form.addRow("字段范围：", self._combo_scope)
        self._edit_find = QLineEdit()
        form.addRow("查找内容：", self._edit_find)
        self._edit_replace = QLineEdit()
        form.addRow("替换为：", self._edit_replace)
        root.addLayout(form)

        option_row = QHBoxLayout()
        self._chk_regex = QCheckBox("使用正则表达式")
        self._chk_case = QCheckBox("区分大小写")
        self._chk_selected = QCheckBox("仅在当前选中条目中替换")
        option_row.addWidget(self._chk_regex)
        option_row.addWidget(self._chk_case)
        option_row.addWidget(self._chk_selected)
        option_row.addStretch(1)
        root.addLayout(option_row)

        self._lbl_preview = QLabel("点击“预览匹配”查看将修改的条目数。")
        self._lbl_preview.setWordWrap(True)
        self._lbl_preview.setStyleSheet("color:#1a73e8;")
        root.addWidget(self._lbl_preview)
        root.addStretch(1)

        buttons = QDialogButtonBox()
        btn_preview = buttons.addButton("预览匹配", QDialogButtonBox.ActionRole)
        btn_preview.clicked.connect(self.dlg_refresh_preview)
        buttons.addButton("确定替换", QDialogButtonBox.AcceptRole).clicked.connect(self.accept)
        buttons.addButton("取消", QDialogButtonBox.RejectRole).clicked.connect(self.reject)
        root.addWidget(buttons)

    def dlg_matched_uids(self, document, selected_uids=None) -> list:
        find_text = self._edit_find.text()
        if not find_text:
            return []
        fields = dict(self.M3ULE_SCOPE_FIELDS)[self._combo_scope.currentText()]
        pattern = None
        if self._chk_regex.isChecked():
            flags = 0 if self._chk_case.isChecked() else re.IGNORECASE
            try:
                pattern = re.compile(find_text, flags)
            except re.error:
                return []
        needle = find_text if self._chk_case.isChecked() else find_text.lower()
        selected = set(selected_uids or [])
        matched = []
        for entry in document.entries:
            if self._chk_selected.isChecked() and selected and entry.uid not in selected:
                continue
            for field in fields:
                value = self._field_value(entry, field)
                if pattern is not None:
                    if pattern.search(value or ""):
                        matched.append(entry.uid)
                        break
                else:
                    haystack = value if self._chk_case.isChecked() else (value or "").lower()
                    if needle and needle in haystack:
                        matched.append(entry.uid)
                        break
        return matched

    @staticmethod
    def _field_value(entry, field: str) -> str:
        if field == "name":
            return entry.title or ""
        if field == "url":
            return entry.url or ""
        if field == "remark":
            return entry.remark or ""
        return entry.entry_get_attr(field)

    def _patterns(self):
        find_text = self._edit_find.text()
        if not find_text:
            return None
        replace_text = self._edit_replace.text()
        if self._chk_regex.isChecked():
            flags = 0 if self._chk_case.isChecked() else re.IGNORECASE
            try:
                return re.compile(find_text, flags), replace_text
            except re.error:
                return None
        return find_text, replace_text

    def dlg_apply_replacements(self, document, selected_uids=None) -> int:
        patterns = self._patterns()
        if patterns is None:
            return 0
        finder, replacer = patterns
        fields = dict(self.M3ULE_SCOPE_FIELDS)[self._combo_scope.currentText()]
        selected = set(selected_uids or [])
        changed = 0
        for entry in document.entries:
            if self._chk_selected.isChecked() and selected and entry.uid not in selected:
                continue
            entry_changed = False
            for field in fields:
                old_value = self._field_value(entry, field)
                if isinstance(finder, re.Pattern):
                    if not finder.search(old_value or ""):
                        continue
                    new_value = finder.sub(replacer, old_value)
                else:
                    if self._chk_case.isChecked():
                        if finder not in (old_value or ""):
                            continue
                        new_value = (old_value or "").replace(finder, replacer)
                    else:
                        if finder.lower() not in (old_value or "").lower():
                            continue
                        new_value = re.sub(re.escape(finder), lambda _m: replacer,
                                           old_value, flags=re.IGNORECASE)
                if new_value == old_value:
                    continue
                self._set_field_value(entry, field, new_value)
                entry_changed = True
            if entry_changed:
                entry.entry_rebuild_extinf_line()
                changed += 1
        if changed:
            document.modified = True
        return changed

    @staticmethod
    def _set_field_value(entry, field: str, value: str) -> None:
        if field == "name":
            entry.title = value
        elif field == "url":
            entry.url = value
        elif field == "remark":
            entry.remark = value
        else:
            entry.entry_set_attr(field, value)

    def dlg_refresh_preview(self) -> None:
        document = getattr(self, "_document", None)
        if document is None:
            self._lbl_preview.setText("尚无可替换的文档。")
            return
        uids = self.dlg_matched_uids(document, getattr(self, "_selected_uids", None))
        self._lbl_preview.setText(f"将在 {len(uids)} 条记录中执行替换。" if uids else "没有匹配到任何内容。")

    def dlg_set_context(self, document, selected_uids=None) -> None:
        self._document = document
        self._selected_uids = list(selected_uids or [])


# ----------------------------------------------------------------------------
# 对话框：HTML5 播放弹窗
# ----------------------------------------------------------------------------

class M3ULiveEditorQtMultimediaBackend(QWidget):
    """Qt 多媒体播放内核：FFmpeg 直接拉流，不依赖 Chromium / GL 上下文。"""

    def __init__(self, parent=None):
        super().__init__(parent)
        self._layout = QVBoxLayout(self)
        self._layout.setContentsMargins(0, 0, 0, 0)
        self._player = None
        self._audio = None
        self._video = None
        self._sink = None
        self._frames = 0
        self._frames_last = 0
        self._error = ""
        self._status = "未开始"
        self._url = ""
        if not M3ULE_QTMM_AVAILABLE:
            label = QLabel(f"QtMultimedia 不可用：{M3ULE_QTMM_ERROR}")
            label.setAlignment(Qt.AlignCenter)
            label.setWordWrap(True)
            self._layout.addWidget(label)
            return
        self._video = QVideoWidget(self)
        self._layout.addWidget(self._video, 1)
        self._player = QMediaPlayer(self)
        self._audio = QAudioOutput(self)
        self._player.setAudioOutput(self._audio)
        self._player.setVideoOutput(self._video)
        self._player.errorOccurred.connect(self.bkd_on_error)
        self._player.mediaStatusChanged.connect(self.bkd_on_media_status)
        try:
            self._sink = self._video.videoSink()
            self._sink.videoFrameChanged.connect(self.bkd_on_frame)
        except Exception:  # noqa: BLE001
            self._sink = None

    # -- 统一接口 -----------------------------------------------------------
    def bkd_start(self, url: str, title: str = "") -> bool:
        if self._player is None:
            return False
        self._frames = 0
        self._frames_last = 0
        self._error = ""
        self._url = url or ""
        self._status = "正在打开…"
        try:
            self._player.stop()
            self._player.setSource(QUrl(self._url))
            self._player.play()
        except Exception as exc:  # noqa: BLE001
            self._error = f"{type(exc).__name__}: {exc}"
            self._status = "打开失败"
            return False
        return True

    def bkd_stop(self) -> None:
        if self._player is None:
            return
        try:
            self._player.stop()
            self._player.setSource(QUrl())
        except Exception:  # noqa: BLE001
            pass
        self._status = "已停止"

    def bkd_status(self) -> str:
        if self._player is None:
            return f"QtMultimedia 不可用（{M3ULE_QTMM_ERROR}）"
        if self._error:
            return f"播放错误：{self._error}"
        return self._status

    def bkd_progress(self) -> tuple:
        """(已解码帧数, 播放位置毫秒) —— 用于判断内核是否真的出画。"""
        if self._player is None:
            return 0, 0
        try:
            return self._frames, int(self._player.position())
        except Exception:  # noqa: BLE001
            return self._frames, 0

    def bkd_error(self) -> str:
        return self._error

    # -- 内部槽 -------------------------------------------------------------
    @Slot()
    def bkd_on_frame(self, _frame=None) -> None:
        self._frames += 1

    @Slot()
    def bkd_on_error(self, _error=None, message: str = "") -> None:
        self._error = str(message or "").strip() or "未知错误"
        self._status = "播放错误"

    @Slot()
    def bkd_on_media_status(self, status=None) -> None:
        text = str(status or "")
        if "InvalidMedia" in text or "NoMedia" in text:
            self._status = "无法识别的媒体流"
        elif "BufferedMedia" in text or "BufferingMedia" in text:
            size = ""
            try:
                if self._video is not None:
                    size = f"（{self._video.width()}x{self._video.height()}）"
            except Exception:  # noqa: BLE001
                size = ""
            self._status = f"正在播放{size}"
        elif "LoadingMedia" in text or "LoadedMedia" in text:
            self._status = "缓冲中…"
        elif "EndOfMedia" in text:
            self._status = "播放结束"
        elif "StalledMedia" in text:
            self._status = "缓冲停滞"


class M3ULiveEditorVlcBackend(QWidget):
    """VLC 播放内核：python-vlc + libvlc，用 set_hwnd 把画面嵌进本控件。

    两条硬约束（都是实测踩出来的）：

    1. 一个控件只允许存在一个**正在播**的播放器：libvlc 的每个 media_player 都是独立
       解码器，换台时若新建播放器而不停掉旧的，会出现「两路一起播」；旧播放器失去宿主
       窗口后还会自己弹出一个独立的输出窗口（关不掉、也停不了）。所以每次换台都给新播放器
       准备**自己的宿主控件**，旧宿主原地隐藏（画面不会跑出去）。
    2. `stop()` / `release()` **绝不能在 GUI 线程调用**：实测同一路流在 GUI 线程里
       `stop()` 要 3.5 秒，源不稳定时甚至一直不返回（vout 窗口的销毁需要 GUI 线程处理
       消息，而 GUI 线程正阻塞在 stop() 上，互相等）——用户感受就是「一换内核就卡死」。
       因此停止/销毁统一交给后台线程，GUI 侧只做「立即静音 + 隐藏宿主 + 换新播放器」。
    """

    _POLL_MS = 500
    _CLEANUP_MS = 250

    def __init__(self, parent=None):
        super().__init__(parent)
        self._layout = QVBoxLayout(self)
        self._layout.setContentsMargins(0, 0, 0, 0)
        self._info = QLabel("VLC 内核")
        self._info.setStyleSheet("color:#5f6368;")
        self._info.setWordWrap(True)
        self._layout.addWidget(self._info)
        self._instance = None
        self._player = None
        self._media = None
        self._host = None
        self._hosts = []
        self._retiring = []
        self._error = ""
        self._status = "未开始"
        self._frames = 0
        self._last_time = -1
        self._timer = QTimer(self)
        self._timer.setInterval(self._POLL_MS)
        self._timer.timeout.connect(self.bkd_poll)
        self._cleanup_timer = QTimer(self)
        self._cleanup_timer.setInterval(self._CLEANUP_MS)
        self._cleanup_timer.timeout.connect(self.bkd_cleanup_retired)

    def bkd_load_module(self):
        if self._instance is not None:
            return self._instance
        try:
            import vlc  # type: ignore
        except Exception as exc:  # noqa: BLE001
            self._error = f"未安装 python-vlc：{type(exc).__name__}: {exc}"
            return None
        lib_path = m3ule_find_libvlc()
        try:
            directory = os.path.dirname(lib_path) if lib_path else ""
            if directory and hasattr(os, "add_dll_directory"):
                os.add_dll_directory(directory)
            if lib_path:
                # 先把 libvlc.dll 载入本进程：python-vlc 是按名字（libvlc.dll）加载的，
                # 若 VLC 目录不在 PATH 里，它自己可能找不到；预加载后按名字必然命中。
                m3ule_library_loadable(lib_path, prepare=False)
            # 注意：VLC 3 起 --plugin-path 已废弃（会打印 "option --plugin-path no longer exists"），
            # 插件目录由 libvlc 自己按 dll 位置定位，所以这里只把这个目录用于诊断提示。
            self._instance = vlc.Instance()
        except Exception as exc:  # noqa: BLE001
            plugins = m3ule_vlc_plugins_dir(lib_path)
            self._error = (f"libvlc 加载失败：{type(exc).__name__}: {exc}"
                           f"（可用 {M3ULE_LIBVLC_DIR_ENV} 指定 VLC 安装目录"
                           + (f"；插件目录：{plugins}" if plugins
                              else "；未找到 plugins 目录，VLC 安装可能不完整") + "）")
            return None
        if self._instance is None:
            self._error = "vlc.Instance() 返回空（libvlc 版本不匹配？）"
        return self._instance

    def bkd_host_new(self):
        """为本次播放准备**独立**的宿主控件（旧宿主留在原地隐藏）。

        复用同一个宿主控件会让新播放器把旧画面挤出去：旧 vout 失去父窗口后就会变成
        一个可见的独立顶层窗口（用户看到「多开了一个 VLC 窗口、还关不掉」）。
        """
        for old in self._hosts:
            if old is not self._host:
                try:
                    old.hide()
                except Exception:  # noqa: BLE001
                    pass
        host = QWidget(self)
        host.setStyleSheet("background:#000000;")
        # 先把原生窗口准备好：set_hwnd 要真实存在的窗口句柄，否则 libvlc 会另开窗口。
        host.setAttribute(Qt.WA_NativeWindow, True)
        self._layout.insertWidget(0, host, 1)
        self._hosts.append(host)
        self._host = host
        return host

    def bkd_detach_current(self) -> tuple:
        """摘下当前播放（立即静音 + 隐藏宿主），返回 (player, media, host)。"""
        player, media, host = self._player, self._media, self._host
        self._player, self._media, self._host = None, None, None
        if player is not None:
            try:
                player.audio_set_volume(0)      # 立刻静音：旧声音不会再和新频道一起响
            except Exception:  # noqa: BLE001
                pass
        if host is not None:
            try:
                host.hide()
            except Exception:  # noqa: BLE001
                pass
        return player, media, host

    def bkd_queue_teardown(self, player, media, instance, host) -> None:
        """把 stop/release/instance.release 交给后台线程做（GUI 线程绝不等待）。"""
        state = {"done": False}
        entry = {"state": state, "player": player, "host": host}

        def worker():
            try:
                if player is not None:
                    try:
                        player.stop()
                    except Exception:  # noqa: BLE001
                        pass
                if media is not None:
                    try:
                        media.release()
                    except Exception:  # noqa: BLE001
                        pass
                if player is not None:
                    try:
                        player.release()
                    except Exception:  # noqa: BLE001
                        pass
                if instance is not None:
                    try:
                        instance.release()
                    except Exception:  # noqa: BLE001
                        pass
            finally:
                state["done"] = True

        thread = threading.Thread(target=worker, name="m3ule-vlc-teardown", daemon=True)
        entry["thread"] = thread
        self._retiring.append(entry)
        thread.start()
        if not self._cleanup_timer.isActive():
            self._cleanup_timer.start()

    def bkd_halt(self) -> None:
        """停止当前播放：立即静音 + 隐藏宿主，把播放器交给后台线程销毁（不阻塞界面）。"""
        player, media, host = self.bkd_detach_current()
        if player is None and media is None:
            return
        self.bkd_queue_teardown(player, media, None, host)

    def bkd_cleanup_retired(self) -> None:
        """删除已经销毁完成的旧宿主控件（没有销毁完就继续等，不阻塞界面）。"""
        alive = []
        for entry in self._retiring:
            if not entry["state"]["done"]:
                alive.append(entry)
                continue
            host = entry.get("host")
            entry["host"] = None
            if host is not None:
                try:
                    self._layout.removeWidget(host)
                    self._hosts.remove(host)
                    host.setParent(None)
                    host.deleteLater()
                except Exception:  # noqa: BLE001
                    pass
        self._retiring = alive
        if not alive:
            self._cleanup_timer.stop()

    def bkd_teardown_pending(self) -> bool:
        """是否还有播放器/实例在后台销毁中（关闭窗口前可以等一下再销毁控件）。"""
        return any(not entry["state"]["done"] for entry in self._retiring)

    def bkd_start(self, url: str, title: str = "") -> bool:
        self._error = ""
        self._frames = 0
        self._last_time = -1
        # 换台先停旧路（非阻塞）：同一个控件里同时存在两路解码就会两路一起播。
        self.bkd_halt()
        instance = self.bkd_load_module()
        if instance is None:
            self._status = "内核不可用"
            return False
        host = self.bkd_host_new()
        try:
            player = instance.media_player_new()
            self._player = player
            player.set_hwnd(int(host.winId()))
            media = instance.media_new(url)
            for option in (f":http-user-agent={M3ULE_DEFAULT_USER_AGENT}", ":network-caching=1500"):
                try:
                    media.add_option(option)
                except Exception:  # noqa: BLE001
                    pass
            player.set_media(media)
            self._media = media
            if player.play() == -1:
                self._error = "VLC 拒绝播放该地址"
                self._status = "打开失败"
                return False
        except Exception as exc:  # noqa: BLE001
            self._error = f"播放异常：{type(exc).__name__}: {exc}"
            self._status = "打开失败"
            return False
        self._status = "正在打开…"
        self._timer.start()
        return True

    def bkd_poll(self) -> None:
        if self._player is None:
            return
        try:
            state = str(self._player.get_state())
            current = int(self._player.get_time() or 0)
        except Exception:  # noqa: BLE001
            return
        if current and current != self._last_time:
            self._last_time = current
            self._frames += 1
        size = ""
        try:
            width = int(self._player.video_get_width(0) or 0)
            height = int(self._player.video_get_height(0) or 0)
            if width and height:
                size = f"{width}x{height}"
        except Exception:  # noqa: BLE001
            size = ""
        self._status = " · ".join(
            part for part in (state.replace("State.", ""), size, f"{current / 1000:.1f}s") if part)
        self._info.setText(f"VLC 内核：{self._status}")

    def bkd_stop(self) -> None:
        self._timer.stop()
        self.bkd_halt()
        self._status = "已停止"
        self._info.setText("VLC 内核：已停止")

    def bkd_status(self) -> str:
        return self._error or self._status

    def bkd_progress(self) -> tuple:
        return self._frames, int(max(0, self._last_time))

    def bkd_error(self) -> str:
        return self._error

    def bkd_release(self) -> None:
        """停止播放并销毁播放器与 libvlc 实例；销毁在后台线程做，绝不阻塞界面。"""
        self._timer.stop()
        self._cleanup_timer.stop()
        player, media, host = self.bkd_detach_current()
        instance = self._instance
        self._instance = None
        if player is None and media is None and instance is None:
            return
        self.bkd_queue_teardown(player, media, instance, host)


class M3ULiveEditorFlowLayout(QLayout):
    """按可用宽度自动换行的布局（工具栏用）：窗口宽就两三行排完，窗口窄自动多折几行。

    这样既能「一行放不下时不要硬撑宽窗口」，也能在宽屏上少占几行。
    """

    def __init__(self, parent=None, margin: int = 0, spacing: int = 4):
        super().__init__(parent)
        self.setContentsMargins(margin, margin, margin, margin)
        self._flow_items = []
        self._flow_spacing = max(0, int(spacing))

    # -- QLayout 接口 -------------------------------------------------------
    def addItem(self, item) -> None:  # noqa: N802 - Qt 命名
        self._flow_items.append(item)

    def count(self) -> int:
        return len(self._flow_items)

    def itemAt(self, index):  # noqa: N802
        if 0 <= index < len(self._flow_items):
            return self._flow_items[index]
        return None

    def takeAt(self, index):  # noqa: N802
        if 0 <= index < len(self._flow_items):
            return self._flow_items.pop(index)
        return None

    def expandingDirections(self):  # noqa: N802
        return Qt.Orientations()

    def hasHeightForWidth(self) -> bool:  # noqa: N802
        return True

    def heightForWidth(self, width: int) -> int:  # noqa: N802
        return self.m3ule_flow_layout(QRect(0, 0, int(width), 0), True)

    def setGeometry(self, rect: QRect) -> None:  # noqa: N802
        super().setGeometry(rect)
        self.m3ule_flow_layout(rect, False)

    def sizeHint(self) -> QSize:  # noqa: N802
        return self.minimumSize()

    def minimumSize(self) -> QSize:  # noqa: N802
        """最小尺寸＝最宽的一个控件（这样窗口可以缩到很窄，由自动换行去承接）。"""
        size = QSize()
        for item in self._flow_items:
            size = size.expandedTo(item.minimumSize())
        margins = self.contentsMargins()
        return size + QSize(margins.left() + margins.right(),
                            margins.top() + margins.bottom())

    # -- 布局算法 ==========================================================
    def m3ule_item_size(self, item) -> QSize:
        """控件的实际排布尺寸：把 sizeHint 夹在 minimumSize / maximumSize 之间。

        下拉框的 sizeHint 可能大于我们设的 maximumWidth（例如超长频道名），
        用夹过的尺寸参与换行计算，行宽才和实际显示一致。
        """
        hint = item.sizeHint()
        width, height = hint.width(), hint.height()
        maximum = item.maximumSize()
        if maximum.width() > 0:
            width = min(width, maximum.width())
        if maximum.height() > 0:
            height = min(height, maximum.height())
        minimum = item.minimumSize()
        width = max(width, minimum.width())
        height = max(height, minimum.height())
        return QSize(width, height)

    def m3ule_flow_layout(self, rect, test_only: bool) -> int:
        margins = self.contentsMargins()
        area = rect.adjusted(margins.left(), margins.top(),
                             -margins.right(), -margins.bottom())
        x, y = area.x(), area.y()
        line_height = 0
        for item in self._flow_items:
            hint = self.m3ule_item_size(item)
            next_x = x + hint.width() + self._flow_spacing
            if next_x - self._flow_spacing > area.right() and line_height > 0:
                x = area.x()
                y = y + line_height + self._flow_spacing
                next_x = x + hint.width() + self._flow_spacing
                line_height = 0
            if not test_only:
                item.setGeometry(QRect(QPoint(x, y), hint))
            x = next_x
            line_height = max(line_height, hint.height())
        return y + line_height - rect.y() + margins.bottom()

    def m3ule_row_count(self, width: int = 0) -> int:
        """给定宽度会排成几行（0＝用当前宽度）；供界面自检与测试使用。"""
        if width <= 0:
            width = max(1, self.geometry().width())
        margins = self.contentsMargins()
        area = QRect(0, 0, int(width) - margins.left() - margins.right(), 0)
        rows = 0
        x = 0
        line_height = 0
        for item in self._flow_items:
            hint = self.m3ule_item_size(item)
            next_x = x + hint.width() + self._flow_spacing
            if next_x - self._flow_spacing > area.right() and line_height > 0:
                rows += 1
                x = 0
                next_x = x + hint.width() + self._flow_spacing
                line_height = 0
            x = next_x
            line_height = max(line_height, hint.height())
        if line_height:
            rows += 1
        return rows


class M3ULiveEditorHtml5PlayerDialog(QDialog):
    """弹窗播放器：在 FFmpeg（Qt 多媒体）与 VLC（libvlc）两个内核之间切换，并在频道间切换。

    类名与 `player/html5_*` 设置键保留历史名称以兼容既有文档、设置与代码。
    """

    M3ULE_HTML5_GEOMETRY_KEY = "ui/geometry/html5_player"

    def __init__(self, main_window, entries: list, start_index: int = 0, parent=None):
        super().__init__(parent or main_window)
        self._main_window = main_window
        self._entries = [entry for entry in (entries or []) if (entry.url or "").strip()]
        self._index = 0
        if self._entries:
            self._index = max(0, min(int(start_index), len(self._entries) - 1))
        self._pending_url = ""
        self._last_url = ""
        self._stall_retries = 0
        self._stall_timer = None
        self._backend_key = M3ULE_PLAYER_BACKEND_DEFAULT
        self._backend_widget = None
        self._retired_widgets = []
        self._retired_timer = None
        self._backend_chain = []
        self._backend_index = 0
        self._backend_switch_count = 0
        self._backend_combo_keys = []
        self._backend_errors = []

        self.setWindowTitle(f"播放器（{M3ULE_PLAYER_BACKEND_LABELS[M3ULE_PLAYER_BACKEND_DEFAULT]}）")
        self.setSizeGripEnabled(True)
        self.resize(940, 620)
        self.setAttribute(Qt.WA_DeleteOnClose, False)

        root = QVBoxLayout(self)
        root.setContentsMargins(4, 4, 4, 4)
        root.setSpacing(4)

        # 工具栏用「自动换行」布局：宽窗口时两三行就排完，窄窗口自动折行，不会把窗口顶宽
        bar = M3ULiveEditorFlowLayout(spacing=4)
        self._btn_prev = QPushButton("◀ 上一个")
        self._btn_prev.setToolTip("切换到上一个频道（循环；打开弹窗时会带上整个频道列表）")
        self._btn_prev.clicked.connect(lambda: self.dlg_step_entry(-1))
        bar.addWidget(self._btn_prev)
        self._btn_next = QPushButton("下一个 ▶")
        self._btn_next.setToolTip("切换到下一个频道（循环；可用上方下拉直接跳转）")
        self._btn_next.clicked.connect(lambda: self.dlg_step_entry(1))
        bar.addWidget(self._btn_next)
        self._lbl_index = QLabel("—")
        bar.addWidget(self._lbl_index)
        self._combo_entries = QComboBox()
        # 宽度跟着内容走（长频道名最多到上限，不会把工具栏顶宽）
        self._combo_entries.setSizeAdjustPolicy(QComboBox.AdjustToContents)
        self._combo_entries.setMinimumContentsLength(10)
        self._combo_entries.setMinimumWidth(110)
        self._combo_entries.setMaximumWidth(M3ULE_PLAYER_COMBO_MAX_WIDTH)
        self.dlg_fill_entries_combo(self._entries, self._index)
        self._combo_entries.currentIndexChanged.connect(self.dlg_on_combo_changed)
        bar.addWidget(self._combo_entries)
        self._btn_reload = QPushButton("重新加载")
        self._btn_reload.clicked.connect(self.dlg_reload_page)
        bar.addWidget(self._btn_reload)
        self._btn_stop = QPushButton("停止")
        self._btn_stop.clicked.connect(self.dlg_stop_playback)
        bar.addWidget(self._btn_stop)
        self._bar_nav = [self._btn_prev, self._btn_next, self._lbl_index,
                         self._combo_entries, self._btn_reload, self._btn_stop]
        root.addLayout(bar)

        self._btn_diagnose = QPushButton("诊断")
        self._btn_diagnose.setToolTip("查看播放内核状态、画面进度与中转请求情况")
        self._btn_diagnose.clicked.connect(self.dlg_show_playback_diagnostics)
        bar.addWidget(self._btn_diagnose)
        self._lbl_kernel = QLabel("内核")
        bar.addWidget(self._lbl_kernel)
        self._combo_backend = QComboBox()
        self._combo_backend.setSizeAdjustPolicy(QComboBox.AdjustToContents)
        self._combo_backend.setMinimumContentsLength(8)
        self._combo_backend.setMinimumWidth(120)
        self._combo_backend.setMaximumWidth(M3ULE_PLAYER_COMBO_MAX_WIDTH)
        self._combo_backend.setToolTip(
            "弹窗播放内核（只有两个）：FFmpeg（内嵌 Qt 多媒体，默认）与 VLC（libvlc）。\n"
            "当前内核打不开画面时会自动换用另一个可用内核。")
        self._combo_backend.currentIndexChanged.connect(self.dlg_on_backend_combo_changed)
        bar.addWidget(self._combo_backend)
        self._btn_backend_report = QPushButton("内核检查")
        self._btn_backend_report.setToolTip("查看本机各播放内核是否可用及其原因")
        self._btn_backend_report.clicked.connect(self.dlg_show_backend_report)
        bar.addWidget(self._btn_backend_report)
        self._bar_kernel = [self._btn_diagnose, self._lbl_kernel,
                            self._combo_backend, self._btn_backend_report]

        self._btn_external = QPushButton("用播放器打开")
        self._btn_external.clicked.connect(self.dlg_open_external_player)
        bar.addWidget(self._btn_external)
        self._btn_browser = QPushButton("在系统浏览器打开")
        self._btn_browser.clicked.connect(self.dlg_open_system_browser)
        bar.addWidget(self._btn_browser)
        self._btn_copy = QPushButton("复制链接")
        self._btn_copy.clicked.connect(self.dlg_copy_current_url)
        bar.addWidget(self._btn_copy)
        self._btn_save_html = QPushButton("另存播放页")
        self._btn_save_html.setToolTip("把当前播放页保存为 HTML 文件（可在任意浏览器打开，需保持本程序运行）")
        self._btn_save_html.clicked.connect(self.dlg_save_player_html)
        bar.addWidget(self._btn_save_html)
        self._bar_tools = [self._btn_external, self._btn_browser, self._btn_copy,
                           self._btn_save_html]
        self._toolbar_flow = bar

        self._stack = QStackedWidget()
        root.addWidget(self._stack, 1)
        self._fallback_label = QLabel()
        self._fallback_label.setAlignment(Qt.AlignCenter)
        self._fallback_label.setWordWrap(True)
        self._stack.addWidget(self._fallback_label)
        self.dlg_fill_backend_combo()
        self.dlg_setup_backend_chain()
        placeholder = QLabel("正在初始化播放内核…")
        placeholder.setAlignment(Qt.AlignCenter)
        self._stack.addWidget(placeholder)
        self._stack.setCurrentIndex(1)

        self._lbl_status = QLabel("就绪")
        self._lbl_status.setWordWrap(True)
        self._lbl_status.setTextInteractionFlags(Qt.TextSelectableByMouse)
        self._lbl_status.setStyleSheet("color:#5f6368;")
        self._lbl_status.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Preferred)
        root.addWidget(self._lbl_status)

        foot = QHBoxLayout()
        self._chk_autoplay = QCheckBox("自动播放")
        self._chk_autoplay.setChecked(bool(main_window.wnd_config_manager().cfg_get("player/html5_autoplay")))
        self._chk_autoplay.toggled.connect(self.dlg_on_autoplay_toggled)
        foot.addWidget(self._chk_autoplay)
        self._lbl_relay = QLabel("")
        self._lbl_relay.setStyleSheet("color:#5f6368;")
        self._lbl_relay.setWordWrap(True)
        foot.addWidget(self._lbl_relay, 1)
        root.addLayout(foot)

        self.dlg_restore_geometry()
        self.dlg_refresh_nav_state()
        if self._entries:
            self.dlg_play_index(self._index)

    # -- 播放内核管理 -------------------------------------------------------
    def dlg_fill_backend_combo(self) -> None:
        """把可选内核填入下拉框：只有 FFmpeg 与 VLC（不可用的标注）。"""
        self._combo_backend.blockSignals(True)
        self._combo_backend.clear()
        self._backend_combo_keys = []
        for key, label, ok, _reason in m3ule_player_backend_report():
            self._combo_backend.addItem(label if ok else f"{label}（不可用）")
            self._backend_combo_keys.append(key)
        self._combo_backend.blockSignals(False)

    def dlg_setup_backend_chain(self) -> None:
        """按设置与可用性算出内核尝试顺序；_backend_key 为当前使用中的内核。"""
        configured = self._main_window.wnd_config_manager().cfg_get("player/backend")
        configured_key = m3ule_player_backend_key(configured)
        self._backend_chain = m3ule_player_backend_chain(configured) or [configured_key]
        self._backend_index = 0
        previous = self._backend_key
        self._backend_key = self._backend_chain[0]
        if self._backend_key != previous:
            # 换内核前必须先停掉旧内核，否则旧内核会留在后台和新内核一起播。
            self.dlg_stop_playback(silent=True)
        if configured_key != self._backend_key:
            self._main_window.wnd_append_log(
                f"已配置的播放内核「{m3ule_player_backend_label(configured_key)}」在本机不可用"
                f"（{m3ule_player_backend_status(configured_key)[1]}），"
                f"本次改用「{m3ule_player_backend_label(self._backend_key)}」。")
        self.dlg_select_backend_combo_item(self._backend_key)

    def dlg_select_backend_combo_item(self, key: str) -> None:
        index = self._backend_combo_keys.index(key) if key in self._backend_combo_keys else -1
        self._combo_backend.blockSignals(True)
        self._combo_backend.setCurrentIndex(max(0, index))
        self._combo_backend.blockSignals(False)

    def dlg_current_backend(self) -> str:
        return self._backend_key

    def dlg_target_url(self, entry) -> str:
        """当前内核应当播放的地址（两个内核都直连拉流，不需要本机中转）。"""
        if entry is None:
            return ""
        return (entry.url or "").strip()

    def dlg_backend_widgets(self) -> list:
        """弹窗里现存的内核控件（换内核时会销毁上一个，所以正常最多一个）。"""
        found = []
        stack = getattr(self, "_stack", None)
        if stack is None:
            return found
        for index in range(stack.count()):
            widget = stack.widget(index)
            if widget is not None and hasattr(widget, "bkd_stop") and hasattr(widget, "bkd_status"):
                found.append(widget)
        return found

    def dlg_backend_teardown_pending(self) -> bool:
        """是否还有内核控件在后台销毁中（libvlc 的停止/销毁只能后台做）。"""
        for widget in self.dlg_backend_widgets() + self._retired_widgets:
            pending = getattr(widget, "bkd_teardown_pending", None)
            if callable(pending) and pending():
                return True
        return False

    def dlg_wait_backend_teardown(self, seconds: float = 1.5) -> bool:
        """给「后台销毁播放器」一点时间（关闭窗口前用），返回是否已经全部结束。"""
        deadline = time.time() + max(0.0, float(seconds))
        while True:
            if not self.dlg_backend_teardown_pending():
                return True
            if time.time() >= deadline:
                return False
            time.sleep(0.05)

    def dlg_start_retired_sweep(self) -> None:
        """开始轮询「被移除的内核控件」后台销毁是否完成（完成后再 deleteLater）。"""
        if self._retired_timer is None:
            self._retired_timer = QTimer(self)
            self._retired_timer.setInterval(300)
            self._retired_timer.timeout.connect(self.dlg_sweep_retired_widgets)
        self._retired_timer.start()

    def dlg_sweep_retired_widgets(self) -> None:
        """把后台已经销毁完的内核控件真正删掉（没销毁完就继续等，不阻塞界面）。"""
        alive = []
        for widget in self._retired_widgets:
            pending = getattr(widget, "bkd_teardown_pending", None)
            if callable(pending) and pending():
                alive.append(widget)
                continue
            try:
                widget.setParent(None)
                widget.deleteLater()
            except Exception:  # noqa: BLE001
                pass
        self._retired_widgets = alive
        if not alive and self._retired_timer is not None:
            self._retired_timer.stop()

    def dlg_dispose_backend_widget(self, widget) -> None:
        """停止并销毁一个内核控件：停止播放 → 释放库资源 → 从界面移除。

        换内核时必须走这里：只把旧控件从界面换掉而不停止/释放，旧内核（尤其 libvlc、
        mpv）会继续在后台播放，表现就是「两个一起播、还关不掉」。
        注意：libvlc 的停止/销毁只能在后台线程做（在 GUI 线程里会卡住界面），所以这里
        先隐藏并移出界面，等它报告「销毁完成」再真正删除。
        """
        if widget is None:
            return
        for name in ("bkd_stop", "bkd_release"):
            action = getattr(widget, name, None)
            if action is None:
                continue
            try:
                action()
            except Exception:  # noqa: BLE001
                pass
        try:
            self._stack.removeWidget(widget)
        except Exception:  # noqa: BLE001
            pass
        if self._backend_widget is widget:
            self._backend_widget = None
        try:
            widget.hide()
        except Exception:  # noqa: BLE001
            pass
        pending = getattr(widget, "bkd_teardown_pending", None)
        if callable(pending) and pending():
            self._retired_widgets.append(widget)
            self.dlg_start_retired_sweep()
            return
        try:
            widget.setParent(None)
            widget.deleteLater()
        except Exception:  # noqa: BLE001
            pass

    def dlg_release_backends(self) -> None:
        """释放所有内核控件的库资源（VLC 播放器/实例、mpv 实例）。"""
        for widget in self.dlg_backend_widgets():
            action = getattr(widget, "bkd_release", None)
            if action is None:
                continue
            try:
                action()
            except Exception:  # noqa: BLE001
                pass

    def dlg_ensure_backend_widget(self, key: str):
        """按内核创建对应播放控件。"""
        if self._backend_widget is not None and getattr(
                self._backend_widget, "M3ULE_BACKEND_KEY", "") == key:
            self._stack.setCurrentWidget(self._backend_widget)
            return self._backend_widget
        widget = None
        try:
            if key == "qtmm":
                widget = M3ULiveEditorQtMultimediaBackend(self)
            elif key == "vlc":
                widget = M3ULiveEditorVlcBackend(self)
        except Exception as exc:  # noqa: BLE001
            self._main_window.wnd_append_log(
                f"创建播放内核 {key} 失败：{type(exc).__name__}: {exc}")
            return None
        if widget is None:
            return None
        widget.M3ULE_BACKEND_KEY = key
        self.dlg_dispose_backend_widget(self._backend_widget)
        self._backend_widget = widget
        self._stack.addWidget(widget)
        self._stack.setCurrentWidget(widget)
        return widget

    def dlg_activate_backend(self, key: str, persist: bool = False) -> bool:
        """切换当前内核（可选写入设置），并停止旧内核的播放。"""
        key = m3ule_player_backend_key(key)
        if key not in M3ULE_PLAYER_BACKEND_CHAIN:
            key = M3ULE_PLAYER_BACKEND_DEFAULT
        if key != self._backend_key:
            self.dlg_stop_playback(silent=True)
            self._backend_key = key
        if persist:
            self._main_window.wnd_config_manager().cfg_set(
                "player/backend", m3ule_player_backend_label(key))
        self.dlg_select_backend_combo_item(key)
        return True

    def dlg_advance_backend(self) -> bool:
        """内核回退：换用下一个可用内核；没有下一个时返回 False。"""
        self._backend_index += 1
        if self._backend_index >= len(self._backend_chain):
            return False
        previous = self._backend_key
        self._backend_switch_count += 1
        self.dlg_activate_backend(self._backend_chain[self._backend_index])
        self._main_window.wnd_append_log(
            f"播放内核「{m3ule_player_backend_label(previous)}」未能出画，"
            f"自动换用「{m3ule_player_backend_label(self._backend_key)}」…")
        return True

    def dlg_remaining_backends(self) -> list:
        return self._backend_chain[self._backend_index + 1:]

    @Slot(int)
    def dlg_on_backend_combo_changed(self, index: int) -> None:
        if index < 0 or index >= len(self._backend_combo_keys):
            return
        self.dlg_request_backend(self._backend_combo_keys[index])

    def dlg_request_backend(self, key: str, notify: bool = True) -> bool:
        """切换播放内核（执行与提示分离：notify=False 供自动化测试复用）。

        返回 True 表示已切换（并已重新开始播放）；False 表示内核不可用或未知，未做改动。
        """
        key = m3ule_player_backend_key(key)
        ok, reason = m3ule_player_backend_status(key)
        if not ok:
            if notify and not self.dlg_offer_backend_library(key, reason):
                self.dlg_setup_backend_chain()
                return False
            ok, reason = m3ule_player_backend_status(key)
            if not ok:
                self.dlg_setup_backend_chain()
                return False
        self.dlg_activate_backend(key, persist=True)
        self._backend_chain = m3ule_player_backend_chain(key)
        self._backend_index = 0
        self._main_window.wnd_append_log(
            f"播放内核已切换为：{m3ule_player_backend_label(self._backend_key)}")
        self.dlg_play_index(self._index)
        return True

    def dlg_show_backend_report(self) -> None:
        QMessageBox.information(self, "播放内核检查", m3ule_player_backend_report_text())

    def dlg_offer_backend_library(self, key: str, reason: str) -> bool:
        """内核不可用时，就地让用户指定它的库文件（返回 True 表示指定后已可用）。

        FFmpeg 内核由 PySide6 自带、不需要指定文件；VLC 只要 libvlc.dll，
        所以这里直接给「指定文件…」按钮，不必让用户去改环境变量或翻设置页。
        """
        if not m3ule_player_backend_library_key(key):
            QMessageBox.warning(
                self, "内核不可用",
                f"{m3ule_player_backend_label(key)} 不可用：\n\n{reason}\n\n"
                + m3ule_player_backend_library_hint(key))
            return False
        box = QMessageBox(self)
        box.setWindowTitle("内核不可用")
        box.setIcon(QMessageBox.Warning)
        box.setText(f"{m3ule_player_backend_label(key)} 不可用：\n\n{reason}")
        box.setInformativeText(m3ule_player_backend_library_hint(key))
        pick = box.addButton("指定库文件…", QMessageBox.AcceptRole)
        box.addButton("知道了", QMessageBox.RejectRole)
        box.exec()
        if box.clickedButton() is not pick:
            return False
        names = m3ule_player_backend_library_names(key)
        path, _ = QFileDialog.getOpenFileName(
            self, f"选择 {m3ule_player_backend_label(key)} 的库文件",
            m3ule_get_program_dir(), "库文件 (%s);;所有文件 (*)" % " ".join(names))
        if not path:
            return False
        usable = m3ule_player_backend_set_library(key, path)
        self._main_window.wnd_append_log(
            f"{m3ule_player_backend_label(key)} 的库文件已记录：{path}（可用：{usable}）")
        if not usable:
            QMessageBox.warning(
                self, "仍然不可用",
                m3ule_player_backend_status(key)[1] + "\n\n" + m3ule_player_backend_library_hint(key))
            return False
        self.dlg_fill_backend_combo()
        return True

    def dlg_backend_status_text(self) -> str:
        if self._backend_widget is not None and hasattr(self._backend_widget, "bkd_status"):
            return self._backend_widget.bkd_status()
        return "未启动"

    def dlg_backend_progress(self) -> tuple:
        """当前内核的进度 (已解码帧数, 播放位置毫秒)，用于判断内核是否真的出画。"""
        if self._backend_widget is not None and hasattr(self._backend_widget, "bkd_progress"):
            return self._backend_widget.bkd_progress()
        return 0, 0

    # -- 播放控制 -----------------------------------------------------------
    def dlg_start_stall_watchdog(self) -> None:
        if self._stall_timer is None:
            self._stall_timer = QTimer(self)
            self._stall_timer.setInterval(3500)
            self._stall_timer.timeout.connect(self.dlg_on_stall_tick)
        self._stall_retries = 0
        self._stall_timer.start()

    def dlg_on_stall_tick(self) -> None:
        """看护：若干次轮询都没有画面就换内核（两个内核都试完才提示外部方案）。"""
        if not self._last_url:
            self.dlg_stop_watchdog()
            return
        frames, _position = self.dlg_backend_progress()
        if frames:
            self.dlg_stop_watchdog()
            return
        self._stall_retries += 1
        if self._stall_retries < 3:
            return
        widget = self._backend_widget
        detail = widget.bkd_error() if (widget is not None and hasattr(widget, "bkd_error")) else ""
        self.dlg_on_backend_gave_up(
            f"{m3ule_player_backend_label(self._backend_key)}内核未出画面"
            + (f"（{detail}）" if detail else ""))

    def dlg_on_backend_gave_up(self, reason: str) -> None:
        """当前内核判定失败：先自动换另一个内核，全部试完才提示外部方案。"""
        self.dlg_stop_watchdog()
        if self.dlg_advance_backend():
            self.dlg_play_index(self._index)
            return
        self._main_window.wnd_append_log(
            f"{reason}：可改用“在系统浏览器打开”或“用播放器打开”(VLC)，"
            "也可在上方换用另一个播放内核。")
        tried = "、".join(m3ule_player_backend_label(key) for key in self._backend_chain)
        self._lbl_status.setText(
            self._lbl_status.text() +
            f"<br><span style='color:#c5221f'>提示：{html.escape(reason)}。"
            f"已尝试内核：{html.escape(tried)}。"
            "可点上方<b>「内核检查」</b>看各内核是否可用（未安装的内核会给出安装指引），"
            "或用<b>「在系统浏览器打开」</b>/<b>「用播放器打开」</b>。</span>")

    def dlg_silence_other_backends(self, key: str) -> None:
        """开始播放前把「不是本次要用的内核」全部停掉：同一个弹窗只允许一路在播。"""
        for widget in self.dlg_backend_widgets():
            if getattr(widget, "M3ULE_BACKEND_KEY", "") == key:
                continue
            action = getattr(widget, "bkd_stop", None)
            if action is None:
                continue
            try:
                action()
            except Exception:  # noqa: BLE001
                pass

    def dlg_play_index(self, index: int) -> None:
        if not self._entries:
            self._lbl_status.setText("没有可播放的链接。")
            return
        self._index = max(0, min(int(index), len(self._entries) - 1))
        self.dlg_silence_other_backends(self._backend_key)
        self._combo_entries.blockSignals(True)
        self._combo_entries.setCurrentIndex(self._index)
        self._combo_entries.blockSignals(False)
        self.dlg_refresh_nav_state()
        entry = self._entries[self._index]
        url = (entry.url or "").strip()
        backend_label = m3ule_player_backend_label(self._backend_key)
        state = entry.test_state or "未测试"
        detail = entry.test_detail or ""
        self._lbl_status.setText(
            f"<b>{html.escape(entry.entry_effective_name() or '未命名')}</b> · 测试状态：{state}"
            f"{(' · ' + html.escape(detail)) if detail else ''}"
            f" · 播放内核：{html.escape(backend_label)}<br>"
            f"<span style='color:#5f6368'>{html.escape(m3ule_shorten_url_text(url))}</span>")
        self._lbl_status.setToolTip(url)
        self.setWindowTitle(
            f"弹窗播放 — {entry.entry_effective_name() or '未命名'}"
            f"（内核：{backend_label}）")
        # 两个内核都直接拉流（使用 FFmpeg 解码，避免二次封装影响解析）
        self._lbl_relay.setText("播放地址：直连（无需本机中转）")
        self._last_url = url
        widget = self.dlg_ensure_backend_widget(self._backend_key)
        started = bool(widget is not None and widget.bkd_start(url, entry.entry_effective_name()))
        if not started:
            reason = ""
            if widget is not None and hasattr(widget, "bkd_error"):
                reason = widget.bkd_error()
            self._main_window.wnd_append_log(
                f"播放内核「{backend_label}」启动失败：{reason or '未知原因'}")
            if self.dlg_advance_backend():
                self.dlg_play_index(self._index)
                return
            self._lbl_status.setText(
                self._lbl_status.text() +
                f"<br><span style='color:#c5221f'>无法用「{html.escape(backend_label)}」播放："
                f"{html.escape(reason or '未知原因')}。可点「内核检查」查看可用内核，"
                "或改用“在系统浏览器打开”/“用播放器打开”。</span>")
            return
        self._main_window.wnd_append_log(
            f"播放（{backend_label}）：{entry.entry_effective_name()} ← {url}")
        self.dlg_start_stall_watchdog()

    def dlg_step_entry(self, offset: int) -> None:
        if not self._entries:
            return
        target = (self._index + offset) % len(self._entries)
        self.dlg_play_index(target)

    @Slot(int)
    def dlg_on_combo_changed(self, index: int) -> None:
        if index != self._index:
            self.dlg_play_index(index)

    def dlg_refresh_nav_state(self) -> None:
        total = len(self._entries)
        self._lbl_index.setText(f"{self._index + 1} / {total}" if total else "0 / 0")
        self._btn_prev.setEnabled(total > 1)
        self._btn_next.setEnabled(total > 1)
        self._btn_prev.setToolTip(
            f"切换到上一个频道（共 {total} 个，循环）" if total > 1
            else "只有一个频道，无法切换（打开弹窗时可带上整个文件/筛选结果）")

    def dlg_fill_entries_combo(self, entries: list, index: int = 0) -> None:
        """填充频道下拉：显示名自动适应宽度，完整名称放在每项的悬停提示里。"""
        self._combo_entries.blockSignals(True)
        self._combo_entries.clear()
        for entry in (entries or []):
            name = entry.entry_effective_name() or "(未命名)"
            self._combo_entries.addItem(name)
            self._combo_entries.setItemData(self._combo_entries.count() - 1, name,
                                            Qt.ToolTipRole)
        if entries:
            position = max(0, min(int(index), len(entries) - 1))
            self._combo_entries.setCurrentIndex(position)
        self._combo_entries.blockSignals(False)
        self._btn_next.setToolTip(
            f"切换到下一个频道（共 {len(entries or [])} 个，循环）" if len(entries or []) > 1
            else "只有一个频道，无法切换（打开弹窗时可带上整个文件/筛选结果）")

    def dlg_toolbar_row_count(self, width: int = 0) -> int:
        """工具栏当前（或指定宽度下）排了几行——用于自检「宽窗口不要分太多行」。"""
        return self._toolbar_flow.m3ule_row_count(width)

    def dlg_current_entry(self):
        if not self._entries:
            return None
        return self._entries[self._index]

    def dlg_reload_page(self) -> None:
        entry = self.dlg_current_entry()
        if entry is None:
            return
        self._main_window.wnd_append_log(
            f"播放（{m3ule_player_backend_label(self._backend_key)}）：重新加载")
        self.dlg_play_index(self._index)

    def dlg_stop_playback(self, silent: bool = False) -> None:
        self.dlg_stop_all_backends()
        if not silent:
            self._main_window.wnd_append_log(
                f"播放已停止（{m3ule_player_backend_label(self._backend_key)}）。")

    def dlg_stop_all_backends(self) -> None:
        """停止所有内核的播放：栈里全部内核控件（换内核/换频道留下的控件也会继续在后台播放）。"""
        for widget in self.dlg_backend_widgets():
            action = getattr(widget, "bkd_stop", None)
            if action is None:
                continue
            try:
                action()
            except Exception:  # noqa: BLE001
                pass

    def dlg_on_autoplay_toggled(self, checked: bool) -> None:
        self._main_window.wnd_config_manager().cfg_set("player/html5_autoplay", bool(checked))

    def dlg_build_diagnostics_lines(self) -> list:
        """汇总播放环境信息（可被测试直接检查，不弹窗）。"""
        relay = self._main_window.wnd_relay_server()
        recent = relay.relay_recent_requests(8)
        lines = [
            f"播放内核：{m3ule_player_backend_label(self._backend_key)}"
            f"（本次尝试顺序：{' → '.join(m3ule_player_backend_label(k) for k in self._backend_chain) or '无'}）",
            f"配置项 player/backend：{self._main_window.wnd_config_manager().cfg_get('player/backend')}",
            f"本次内核状态：{self.dlg_backend_status_text()}",
            f"本次画面进度：{self.dlg_backend_progress()[0]}（已解码帧数）",
        ]
        for _key, label, ok, reason in m3ule_player_backend_report():
            lines.append(f"· {label}：{'可用' if ok else '不可用'} — {reason}")
        lines.extend([
            f"本地 hls.js（系统浏览器播放页用）："
            f"{relay.relay_local_hlsjs_path() or '未找到（将回退到 CDN，需要联网）'}",
            f"本机中转（系统浏览器播放页用）："
            f"{relay.relay_base_url() if relay.relay_is_running() else '未启动'}",
            "最近中转记录：" + ("；".join(recent) if recent else "(无)"),
        ])
        return lines

    def dlg_show_playback_diagnostics(self) -> None:
        """展示播放环境信息，便于用户/维护者定位“看不到画面”的原因。"""
        self._diag_shown = False
        self._diag_base = self.dlg_build_diagnostics_lines()
        QTimer.singleShot(300, self.dlg_show_diagnostics_box)

    def dlg_show_diagnostics_box(self) -> None:
        if getattr(self, "_diag_shown", False):
            return
        self._diag_shown = True
        lines = list(getattr(self, "_diag_base", []))
        lines.extend(self.dlg_build_diagnostics_advice())
        QMessageBox.information(self, "播放诊断", "\n".join(lines))

    @staticmethod
    def dlg_build_diagnostics_advice() -> list:
        """排错建议（独立成方法，便于自动化测试直接检查文案）。"""
        return [
            "",
            "排查建议：",
            "0) 先看第一行「播放内核」：两个内核（FFmpeg / VLC）都基于 FFmpeg 直连拉流，",
            "   看不到画面时可以点「内核检查」看哪个内核可用，直接在上方下拉里换内核（立即生效）。",
            "1) FFmpeg 内核显示“不可用”时：源码运行请执行 pip install PySide6；",
            "   编译版请确认打包时带上了 Qt 的 multimedia 插件（见《软件升级迭代记录.md》的编译说明）——",
            "   缺少 ffmpegmediaplugin.dll 时内核会安静地不出画（没有报错）。",
            "2) VLC 内核显示“不可用”时：装好 VLC（提供 libvlc.dll）并 pip install python-vlc，",
            "   或用上方「指定库文件…」直接指到 libvlc.dll。",
            "3) 两个内核都不行时：用“在系统浏览器打开”（Chrome/Edge 解码支持最完整，页面经本机中转），",
            "   或用“用播放器打开”（系统里已装的 VLC / mpv）。",
            "4) 若提示 hls.js 加载失败，请确认 assets\\hls.min.js 存在（或允许回退 CDN 联网）。",
        ]

    # -- 外部打开 -----------------------------------------------------------
    def dlg_open_external_player(self) -> None:
        entry = self.dlg_current_entry()
        if entry is None:
            return
        self._main_window.wnd_open_url_with_player(entry.url or "")

    def dlg_open_system_browser(self) -> None:
        if not self._last_url:
            entry = self.dlg_current_entry()
            if entry is None:
                return
            relay = self._main_window.wnd_relay_server()
            if not relay.relay_start():
                QMessageBox.warning(self, "提示", "无法启动本机播放中转服务。")
                return
            self._last_url = relay.relay_player_url(
                (entry.url or "").strip(), entry.entry_effective_name())
        QDesktopServices.openUrl(QUrl(self._last_url))
        self._main_window.wnd_append_log("已在系统浏览器打开播放页（需保持本程序运行）。")

    def dlg_copy_current_url(self) -> None:
        entry = self.dlg_current_entry()
        if entry is None:
            return
        QApplication.clipboard().setText(entry.url or "")
        self._main_window.wnd_append_log("已复制当前频道链接。")

    def dlg_save_player_html(self) -> None:
        entry = self.dlg_current_entry()
        if entry is None:
            return
        relay = self._main_window.wnd_relay_server()
        if not relay.relay_start():
            QMessageBox.warning(self, "提示", "无法启动本机播放中转服务。")
            return
        config = self._main_window.wnd_config_manager()
        default_dir = config.cfg_get("io/last_save_dir")
        safe_name = re.sub(r'[\\/:*?"<>|]', "_", entry.entry_effective_name() or "player")[:40]
        path, _ = QFileDialog.getSaveFileName(
            self, "另存播放页", os.path.join(default_dir, f"{safe_name}.html"),
            "HTML 文件 (*.html)")
        if not path:
            return
        page = relay.relay_build_player_html(
            (entry.url or "").strip(), entry.entry_effective_name(),
            self._chk_autoplay.isChecked())
        try:
            with open(path, "w", encoding="utf-8") as handle:
                handle.write(page)
        except OSError as exc:
            QMessageBox.warning(self, "保存失败", str(exc))
            return
        config.cfg_set("io/last_save_dir", os.path.dirname(path))
        self._main_window.wnd_append_log(f"播放页已保存：{path}")
        QMessageBox.information(
            self, "完成",
            f"已保存到：\n{path}\n\n注意：播放地址经由本机中转，"
            "使用该页面时请保持本程序运行。")

    # -- 生命周期 -----------------------------------------------------------
    def showEvent(self, event) -> None:
        super().showEvent(event)
        if self._backend_key not in M3ULE_PLAYER_BACKEND_CHAIN:
            self.dlg_setup_backend_chain()

    def dlg_stop_watchdog(self) -> None:
        if self._stall_timer is not None:
            self._stall_timer.stop()

    def dlg_restore_geometry(self) -> None:
        config = self._main_window.wnd_config_manager()
        if not config.cfg_get("ui/geometry/html5_player_compact", False):
            # v1.6.0 起工具栏改成 3 行（原来一排按钮把窗口顶得很宽），
            # 旧的「被顶宽」尺寸不再适用：首次运行时重置为新的紧凑默认尺寸。
            config.cfg_set("ui/geometry/html5_player_compact", True)
            return
        geometry = config.cfg_load_geometry(self.M3ULE_HTML5_GEOMETRY_KEY)
        if not geometry.isEmpty():
            self.restoreGeometry(geometry)

    def dlg_save_geometry(self) -> None:
        self._main_window.wnd_config_manager().cfg_save_geometry(
            self.M3ULE_HTML5_GEOMETRY_KEY, self.saveGeometry())

    def closeEvent(self, event) -> None:
        self.dlg_stop_watchdog()
        if self._retired_timer is not None:
            self._retired_timer.stop()
        self.dlg_save_geometry()
        # 关闭时把所有内核都停掉并释放库资源：只处理「当前」内核会漏掉换内核时
        # 留下的控件，那些控件会在后台继续播放（表现为「关了还在响/关不掉」）。
        self.dlg_stop_all_backends()
        self.dlg_release_backends()
        # 等后台销毁完再让窗口消失：避免在 libvlc 还在用宿主窗口时把窗口销毁掉。
        self.dlg_wait_backend_teardown(1.5)
        self.dlg_sweep_retired_widgets()
        event.accept()


# ----------------------------------------------------------------------------
# 对话框：使用说明
# ----------------------------------------------------------------------------

class M3ULiveEditorHelpDialog(QDialog):
    """显示使用说明（Markdown 转简易 HTML）。"""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("使用说明")
        self.resize(820, 620)
        root = QVBoxLayout(self)
        root.setContentsMargins(8, 8, 8, 8)
        browser = QTextEdit()
        browser.setReadOnly(True)
        browser.setHtml(M3ULE_HELP_HTML)
        root.addWidget(browser)
        buttons = QDialogButtonBox()
        buttons.addButton("关闭", QDialogButtonBox.RejectRole).clicked.connect(self.accept)
        root.addWidget(buttons)


class M3ULiveEditorColumnChooserDialog(QDialog):
    """自定义某张表显示哪些列（勾选显示 + 调整顺序）。"""

    def __init__(self, columns: list, visible_keys, order_keys, table_title: str,
                 parent=None):
        super().__init__(parent)
        self.setWindowTitle(f"自定义「{table_title}」显示的列")
        self.resize(480, 540)
        self._column_by_key = {column["key"]: column for column in columns}
        root = QVBoxLayout(self)
        root.setContentsMargins(8, 8, 8, 8)
        hint = QLabel(
            "勾选要显示的列，用「上移 / 下移」调整顺序。<br>"
            "设置会自动保存，下次启动继续生效；「状态 / 对比上次」这类列藏起来后依然在后台计算。")
        hint.setWordWrap(True)
        root.addWidget(hint)

        tools = QHBoxLayout()
        button_all = QPushButton("全选")
        button_all.clicked.connect(lambda: self.dlg_set_all_checked(True))
        tools.addWidget(button_all)
        button_none = QPushButton("全不选")
        button_none.clicked.connect(lambda: self.dlg_set_all_checked(False))
        tools.addWidget(button_none)
        button_default = QPushButton("恢复默认（全显示）")
        button_default.clicked.connect(self.dlg_restore_default)
        tools.addWidget(button_default)
        tools.addStretch(1)
        root.addLayout(tools)

        self._list = QListWidget()
        visible = set(visible_keys or [])
        for key in self.dlg_ordered_keys(order_keys, columns):
            column = self._column_by_key.get(key)
            if column is None:
                continue
            item = QListWidgetItem(f"{column['title']}　（{key}）")
            item.setData(Qt.UserRole, key)
            item.setFlags(item.flags() | Qt.ItemIsUserCheckable)
            item.setCheckState(Qt.Checked if key in visible else Qt.Unchecked)
            self._list.addItem(item)
        self._list.setCurrentRow(0)
        root.addWidget(self._list, 1)

        move_row = QHBoxLayout()
        button_up = QPushButton("上移")
        button_up.clicked.connect(lambda: self.dlg_move_current(-1))
        move_row.addWidget(button_up)
        button_down = QPushButton("下移")
        button_down.clicked.connect(lambda: self.dlg_move_current(1))
        move_row.addWidget(button_down)
        move_row.addStretch(1)
        move_row.addWidget(QLabel("提示：也可以直接拖动表头改变列顺序"))
        root.addLayout(move_row)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.button(QDialogButtonBox.Ok).setText("确定")
        buttons.button(QDialogButtonBox.Cancel).setText("取消")
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        root.addWidget(buttons)

    @staticmethod
    def dlg_ordered_keys(order_keys, columns) -> list:
        """按存储顺序排列，源码里新增的列自动补到末尾（老设置不会丢新列）。"""
        known = [column["key"] for column in columns]
        ordered = [key for key in (order_keys or []) if key in known]
        for key in known:
            if key not in ordered:
                ordered.append(key)
        return ordered

    def dlg_set_all_checked(self, checked: bool) -> None:
        state = Qt.Checked if checked else Qt.Unchecked
        for row in range(self._list.count()):
            self._list.item(row).setCheckState(state)

    def dlg_restore_default(self) -> None:
        self.dlg_set_all_checked(True)

    def dlg_move_current(self, step: int) -> None:
        row = self._list.currentRow()
        target = row + step
        if row < 0 or not (0 <= target < self._list.count()):
            return
        item = self._list.takeItem(row)
        self._list.insertItem(target, item)
        self._list.setCurrentRow(target)

    def dlg_order_keys(self) -> list:
        return [self._list.item(row).data(Qt.UserRole)
                for row in range(self._list.count())]

    def dlg_visible_keys(self) -> list:
        visible = []
        for row in range(self._list.count()):
            item = self._list.item(row)
            if item.checkState() == Qt.Checked:
                visible.append(item.data(Qt.UserRole))
        return visible

    def dlg_layout(self) -> dict:
        return {"order": self.dlg_order_keys(), "visible": self.dlg_visible_keys()}


M3ULE_HELP_HTML = """
<h2>M3U 直播源编辑管理系统 · 使用说明</h2>
<h3>一、基本流程</h3>
<ol>
<li><b>打开</b>一个 .m3u / .m3u8 直播源文件（文件 → 打开，或拖拽/快捷键 Ctrl+O）。</li>
<li>在<b>文件编辑</b>页查看、搜索、编辑所有频道；双击单元格即可修改。</li>
<li>在<b>链接测试</b>页批量测试链接是否可播放，进度条实时显示，结果写回列表。</li>
<li>在<b>ID扫描</b>页对某一编号区间做全网探测，找出“哪个 ID 是通的、是否还有节目”。</li>
<li>在<b>对比分析</b>页比较新旧两个文件，快速看出电视台重新排序后哪个频道换了编号。</li>
</ol>
<h3>二、字段说明</h3>
<ul>
<li><b>状态</b>：🟢成功（播放列表有效且有节目）、🟡部分可用（播放列表有效但分片无效）、
🔴失败、🟠超时、⚫错误、⚪未测试。</li>
<li><b>对比上次</b>：每次开始测试前会把当前结果存成「上一次」，测完就显示这次相对上次的变化 ——
<span style="color:#137333"><b>★新增可用</b></span>（以前不行、现在能播）、
<span style="color:#c5221f"><b>★新失效</b></span>（以前能播、现在播不了）、
仍然可用、仍然不可用、首次测试（以前没记录）、本次未测。测试完成时状态栏与日志会给出
<b>对比上次：★新增可用 N · ★新失效 M · …</b> 一句话结论，不用逐行数就知道这次比上次多了还是少了台；
鼠标悬停可看到「上次状态（含时间）→ 本次状态（含时间）」。</li>
<li><b>深度测试</b>：除校验播放列表外，会尝试下载首个分片，用来判断“是否有节目”。</li>
<li><b>检测时间</b>：该条结果是什么时候测出来的；状态列出现「（缓存）」表示这条结果来自
检测缓存（之前测过、本次没有重新联网检测），鼠标悬停可看到具体时间与“多久以前”。</li>
<li><b>码率(kbps)</b>：从清单里 <code>#EXTINF</code> 的分片字节数实测换算，比主清单声明的
<code>BANDWIDTH</code> 更接近真实占用；悬停可看到该源提供的码率档位数与是否加密。</li>
<li><b>延迟(s)</b>：清单最后一段的起播时刻距现在多少秒（来自
<code>#EXT-X-PROGRAM-DATE-TIME</code>）。<b>这是判断“是否真的在直播”的关键</b>：
数值正常（几十秒内）说明内容在向前推进；数值很大说明该台可能已卡住或在循环播放旧内容。</li>
<li><b>流ID</b>：从分片地址里解析出的<b>频道内部流ID</b>。同一个编号前后两次测出的流ID不同，
就说明该编号背后的频道被换过了 —— 这是判断“电视台重新排序”的可靠依据。</li>
</ul>
<h3>三、快捷操作</h3>
<ul>
<li>Ctrl+O 打开　Ctrl+S 保存　Ctrl+Shift+S 另存为　Ctrl+N 新建</li>
<li>Ctrl+F 聚焦搜索框　Ctrl+D 删除选中　Ctrl+A 全选　Ctrl+G 批量修改分组　Ctrl+Shift+L 台标自动匹配</li>
<li>Ctrl+T 测试全部　Ctrl+Shift+T 测试选中　Esc 停止测试</li>
<li><b>自定义显示哪些列</b>：菜单「视图 → 文件编辑列…／链接测试列…」打开列选择框，
勾选要显示的列、用「上移/下移」调整顺序；也可以直接<b>右键表头</b>快速勾选单列、
一键「自定义列…／恢复默认列／适应内容宽度」。两张表的列设置<b>各自记住</b>，
下次启动继续生效；源里新增的列会自动补上，不会因为旧设置而消失。</li>
<li>双击“链接”列任意行 → 用系统默认播放器/VLC 打开该链接</li>
<li>选中频道后按 <b>Ctrl+Alt+Enter</b>（或右键菜单「用弹窗播放」）→ 在弹窗播放器中播放，
可「上一个/下一个」连续查看多个频道，用于快速确认某个编号现在是什么台</li>
</ul>
<h3>三点五、弹窗播放（v1.1.0 新增；v1.6.0 扩展为多内核；v1.8.4 只保留 FFmpeg / VLC）</h3>
<ul>
<li>选中频道后按 <b>Ctrl+Alt+Enter</b>（菜单「工具」/右键菜单「用弹窗播放」/详情面板「弹窗播放」）
即可在弹出的播放器中观看，可用「上一个 / 下一个」连续比对多个频道，
用于快速确认某个编号现在是什么台。</li>
<li><b>内嵌播放（默认）</b>：用 <b>FFmpeg</b>（Qt 多媒体）或 <b>VLC</b>（libvlc）内核直接拉流，
不依赖浏览器；当前内核打不开画面时会自动换用另一个可用内核。</li>
<li><b>系统浏览器播放</b>：把「播放方式」改成「系统浏览器」后，播放页交给 Chrome/Edge，
地址经本机 <code>127.0.0.1</code> <b>回环中转</b>（自动解决跨域（CORS）与混合内容限制，
并改写 m3u8 内的分片 / 子清单 / 密钥 / 初始化段地址），内置 <b>hls.js</b>
（优先使用程序目录 <code>assets\hls.min.js</code>，缺失时自动回退 CDN）播放 HLS 直播。</li>
<li>两个内嵌内核都失败时才提示改用「在系统浏览器打开」或「用播放器打开」，
并可点「诊断」查看内核状态、画面进度与中转请求情况。</li>
<li>「另存播放页」可把系统浏览器播放页导出为 HTML 文件；ID 扫描页的「弹窗播放所选」
按钮可直接播放扫描到的编号。</li>
</ul>
<h3>三点七、检测结果缓存（v1.2.0 新增）</h3>
<ul>
<li><b>测过就不会白测</b>：每次测试的结果都会按链接保存到本地数据库
（<code>data\\m3u_live_editor.db</code> 的 <code>probe_cache</code> 表），
<b>关闭程序、下次打开同一个文件时会自动把上次的结果填回列表</b>，状态列标注「（缓存）」，
“检测时间”列显示当时的检测时间和“多久以前”，不需要再全部重测。</li>
<li><b>只测该测的</b>：勾选测试页的「跳过有效缓存」后，已经检测过、且结果还在
“检测缓存有效期”（默认 72 小时）内的链接会被直接跳过，只测没测过的、过期的和失败的，
速度更快。日志会显示跳过了多少条。</li>
<li><b>需要重测时</b>：把“范围”选为「忽略缓存全部重测」（或菜单「测试 → 忽略缓存重测全部」），
或取消勾选「跳过有效缓存」，即可强制全部重新联网检测。</li>
<li><b>范围选项</b>：新增「仅缓存过期项」，只测缓存已过期或从未测过的链接。</li>
<li><b>缓存的维护</b>：测试页与「设置 → 检测缓存」都可「应用检测缓存」「清空检测缓存」；
右键菜单「清除所选链接的缓存」可只删掉个别条目的缓存（例如该台已停播，想彻底重测）。</li>
<li><b>不会张冠李戴</b>：修改某条的链接后，该条旧的检测结果会自动清除，
不会把旧链接的结果留在新链接上；缓存的键是完整链接（含参数），
所以编号不同/参数不同的链接各自独立。</li>
<li>「清空测试结果」只清空当前显示的状态，<b>不会</b>删除检测缓存。</li>
</ul>
<h3>三点八、流元信息：码率 / 延迟 / 流ID（v1.3.0 新增）</h3>
<p>深度测试除判断“是否有节目”外，还会从 m3u8 清单里再解出三项关键信息，直接显示在列表里：</p>
<ul>
<li><b>码率(kbps)</b>：用 <code>#EXTINF</code> 第二个字段（分片字节数）÷ 分片时长换算，
所以是<b>实测值</b>；悬停可看到主清单提供了几个码率档位、是否加密
（<code>#EXT-X-KEY</code>）。</li>
<li><b>延迟(s)</b>：清单里最后一段的 <code>#EXT-X-PROGRAM-DATE-TIME</code> 距现在的秒数。
<b>这项用来区分“通”和“真的在直播”</b>——链接 200 且能下载分片，但延迟数值一直变大，
说明这个台其实已经卡住或在循环播放旧的片段。一般正常值是十几到几十秒。</li>
<li><b>流ID</b>：分片地址里带的<b>服务端流实例编号</b>（该编号背后是哪路码流）。
同一编号在短时间内稳定（实测 90 秒内 10 个编号全不变），
但源端重启/重连时可能变化 —— <b>所以它不是绝对的“频道指纹”</b>。
正确的用法是：把两份文件的流ID 互相比对 ——
变化很小多半只是源端重启；<b>变化很大、或与另一个编号的旧值相同，
就说明该编号背后的频道很可能被换过</b>（建议再播放确认）。
测出的流ID 会随检测缓存一起保存，下次打开仍能和上次对比。</li>
</ul>
<p><b>注意</b>：这些信息都来自清单本身，清单里<b>没有</b>频道名称、节目单（EPG）、台标或频道总表
—— 直播流不携带“这个台叫什么”，同一个编号现在是什么台，仍需播放后人工确认，
再填到「ID 扫描」页的“当前频道”列里保存下来。</p>
<h3>三点九、编号映射表（v1.4.0 新增）</h3>
<p>很多播放列表把编号直接写在标题里，例如 <code>[000] 广东民生</code>。
「工具 → 编号映射表…」（快捷键 <b>Ctrl+M</b>）会把这类编号解析出来，
和实测结果合并成一张表：<b>编号 · 频道名 · 来源 · 状态 · 延迟(s) · 流ID · 链接</b>。</p>
<ul>
<li><b>识别两种写法</b>：标题带编号（<code>[000] 广东民生</code>、<code>000 广东民生</code>），
或链接带编号参数（<code>...se_idx=000...</code>、<code>...idx=000...</code>）。</li>
<li><b>★ 待确认的编号不会被丢掉</b>：如果标题里<b>只有编号没有名称</b>（例如只写 <code>[048]</code>），
该编号依然会列出并标记为「（待确认）」—— 一眼就能看出<b>还有哪些编号没认出是什么台</b>。
汇总栏会分别统计「已命名 / 待确认」。</li>
<li><b>与实测叠加</b>：状态列直接显示该编号测得的结果，配合延迟(s) 就能同时看出
「通不通」和「是不是真的在播」。</li>
<li><b>可存可导</b>：「保存到数据库」把映射写进本地库（下次可直接读回，且优先级高于标题）；
「导出 CSV…」输出整张表；「导入其它 m3u…」可把另一个文件（例如旧版本）的映射并进来比对。</li>
<li><b>ID 扫描页联动</b>：扫描页新增「从文件标题生成编号映射」按钮，一键把这些编号填入
「当前频道」列，省去逐条手输；标题里没有名称的编号会标成「待确认」等人工补齐。</li>
</ul>
<h3>三点九五、频道同步（v1.7.6 新增，v1.7.7 摘要可滚动，v1.8.0 增加整表替换与字段对齐）</h3>
<p>用途：<b>把已校对文件里确认的「频道名 → 编号」同步到另一个文件</b>
（例如把「广州珠江宽频的m3u8直播源 - 154」里确认好的频道，同步到 <code>xteve.m3u</code>）。</p>
<p>打开方式：菜单「<b>工具 → 频道同步…</b>」（快捷键 <b>Ctrl+Shift+M</b>）。</p>
<ul>
<li><b>① 校对来源</b>：选已校对好的文件（也可直接用「当前打开的文件」）；
也可以把来源切成「数据库编号映射」，用「编号映射表 / ID 扫描页」保存过的映射。</li>
<li><b>② 目标文件</b>：选要同步到的文件（例如 <code>xteve.m3u</code>）。</li>
<li><b>③ 同步方式一：只更新编号（默认）</b>——目标文件里<b>同名</b>频道换成校对来源里确认的编号，
只改链接里的那几位编号数字；<b>分组、台标、注释与空行一个都不动</b>；
目标里没有的频道按名字<b>追加到末尾</b>（分组留空，可稍后自行分组），地址用目标文件里最常见的模板拼。</li>
<li><b>③ 同步方式二：整表替换（更直接）</b>——<b>不管旧文件有哪些频道</b>，直接用来源的频道重建目标
文件的频道区：写入顺序就是来源文件里的顺序，<b>旧文件里不在新列表里的频道会被清除</b>；
同名频道<b>沿用原来的分组与台标</b>（台标跟着频道走，不因编号变化而错位），
可以勾选「<b>只同步有信号的频道</b>」（数据库里已确认无信号/无节目的跳过，还没测过的照写）。
文件头 <code>#EXTM3U …</code>、注释行与末尾行都会保留。</li>
<li><b>④ 字段对齐（两种方式都有）</b>：
<b>频道名称写入 tvg-name</b>；<b>标题也用校对名称</b>；
<b>channelID / 频道号(tvg-chno) / tvg-id 跟随编号</b>——即对应该链接里的
<code>Fsv_chan_hls_se_idx</code>（例如 <code>se_idx=031</code> →
<code>channelID="x-ID.31" tvg-chno="31" tvg-id="31"</code>，前缀留空时自动从目标文件识别，
也可手动指定）；<b>台标</b>始终跟着它属于的那个频道。</li>
<li><b>不会瞎改的情况（都会在预览里列出）</b>：
<b>冲突</b>（校对文件里同名对应多个编号，先自己确认）、
<b>无编号</b>（链接里没有编号参数）、
<b>未匹配</b>（只更新编号时，目标里找不到同名频道就保持原样，并提示校对文件里那个编号是什么/还没填名称）、
<b>跳过</b>（整表替换时：来源条目没有名称 / 没有编号 / 已确认无信号 / 编号重复，都会写明原因）。</li>
<li><b>安全的用法</b>：点「开始分析」只读文件、只出预览表（动作/名称/原编号/新编号/说明/地址）；
确认无误再点「<b>应用并保存</b>」（写前自动备份原文件），或点「<b>另存为副本…</b>」先导出一份对照。
选项（同步方式、名字匹配、是否新增、字段对齐、channelID 前缀等）<b>改完即时保存</b>，下次打开沿用。</li>
</ul>
<h3>三点十、编号双列对比（v1.5.0 新增）</h3>
<p>「对比分析」页现在有两个模式，顶部可切换：</p>
<ol>
<li><b>文件对比（按频道匹配键）</b> —— 原来的功能，按 <code>tvg-id → channelID → 名称</code>
匹配两个文件，看频道名 / 编号 / 链接有没有变。</li>
<li><b>编号双列对比（ID 增删 / 失效）</b> —— <b>新增</b>，按 <b>编号（ID）</b> 左右对齐两列，
专门回答「跟以前那份文件比，现在多了哪些台、哪些台失效了」。</li>
</ol>
<p><b>双列对比怎么用</b>：</p>
<ul>
<li><b>旧（以前）</b>与<b>新（现在）</b>两侧都支持四种来源：
<b>选择文件…</b>（以前的 m3u）、<b>当前文件</b>（含已实测状态）、
<b>ID 扫描结果</b>（适合你刚扫完 0–999 的情形）、<b>数据库映射</b>。<br>
两侧的选择会<b>自动记住</b>，下次启动程序时原样恢复，直接点「开始双列对比」即可，
不用每次重新挑文件。</li>
<li>某一侧是否「有信号」的判定顺序：先看该文件的<b>实测结果</b>，
没有实测就自动查<b>检测缓存</b>（同一个链接以前测过的结果），都没有才算「未测」。</li>
<li>表格四列：<b>编号 · 旧（以前）· 新（现在）· 变化</b>，每列直接显示
「图标 + 频道名 + 有信号/无信号/未测」。</li>
<li><b>变化类型</b>：<span style="color:#137333">新增可用</span>（以前不行现在行了）、
<span style="color:#c5221f">新失效</span>（以前能播现在播不了）、
仍然可用、仍然不可用、仅旧有、仅新有、未测。
「新增可用」与「新失效」会加粗 + 着色，一眼看到重点。</li>
<li>勾选<b>「只看有变化」</b>可隐藏「仍然可用 / 仍然不可用」的噪音；可<b>导出 CSV</b>。</li>
<li><b>信号过滤</b>（回答「大家都有信号的编号，有没有缺失」）：下拉框有六种视角 ——
<b>全部（不按信号过滤）</b>、
<b>只看两侧都有信号</b>（新旧都能播的编号）、
<b>只看旧侧有信号（查缺失）</b>（以前能播的编号现在还剩几个）、
<b>只看新侧有信号</b>、
<b>只看缺失项（旧有→现无）</b>、
<b>只看待确认（旧有→现未测）</b>。
选了「按信号过滤」之外的任一视角时会自动取消「只看有变化」，避免行被藏起来。</li>
<li><b>「★缺失」</b>的定义（保守，两步确认才下结论）：<b>旧侧有信号</b>，且
<b>新侧实测为无信号</b>，或<b>该编号在新列表里已不存在</b>。
缺失行会标红并加粗，汇总条同时给出
<b>旧侧有信号 N → 现在仍可用 M · ★缺失 K · 新增可用 G</b>，
不用逐行数就能知道少了几个台。</li>
<li><b>「❓待确认」</b>：旧侧有信号、新侧存在但<b>还没测过</b>。它<b>不算缺失</b>，
用橙色单独统计 —— 这样「没测」永远不会被误报成「失效」，
而「确实没了」的红色结论又不会漏。</li>
<li>筛选结果与汇总只统计<b>真正在用的编号</b>（旧侧未测的编号不算缺失），
所以「旧文件没实测过」时永远报「无缺失」而不是误报。</li>
<li><b>「旧侧用最早历史记录」</b>（默认勾选）：旧（以前）一侧优先取该链接在
「测试历史」里<b>最早</b>的一次实测结果。原因是检测缓存只保留每个链接的<b>最新</b>结果，
若新旧文件用的是同一批链接，两侧都会落到同一个最新结果，就永远看不出
「以前能播、现在不能」。取消勾选则旧侧也只看最新缓存。</li>
<li>汇总栏的<b>「旧侧状态来源」</b>会列出「最早历史记录 / 检测缓存（最新）/ 未测」各多少条
（旧侧没有该编号的不计），用来判断「无缺失」可信不可信 —— 若来源里「未测」占多数，
说明<b>只有一次检测记录、还没有历史可比</b>，需要隔一段时间再扫一次才会出现真正的缺失。</li>
<li>单元格鼠标悬停显示该格状态的<b>来源与时间</b>；导出的 CSV 含
「旧状态来源」「新状态来源」两列，便于事后核对。</li>
<li>「未测」是<b>刻意保守</b>的：只要有一侧没测过，就不下「新增/失效」的结论，
避免把「没测」误报成「失效」。</li>
</ul>
<h3>三点十一、看不到画面时的排查（v1.5.1 新增，v1.8.4 改为围绕两个内核）</h3>
<ul>
<li><b>先点播放器窗口上的「诊断」</b>：会列出两个内核各自的可用性与原因、本次画面进度
（已解码帧数）、以及系统浏览器播放页用的 hls.js / 中转状态。</li>
<li><b>第一步换内核</b>：顶部「内核」下拉里换另一个可用内核（立即生效，无需重启）。
两个内核都确认可用却都不出画时，用「在系统浏览器打开」（Chrome/Edge 解码支持最完整）
或「用播放器打开」（系统里已装的 VLC / mpv）。</li>
<li><b>FFmpeg 内核不可用 / 不出画</b>：源码运行 <code>pip install PySide6</code>；
<b>编译版</b>请确认打包参数里有 <code>--include-qt-plugins=multimedia</code>
（缺少 <code>ffmpegmediaplugin.dll</code> 时 Qt 多媒体<b>没有媒体后端</b>，
表现为「没有报错、也不出画」）。自检：<code>--selftest-player=&lt;m3u8 地址&gt;</code>。</li>
<li><b>VLC 内核不可用</b>：需要本机已安装 VLC（提供 <code>libvlc.dll</code>）并
<code>pip install python-vlc</code>；VLC 装在非默认目录时用「指定库文件…」指到
<code>libvlc.dll</code>，或用环境变量 <code>M3ULE_LIBVLC_DIR</code> 指定安装目录。</li>
<li>检测到<b>远程桌面会话</b>时不需要额外设置（内嵌内核不再依赖 GL 上下文），
若仍出不了画请换内核或用系统浏览器方式。</li>
</ul>
<h3>三点十二、弹窗播放内核：FFmpeg 与 VLC（v1.6.0 新增多内核，v1.8.4 收窄为两个）</h3>
<p>「用弹窗播放」的窗口顶部多了一个<b>「内核」下拉框</b>，
可以随时切换用哪种播放内核，<b>切换立即生效、无需重启程序</b>；
旁边的<b>「内核检查」</b>按钮会列出本机每个内核是否可用及原因（未安装的会给出安装指引）。</p>
<ul>
<li><b>FFmpeg（内嵌 Qt 多媒体）</b>：<b>默认内核</b>，<b>PySide6 自带、无需另外安装</b>，直接拉流，
直播流延迟低；<b>编译版请注意</b>：打包时必须带上 Qt 的 multimedia 插件
（<code>--include-qt-plugins=multimedia</code>，缺 <code>ffmpegmediaplugin.dll</code> 时会
「没有报错但不出画」）。</li>
<li><b>VLC（libvlc）</b>：兼容性最好。装好 VLC 后执行 <code>pip install python-vlc</code> 即可；
若 VLC 装在非默认目录，可在设置页点「浏览…」指定 <code>libvlc.dll</code>，
或用环境变量 <code>M3ULE_LIBVLC_DIR</code> 指定安装目录。</li>
<li><b>只保留这两个内核（v1.8.4）</b>：以前的「内嵌 HTML5（Qt WebEngine）」与「mpv（libmpv）」
已不再提供 —— 前者依赖 Chromium 的 GL / 解码能力（远程桌面、虚拟机、老显卡驱动下容易黑屏），
后者的 <code>libmpv-2.dll</code> 还要单独获取与修依赖。旧设置里如果存着这两个内核，
程序会自动迁移到 FFmpeg 并写回设置，不会出现「升级后什么都播不了」。</li>
<li><b>自动换内核</b>：播放时若判定当前内核<b>始终没出画面</b>，会自动换用另一个可用内核继续尝试，
两个都失败才提示改用「在系统浏览器打开」或「用播放器打开」。</li>
<li><b>播放地址</b>：两个内核都用原始地址直连拉流（FFmpeg 解析更稳，也不会被中转二次改写）；
只有「系统浏览器播放页」方式才经过本机中转（解决跨域 / 混合内容 / 统一 UA）。</li>
</ul>
<p>设置位置：<b>设置 → 弹窗播放 → 播放内核</b>（默认 FFmpeg；每台机器的选择会保存，
下次启动沿用；换到别的机器上若该内核不可用，程序会自动改用另一个可用内核并在日志里说明）。</p>
<p><b>编译后 ffmpeg 播放不了？</b>这是打包漏了 Qt 的多媒体插件导致的，与程序逻辑无关：
Nuitka 的 PySide6 插件默认只带 <code>mediaservice</code> 插件族（Qt5 的叫法），
而 Qt6 的媒体后端在 <code>multimedia</code> 插件族里。本项目的
<code>0_nuitka_pyside6_clang_auto.bat</code> 已加 <code>--include-qt-plugins=multimedia</code>，
PyInstaller 的 <code>M3U_Live_Editor.spec</code> 也已带上该插件与 FFmpeg 运行库；
自检命令：<code>python M3U_Live_Editor.py --selftest-player=&lt;m3u8 地址&gt;</code>
（编译后的 exe 同样支持，出画即打印帧数与播放位置，不出画会打印诊断）。</p>
<p><b>连着切换频道</b>：从表格打开弹窗时，会把<b>当前视图里的整个频道列表</b>一起带进去
（按你当前的筛选与排序），起始位置就是你选中的那一行 —— 于是
<b>「◀ 上一个 / 下一个 ▶」</b>与频道下拉可以直接一个接一个往下看，不用每次退回表格重新选行；
两个按钮是循环的（到底会回到第一个）。ID 扫描页的播放按钮同样会把整张结果表带进去。
<b>工具栏会自动换行</b>：窗口宽时两三行就放得下，窗口窄时自动多折几行，
频道下拉框的宽度跟着频道名长短自动调整（长名字最多占一个上限宽度，完整名称放在悬停提示里）。</p>
<h3>三点十三、批量修改分组（多选 / 整批）（v1.8.1 新增）</h3>
<ul>
<li><b>打开方式</b>：菜单「编辑 → 批量修改分组…」/ 工具栏按钮 / 表格右键菜单 / 快捷键 <b>Ctrl+G</b>。</li>
<li><b>第一步「要改哪些条目」</b>：
<ul>
<li><b>选中的条目</b> —— 在列表里按住 <b>Ctrl</b> 逐个点、或按住 <b>Shift</b> 选一段，可以一次选很多条；
一条都没选中时程序会自动改用下面那一项（按钮也会置灰）。</li>
<li><b>当前列表全部</b> —— 把当前表里<b>筛选后剩下的全部条目</b>一次改掉
（先把关键词 / 分组 / 状态筛好，再整批归入某个分组，最省事）。两个选项后面都直接写着条数。</li>
</ul></li>
<li><b>第二步「分组改成什么」</b>：
<ul>
<li><b>设为新的分组名称</b>：直接输入一个新名字（例如 <code>广东-高清</code>），选中/整批的条目全部归入它。</li>
<li><b>添加到已有分组</b>：下拉框里是<b>当前文件已有的分组</b>（不会写错名字），选一个即可。</li>
<li><b>清除分组（删除 group-title）</b>：把这些条目的分组字段直接删掉，回到「未分组」。</li>
</ul></li>
<li><b>先看再改</b>：点「预览」会列出「序号 / 频道名称 / 原分组 / 新分组」（最多 300 条），
并给出「命中 N 条，将修改 K 条，另有 M 条分组本来就是目标值（跳过）」的结论 ——
<b>分组已经等于目标值的条目不会被重复改写</b>，日志里也只记真正改动的条数。</li>
<li><b>更快的做法（右键菜单）</b>：右键表格 →「<b>加入已有分组（选中条目）</b>」，
子菜单里直接点一个已有分组名，选中的条目立刻归入该组；子菜单末尾还有
「清除分组（删除 group-title）」。这一条不需要打开对话框。</li>
<li><b>安全边界</b>：只改 <code>group-title</code> 一个属性（其它属性、链接、注释与空行一律不动，
<code>#EXTINF</code> 行按原有属性顺序重写这一项）；改动照常计入「未保存」状态，<b>不写盘</b>，
点「保存」才会落盘（保存前仍按设置自动备份）。</li>
</ul>
<h3>三点十四、台标自动匹配（按频道名补 tvg-logo）（v1.8.2 新增）</h3>
<ul>
<li><b>打开方式</b>：菜单「工具 → 台标自动匹配…」/ 表格右键菜单 / 快捷键 <b>Ctrl+Shift+L</b>。
在列表里选了条目再打开，默认<b>只处理选中的那些</b>；想改整份文件在对话框里切回「当前文件全部」。</li>
<li><b>它怎么找台标</b>：按<b>频道名称</b>匹配（标题 → tvg-name → channelID），四种来源可任意组合：
<ul>
<li><b>台标库 CSV / JSON（v1.8.3）</b>：程序自带一份整理好的网络台标库
（<code>data\台标库-网络汇总.csv</code>，从 fanmingming/live、CCSH/IPTV、iptv-pro、baihy99/iptv、
mytv-android/China-TV-HD-Logo、kk3432/china-station-caption、wanglindl/TVlogo、iptv-org 等公开库汇总，
约 9000 条「频道名 → 台标地址」）。第一次打开本对话框会自动把它加为来源；也可以点
「<b>导入网络台标库</b>」一次性存进数据库台标库，之后勾上「用已保存的台标库」即可给任何文件补台标。
自己整理的映射文件同样能用：「添加文件…」或按钮区「导入台标库 CSV」都支持
两列 <code>频道名,台标地址</code>（可带表头、第三列写来源）以及
<code>{"频道名": "台标地址"}</code> / <code>[{"name": …, "logo": …}]</code> 的 JSON。</li>
<li><b>参考 m3u（文件或网址）</b>：从另一个已经带台标的 m3u 里学「频道名 → 台标」——
你手头有整理好的文件时最省事（例如用 <code>xteve.m3u</code> 给只有名字的新文件补台标）；
点「内置推荐」还能加上 <code>iptv-org</code> 的中国频道列表（含台标，需联网）。</li>
<li><b>台标库</b>：每次匹配成功的「频道名 → 台标」都会自动存进数据库，<b>跨启动累积</b>，
下次打开别的文件直接命中，不用再读参考文件；可导入/导出 CSV（两列「频道名, 台标地址」即可），
也能直接「导入网络台标库」（约 9000 条公开台标，来源随程序放在 <code>data\</code> 目录）。</li>
<li><b>EPG(XMLTV)</b>：取每个频道的 <code>&lt;icon src="…"&gt;</code>，按 <code>&lt;display-name&gt;</code> 匹配；
勾上「用文件头部声明的 EPG」就会自动使用 m3u 头部 <code>x-tvg-url</code> / <code>url-tvg</code> 里的地址。</li>
<li><b>台标文件夹</b>：把图片文件名当成频道名（<code>CCTV1.png</code> → 频道 <code>CCTV1</code>）；
如果这些图片已经由服务器（例如 xteve）挂在网上，可在「台标文件夹」来源里带上网络前缀，
写出的就是 <code>http://主机:端口/目录/文件名</code>，否则写本机 <code>file:///…</code> 地址。</li>
</ul></li>
<li><b>名字怎么算「同名」</b>：先去掉标题里的编号（<code>[000]</code>）与空格/标点、忽略大小写；
再宽松一档：去掉「高清 / HD / 蓝光 / 1080p / 频道 / 卫视 / 综合」这类噪声
（<code>CCTV1 综合</code>、<code>CCTV-1</code>、<code>CCTV1高清</code> 都算同一个台）；
还找不到时可选「给出相似名建议」（只列出、<b>默认不勾选</b>，需你自己确认）。</li>
<li><b>先看再改</b>：点「开始匹配」后，预览表逐条列出「频道名称 / 状态 / 台标地址 / 来源」，
状态分 <b>精确匹配、去噪匹配、相似建议、已是同一台标、已有台标、未匹配、无名条目</b>；
每行最左边有勾选框，<b>只写勾选的行</b>（可「全选 / 全不选 / 只选可自动应用的」），
摘要一句话给出「可补台标 N 条…」。预览可导出 CSV 留档。</li>
<li><b>安全边界</b>：只改 <code>tvg-logo</code> 一个属性（其它属性、链接、注释与空行不动，
<code>#EXTINF</code> 按原有属性顺序重写这一项）；只标记「未保存」、<b>不写盘</b>，
点「保存」才落盘（保存前仍按设置自动备份）。默认「只补没有台标的条目」，
已有台标的一律跳过；关掉该开关才会覆盖同名频道的现有台标。</li>
<li><b>拿不到台标的情况</b>：条目本身<b>只有编号没有名称</b>（如 <code>[008]</code>）时无法按名字匹配，
预览里会明确标成「无名条目」——这也是补全名称的工作清单（可用「频道同步 / 编号映射表」把名字补上后再匹配）。</li>
</ul>
<h3>四、设置持久化</h3>
<p>所有设置（并发数、超时、深度测试、播放器路径、窗口布局、列宽、检测缓存开关与有效期、
最近目录等）都会 <b>实时自动保存</b>，下次启动自动加载。检测结果本身同样持久保存，
重启后会重新套用到同名链接。密钥类信息（API Key、数据库密码、代理）保存在
程序目录的 <code>.env</code> 文件中，不会写入源码。</p>
<p><b>记忆上次打开的文件</b>：程序会记住你上次打开（或另存为）的 m3u，下次启动
<b>自动加载</b>并回填检测缓存，不用每次重新选文件；命令行已指定文件时不受影响。
可在「设置 → 文件与备份」里关闭，并能看到当前记住的是哪个文件。
<b>对比分析</b>两侧选择的来源（旧 / 新：文件、当前文件、ID 扫描结果、数据库映射）
同样会被记住并在下次启动恢复。
<b>文件编辑 / 链接测试</b>两张表的<b>列设置</b>（显示哪些列、按什么顺序）也分别记住，
下次启动原样恢复。</p>
<h3>五、维护约定</h3>
<p>本程序为唯一主程序，所有更新直接修改 <code>M3U_Live_Editor.py</code>；每次改动都会同步更新
《软件升级迭代记录.md》与版本号，并把旧版本备份到 <code>version\\</code> 子目录。</p>
"""


# ----------------------------------------------------------------------------
# 后台线程：批量链接探测
# ----------------------------------------------------------------------------

class M3ULiveEditorProbeWorker(QThread):
    """在独立线程内用线程池并发探测一批链接并回传结果。"""

    sig_worker_results = Signal(object)     # list[dict] 一批结果
    sig_worker_progress = Signal(int, int)  # 已完成 / 总数
    sig_worker_log = Signal(str)
    sig_worker_finished = Signal(dict)

    def __init__(self, tasks: list, options: dict, parent=None):
        super().__init__(parent)
        self._tasks = list(tasks)
        self._options = dict(options)
        self._cancel_event = threading.Event()
        self._results: list = []

    def worker_request_cancel(self) -> None:
        self._cancel_event.set()

    def worker_is_cancelled(self) -> bool:
        return self._cancel_event.is_set()

    def worker_cancel_check(self) -> bool:
        return self._cancel_event.is_set()

    def worker_results(self) -> list:
        return list(self._results)

    def run(self) -> None:  # noqa: C901 - 线程主体，逻辑集中
        options = self._options
        workers = max(1, min(64, m3ule_safe_int(options.get("workers", 16), 16)))
        timeout = max(0.5, m3ule_safe_float(options.get("timeout", 8.0), 8.0))
        retries = max(0, min(5, m3ule_safe_int(options.get("retries", 1), 1)))
        deep = bool(options.get("deep", True))
        user_agent = str(options.get("user_agent", "") or M3ULE_DEFAULT_USER_AGENT)
        proxy = str(options.get("proxy", "") or "")
        ignore_ssl = bool(options.get("ignore_ssl", True))

        total = len(self._tasks)
        started = time.time()
        self.sig_worker_log.emit(
            f"开始测试 {total} 条链接（并发 {workers}，超时 {timeout:g}s，重试 {retries}，"
            f"深度测试 {'开' if deep else '关'}）")

        if total == 0:
            summary = m3ule_probe_summarize([])
            summary["elapsed_ms"] = 0
            summary["cancelled"] = False
            self.sig_worker_finished.emit(summary)
            return

        executor = ThreadPoolExecutor(max_workers=workers, thread_name_prefix="M3ULEProbe")
        future_map = {}
        for task in self._tasks:
            if self._cancel_event.is_set():
                break
            future = executor.submit(
                m3ule_probe_stream_url,
                str(task.get("url", "")), timeout, retries, deep,
                user_agent, proxy, ignore_ssl, self.worker_cancel_check)
            future_map[future] = task
        self.sig_worker_log.emit(f"已提交 {len(future_map)} 个探测任务。")

        done = 0
        batch: list = []
        batch_size = 20 if total > 200 else 1
        progress_step = max(1, total // 200)
        try:
            for future in as_completed(list(future_map.keys())):
                task = future_map.get(future)
                try:
                    payload = future.result()
                except Exception as exc:  # noqa: BLE001
                    payload = m3ule_probe_result_template(str(task.get("url", "")) if task else "")
                    payload["state"] = M3ULE_STATUS_ERROR
                    payload["detail"] = f"{type(exc).__name__}: {exc}"
                if not isinstance(payload, dict):
                    payload = m3ule_probe_result_template("")
                payload["uid"] = task.get("uid", -1) if task else -1
                payload["label"] = task.get("label", "") if task else ""
                self._results.append(payload)
                batch.append(payload)
                done += 1
                if len(batch) >= batch_size:
                    self.sig_worker_results.emit(batch)
                    batch = []
                if done % progress_step == 0 or done == total:
                    self.sig_worker_progress.emit(done, total)
                if self._cancel_event.is_set() and done < total:
                    self.sig_worker_log.emit("收到停止指令，正在结束剩余任务…")
                    break
        finally:
            if batch:
                self.sig_worker_results.emit(batch)
            for future in future_map:
                future.cancel()
            executor.shutdown(wait=False, cancel_futures=True)

        if self._cancel_event.is_set():
            self.sig_worker_progress.emit(done, total)
        summary = m3ule_probe_summarize(self._results)
        summary["elapsed_ms"] = int((time.time() - started) * 1000)
        summary["cancelled"] = self._cancel_event.is_set()
        summary["tested"] = done
        self.sig_worker_log.emit(
            f"测试结束：成功 {summary['ok']} / 部分 {summary['partial']} / 失败 {summary['fail']} / "
            f"超时 {summary['timeout']} / 错误 {summary['error']}，用时 {summary['elapsed_ms'] / 1000:.1f}s")
        self.sig_worker_finished.emit(summary)


# ----------------------------------------------------------------------------
# ID 扫描页
# ----------------------------------------------------------------------------

class M3ULiveEditorIndexMapDialog(QDialog):
    """编号映射表：把「编号 → 频道名」从标题 / 链接里汇总出来，并标注该编号是否还有效。

    典型用途：用户手上的播放列表标题形如 `[000] 广东民生`，本身就带着编号与频道名，
    但链接是否还活着要实测才知道。本对话框把两者合并成一张表：
    编号、频道名、映射来源、实测状态、直播延迟、流ID、链接。
    """

    M3ULE_MAP_COLUMNS = ["编号", "频道名", "来源", "状态", "延迟(s)", "流ID", "链接"]

    def __init__(self, main_window, parent=None):
        super().__init__(parent or main_window)
        self._main_window = main_window
        self._map: dict = {}
        self.setWindowTitle("编号映射表 — 编号 ↔ 频道名 ↔ 可用性")
        self.resize(1000, 620)
        self.setSizeGripEnabled(True)

        layout = QVBoxLayout(self)
        layout.setContentsMargins(8, 8, 8, 8)
        layout.setSpacing(6)

        hint = QLabel(
            "把播放列表标题里内嵌的编号（如 <code>[000] 广东民生</code>）与链接里的编号参数"
            "解析出来，合并成「编号 → 频道名」对照表，并叠加实测状态。<br>"
            "状态为空表示该编号还没测过 —— 在「链接测试」页测一遍即可补齐。")
        hint.setWordWrap(True)
        hint.setStyleSheet("color:#5f6368;")
        layout.addWidget(hint)

        button_row = QHBoxLayout()
        button_row.setSpacing(6)
        btn_current = QPushButton("从当前文件解析")
        btn_current.setToolTip("解析当前打开文件里的标题与链接，汇总编号映射")
        btn_current.clicked.connect(self.dlg_load_from_current)
        button_row.addWidget(btn_current)
        btn_import = QPushButton("导入其它 m3u…")
        btn_import.setToolTip("从另一个 m3u/m3u8 文件解析编号映射（例如旧版本的文件）")
        btn_import.clicked.connect(self.dlg_import_file)
        button_row.addWidget(btn_import)
        btn_db = QPushButton("读入数据库映射")
        btn_db.setToolTip("把之前用「保存映射」存进数据库的编号→频道名读回来")
        btn_db.clicked.connect(self.dlg_load_from_db)
        button_row.addWidget(btn_db)
        button_row.addStretch(1)
        btn_save = QPushButton("保存到数据库")
        btn_save.setToolTip("把当前对照表写入数据库（id_remarks），下次可直接读回")
        btn_save.clicked.connect(self.dlg_save_to_db)
        button_row.addWidget(btn_save)
        btn_csv = QPushButton("导出 CSV…")
        btn_csv.clicked.connect(self.dlg_export_csv)
        button_row.addWidget(btn_csv)
        layout.addLayout(button_row)

        self._table = QTableWidget(0, len(self.M3ULE_MAP_COLUMNS))
        self._table.setHorizontalHeaderLabels(self.M3ULE_MAP_COLUMNS)
        self._table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self._table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self._table.setAlternatingRowColors(True)
        self._table.verticalHeader().setDefaultSectionSize(22)
        self._table.horizontalHeader().setStretchLastSection(True)
        layout.addWidget(self._table, 1)

        progress_row = QHBoxLayout()
        self._progress = QProgressBar()
        self._progress.setRange(0, 100)
        self._progress.setValue(0)
        progress_row.addWidget(self._progress, 1)
        self._lbl_summary = QLabel("—")
        progress_row.addWidget(self._lbl_summary)
        layout.addLayout(progress_row)

        footer = QDialogButtonBox(QDialogButtonBox.Close)
        footer.rejected.connect(self.reject)
        layout.addWidget(footer)

        self.dlg_load_from_current()

    # -- 数据装载 -----------------------------------------------------------
    def dlg_load_from_current(self) -> None:
        document = self._main_window.wnd_document()
        store = self._main_window.wnd_history_store()
        existing = store.dbh_get_id_remarks() if store is not None and store.available else {}
        self._map = m3ule_build_index_name_map(document.entries, existing)
        self.dlg_refresh_table("当前文件")

    def dlg_load_from_db(self) -> None:
        store = self._main_window.wnd_history_store()
        if store is None or not store.available:
            QMessageBox.information(self, "提示", "历史数据库不可用。")
            return
        existing = store.dbh_get_id_remarks()
        document = self._main_window.wnd_document()
        merged = m3ule_build_index_name_map(document.entries, existing)
        for number, record in self._map.items():
            merged.setdefault(number, record)
        self._map = merged
        self.dlg_refresh_table("数据库映射")

    def dlg_import_file(self) -> None:
        last_dir = self._main_window.wnd_config_manager().cfg_get("io/last_open_dir")
        path, _ = QFileDialog.getOpenFileName(
            self, "导入 m3u / m3u8 用于解析编号映射", last_dir,
            "播放列表 (*.m3u *.m3u8 *.txt);;所有文件 (*.*)")
        if not path:
            return
        try:
            document = M3ULiveEditorDocument()
            document.doc_load_from_path(path)
        except Exception as exc:  # noqa: BLE001
            QMessageBox.warning(self, "导入失败", f"{type(exc).__name__}: {exc}")
            return
        imported = m3ule_build_index_name_map(document.entries)
        added = 0
        for number, record in imported.items():
            if number not in self._map:
                self._map[number] = record
                added += 1
            else:
                self._map[number].setdefault("alt_name", record.get("name", ""))
        self.dlg_refresh_table(f"导入 {os.path.basename(path)}")
        self._main_window.wnd_append_log(
            f"编号映射：从 {os.path.basename(path)} 解析出 {len(imported)} 条，新增 {added} 条。")

    # -- 展示 ---------------------------------------------------------------
    def dlg_liveness_by_index(self) -> dict:
        """把当前文件的实测状态按编号汇总（标题里的编号优先，其次链接参数）。"""
        result: dict = {}
        document = self._main_window.wnd_document()
        for entry in document.entries:
            number, _, _ = m3ule_parse_indexed_title(entry.title or "")
            if number is None:
                number = m3ule_extract_index_from_url(entry.url or "")
            if number is None:
                continue
            state = entry.test_state
            previous = result.get(number)
            if previous is None or (not previous.get("state") and state):
                result[number] = {
                    "state": state, "delay": entry.test_delay,
                    "stream_id": entry.test_stream_id, "url": entry.url or "",
                    "cached": entry.test_cached,
                }
        return result

    def dlg_refresh_table(self, source_text: str = "") -> None:
        live = self.dlg_liveness_by_index()
        numbers = sorted(set(self._map.keys()) | set(live.keys()))
        self._progress.setRange(0, max(1, len(numbers)))
        self._progress.setValue(0)
        self._table.setRowCount(0)
        alive = dead = untested = unnamed = 0
        for number in numbers:
            record = self._map.get(number, {})
            info = live.get(number, {})
            state = info.get("state", "")
            if not record.get("name"):
                unnamed += 1
            if state in (M3ULE_STATUS_OK, M3ULE_STATUS_PARTIAL):
                alive += 1
            elif state:
                dead += 1
            else:
                untested += 1
            row = self._table.rowCount()
            self._table.insertRow(row)
            icon = M3ULE_TEST_STATE_ICON_MAP.get(state, "")
            delay = info.get("delay", -1)
            name = record.get("name", "")
            alt = record.get("alt_name", "")
            if alt and alt != name:
                name = f"{name}（另一文件：{alt}）"
            values = [
                str(number),
                name if name else "（待确认）",
                record.get("source", ""),
                f"{icon} {state}".strip(),
                str(delay) if delay is not None and delay >= 0 else "",
                info.get("stream_id", "") or "",
                info.get("url", "") or record.get("url", ""),
            ]
            for column, text in enumerate(values):
                item = QTableWidgetItem(text)
                if column in (0, 4, 5):
                    item.setTextAlignment(Qt.AlignCenter)
                if column == 3:
                    color = M3ULE_TEST_STATE_COLORS.get(state)
                    if color is not None:
                        item.setForeground(QBrush(color))
                    background = M3ULE_TEST_STATE_BG.get(state)
                    if background is not None:
                        item.setBackground(QBrush(background))
                self._table.setItem(row, column, item)
            self._progress.setValue(row + 1)
        self._table.resizeColumnsToContents()
        self._table.horizontalHeader().setStretchLastSection(True)
        summary = (f"{source_text} · 共 {len(numbers)} 个编号 · 已命名 "
                   f"{len(numbers) - unnamed} · 待确认 {unnamed} · "
                   f"有效 {alive} · 失效 {dead} · 未测 {untested}")
        self._lbl_summary.setText(summary)

    @Slot()
    def dlg_save_to_db(self, notify: bool = True) -> int:
        store = self._main_window.wnd_history_store()
        if store is None or not store.available:
            if notify:
                QMessageBox.information(self, "提示", "历史数据库不可用。")
            return 0
        saved = 0
        for number, record in self._map.items():
            name = (record.get("name") or "").strip()
            if not name:
                continue
            store.dbh_set_id_remark(f"idx:{number}", name, record.get("remark", "") or "")
            saved += 1
        self._main_window.wnd_append_log(f"编号映射已保存到数据库（{saved} 条）。")
        self._lbl_summary.setText(f"已保存 {saved} 条编号→频道名 映射到数据库")
        if notify:
            QMessageBox.information(self, "完成", f"已保存 {saved} 条编号→频道名 映射。")
        return saved

    @Slot()
    def dlg_export_csv(self) -> None:
        if self._table.rowCount() == 0:
            QMessageBox.information(self, "提示", "当前没有可导出的映射。")
            return
        base = self._main_window.wnd_config_manager().cfg_get("io/last_save_dir")
        path, _ = QFileDialog.getSaveFileName(
            self, "导出编号映射 CSV", os.path.join(base, "编号映射表.csv"),
            "CSV 文件 (*.csv)")
        if not path:
            return
        headers = [self._table.horizontalHeaderItem(column).text()
                   for column in range(self._table.columnCount())]
        try:
            with open(path, "w", encoding="utf-8-sig", newline="") as handle:
                writer = csv.writer(handle)
                writer.writerow(headers)
                for row in range(self._table.rowCount()):
                    writer.writerow([
                        self._table.item(row, column).text() if self._table.item(row, column)
                        else "" for column in range(self._table.columnCount())])
        except OSError as exc:
            QMessageBox.warning(self, "导出失败", str(exc))
            return
        self._main_window.wnd_config_manager().cfg_set(
            "io/last_save_dir", os.path.dirname(path))
        self._main_window.wnd_append_log(f"已导出编号映射表：{path}")
        QMessageBox.information(self, "完成", f"已导出到：\n{path}")


# ----------------------------------------------------------------------------
# 频道同步对话框
# ----------------------------------------------------------------------------

class M3ULiveEditorSyncDialog(QDialog):
    """频道同步：把「已校对文件的 频道名 → 编号」同步到另一个文件（两种方式）。

    · 方式一「只更新编号」：只改目标文件里**同名**频道链接中的编号数字（以及按选项对齐的
      channelID / 频道号 / tvg-id / tvg-name），分组 / 台标 / 注释与空行等**一律不动**；
      目标里没有的名字，用目标文件最常见的地址模板**追加**到末尾（分组留空，稍后自行分组）；
    · 方式二「整表替换」：以来源频道列表**重建**目标文件的频道区（旧频道清除，同名频道沿用
      原分组与台标，已确认无信号的频道跳过）；
    · 分析过程只读文件，只有点「应用并保存」才写盘（写前自动备份）。
    """

    M3ULE_SYNC_GEOMETRY_KEY = "ui/geometry/sync_ids"
    M3ULE_SYNC_PREVIEW_COLUMNS = ("动作", "频道名称", "原编号", "新编号", "说明", "地址")
    M3ULE_SYNC_ACTION_COLORS = {
        M3ULE_SYNC_ACTION_UPDATE: QColor("#137333"),
        M3ULE_SYNC_ACTION_ADD: QColor("#1a73e8"),
        M3ULE_SYNC_ACTION_REMOVE: QColor("#c5221f"),
        M3ULE_SYNC_ACTION_SKIP: QColor("#9a6b00"),
        M3ULE_SYNC_ACTION_CONFLICT: QColor("#c5221f"),
        M3ULE_SYNC_ACTION_NO_INDEX: QColor("#9a6b00"),
        M3ULE_SYNC_ACTION_UNMATCHED: QColor("#5f6368"),
        M3ULE_SYNC_ACTION_SAME: QColor("#9aa0a6"),
    }

    def __init__(self, main_window, parent=None):
        super().__init__(parent or main_window)
        self._main_window = main_window
        self._plan = None
        self._source_document = None
        self._target_document = None
        self._analyzed_once = False
        self.setWindowTitle("频道同步（把校对好的频道同步到另一个文件）")
        self.setSizeGripEnabled(True)
        self.resize(1180, 760)
        self.setAttribute(Qt.WA_DeleteOnClose, False)
        self.sid_build_ui()
        self.sid_reload_from_config()

    # -- 界面 ---------------------------------------------------------------
    def sid_build_ui(self) -> None:
        root = QVBoxLayout(self)
        root.setContentsMargins(6, 6, 6, 6)
        root.setSpacing(6)

        source_box = QGroupBox("① 校对来源（哪个编号是哪个台，以它为准）")
        source_layout = QGridLayout(source_box)
        source_layout.setContentsMargins(8, 6, 8, 6)
        source_layout.setHorizontalSpacing(6)
        self._combo_source_mode = QComboBox()
        self._combo_source_mode.addItems(M3ULE_SYNC_SOURCE_MODES)
        self._combo_source_mode.setToolTip(
            "「已校对的文件」：用文件里标题的 [编号] 或链接里的编号参数当作确认结果；\n"
            "「数据库编号映射」：用「编号映射表 / ID 扫描页」保存过的频道映射")
        self._combo_source_mode.currentIndexChanged.connect(self.sid_on_option_changed)
        source_layout.addWidget(self._combo_source_mode, 0, 0)
        self._edit_source = QLineEdit()
        self._edit_source.setPlaceholderText(
            "选择已经人工校对好的文件（例如「广州珠江宽频的m3u8直播源 - 154.m3u」）")
        self._edit_source.editingFinished.connect(self.sid_on_option_changed)
        source_layout.addWidget(self._edit_source, 0, 1)
        self._btn_source_browse = QPushButton("选择文件…")
        self._btn_source_browse.clicked.connect(self.sid_choose_source_file)
        source_layout.addWidget(self._btn_source_browse, 0, 2)
        self._btn_source_current = QPushButton("用当前打开的文件")
        self._btn_source_current.clicked.connect(self.sid_use_current_file)
        source_layout.addWidget(self._btn_source_current, 0, 3)
        self._lbl_source_info = QLabel("尚未选择来源")
        self._lbl_source_info.setStyleSheet("color:#5f6368;")
        self._lbl_source_info.setWordWrap(True)
        source_layout.addWidget(self._lbl_source_info, 1, 0, 1, 4)
        source_layout.setColumnStretch(1, 1)
        root.addWidget(source_box)

        target_box = QGroupBox("② 目标文件（只改同名频道的编号，其它信息不动）")
        target_layout = QGridLayout(target_box)
        target_layout.setContentsMargins(8, 6, 8, 6)
        target_layout.setHorizontalSpacing(6)
        self._edit_target = QLineEdit()
        self._edit_target.setPlaceholderText("选择要更新的文件（例如 xteve.m3u）")
        self._edit_target.editingFinished.connect(self.sid_on_option_changed)
        target_layout.addWidget(self._edit_target, 0, 0)
        self._btn_target_browse = QPushButton("选择文件…")
        self._btn_target_browse.clicked.connect(self.sid_choose_target_file)
        target_layout.addWidget(self._btn_target_browse, 0, 1)
        self._lbl_target_info = QLabel("尚未选择目标文件")
        self._lbl_target_info.setStyleSheet("color:#5f6368;")
        self._lbl_target_info.setWordWrap(True)
        target_layout.addWidget(self._lbl_target_info, 1, 0, 1, 2)
        target_layout.setColumnStretch(0, 1)
        root.addWidget(target_box)

        option_box = QGroupBox("③ 同步方式与选项（改动即时保存，下次启动沿用）")
        option_layout = QGridLayout(option_box)
        option_layout.setContentsMargins(8, 6, 8, 6)
        option_layout.setHorizontalSpacing(8)
        option_layout.addWidget(QLabel("同步方式"), 0, 0)
        self._combo_mode = QComboBox()
        self._combo_mode.addItems(M3ULE_SYNC_MODES)
        self._combo_mode.setToolTip(
            "「只更新编号」：只改目标文件里同名频道的编号（其它频道原样保留，可追加缺失的）；\n"
            "「整表替换」：不管旧文件有哪些，直接用来源的频道重建目标文件的频道区，\n"
            "　　　　　　旧文件里不在新列表的频道会被清除（同名频道沿用原分组与台标）。")
        self._combo_mode.currentIndexChanged.connect(self.sid_on_mode_changed)
        option_layout.addWidget(self._combo_mode, 0, 1, 1, 4)
        option_layout.addWidget(QLabel("名字匹配"), 1, 0)
        self._combo_match = QComboBox()
        self._combo_match.addItems(M3ULE_SYNC_MATCH_MODES)
        self._combo_match.setToolTip("「忽略大小写与空格」还会把全角/半角与多余空格视为相同")
        self._combo_match.currentIndexChanged.connect(self.sid_on_option_changed)
        option_layout.addWidget(self._combo_match, 1, 1)
        self._chk_add_missing = QCheckBox("目标里没有的频道按名字新增")
        self._chk_add_missing.toggled.connect(self.sid_on_option_changed)
        option_layout.addWidget(self._chk_add_missing, 1, 2)
        option_layout.addWidget(QLabel("新增条目分组"), 1, 3)
        self._edit_new_group = QLineEdit()
        self._edit_new_group.setPlaceholderText("留空＝不写分组（稍后自行分组）")
        self._edit_new_group.setMaximumWidth(220)
        self._edit_new_group.editingFinished.connect(self.sid_on_option_changed)
        option_layout.addWidget(self._edit_new_group, 1, 4)
        option_layout.addWidget(QLabel("新增条目标题"), 2, 0)
        self._combo_new_title = QComboBox()
        self._combo_new_title.addItems(M3ULE_SYNC_NEW_TITLE_MODES)
        self._combo_new_title.currentIndexChanged.connect(self.sid_on_option_changed)
        option_layout.addWidget(self._combo_new_title, 2, 1)
        self._chk_new_tvg_name = QCheckBox("新增条目同时写 tvg-name（xteve 这类播放器需要）")
        self._chk_new_tvg_name.toggled.connect(self.sid_on_option_changed)
        option_layout.addWidget(self._chk_new_tvg_name, 2, 2, 1, 3)
        option_layout.addWidget(QLabel("对齐字段"), 3, 0)
        self._chk_write_tvg_name = QCheckBox("频道名称写入 tvg-name")
        self._chk_write_tvg_name.setToolTip(
            "用校对文件里确认的名称覆盖目标的 tvg-name（整表替换时一定按校对名称写）")
        self._chk_write_tvg_name.toggled.connect(self.sid_on_option_changed)
        option_layout.addWidget(self._chk_write_tvg_name, 3, 1)
        self._chk_write_title = QCheckBox("标题也用校对名称")
        self._chk_write_title.setToolTip("同名频道的标题写成校对文件里的名称（整表替换时一律按校对名称写）")
        self._chk_write_title.toggled.connect(self.sid_on_option_changed)
        option_layout.addWidget(self._chk_write_title, 3, 2)
        self._chk_write_ids = QCheckBox("channelID / 频道号 / tvg-id 跟随编号")
        self._chk_write_ids.setToolTip(
            "让这三个字段对应该链接里的编号（例如 se_idx=031 → channelID=x-ID.31、\n"
            "频道号 31、tvg-id 31）；xteve 这类播放器靠它把频道对上")
        self._chk_write_ids.toggled.connect(self.sid_on_option_changed)
        option_layout.addWidget(self._chk_write_ids, 3, 3, 1, 2)
        option_layout.addWidget(QLabel("整表替换"), 4, 0)
        self._chk_keep_meta = QCheckBox("同名频道沿用原分组与台标（不丢分组、台标跟着频道）")
        self._chk_keep_meta.setToolTip("关掉就是彻底重建：分组与台标都不沿用（分组留空，需自行重分）")
        self._chk_keep_meta.toggled.connect(self.sid_on_option_changed)
        option_layout.addWidget(self._chk_keep_meta, 4, 1, 1, 2)
        self._chk_skip_dead = QCheckBox("只同步有信号的频道（已确认无信号跳过，未测保留）")
        self._chk_skip_dead.setToolTip(
            "按数据库里的最新检测结果判断：明确判定为失败/无节目的不写入；\n"
            "还没测过的频道照样写入（不看实测结果时请关掉本项）")
        self._chk_skip_dead.toggled.connect(self.sid_on_option_changed)
        option_layout.addWidget(self._chk_skip_dead, 4, 3, 1, 2)
        self._chk_keep_unnamed = QCheckBox("没有名称的编号也写入（标题写 [编号]，稍后补名）")
        self._chk_keep_unnamed.setToolTip(
            "来源里「只有编号、还没填名称」的条目（如 [048]）照样写入，标题就是 [048]、\n"
            "tvg-name 留空；名称补齐后再同步一次即可。关掉就不会写入这些条目")
        self._chk_keep_unnamed.toggled.connect(self.sid_on_option_changed)
        option_layout.addWidget(self._chk_keep_unnamed, 5, 0, 1, 2)
        option_layout.addWidget(QLabel("channelID 前缀"), 5, 2)
        self._edit_id_prefix = QLineEdit()
        self._edit_id_prefix.setPlaceholderText("留空＝自动识别（如 x-ID.）")
        self._edit_id_prefix.setMaximumWidth(220)
        self._edit_id_prefix.setToolTip(
            "新生成的 channelID = 前缀 + 编号；留空时自动从目标文件现有 channelID 里识别")
        self._edit_id_prefix.editingFinished.connect(self.sid_on_option_changed)
        option_layout.addWidget(self._edit_id_prefix, 5, 3)
        self._lbl_option_hint = QLabel("")
        self._lbl_option_hint.setStyleSheet("color:#5f6368;")
        self._lbl_option_hint.setWordWrap(True)
        option_layout.addWidget(self._lbl_option_hint, 6, 0, 1, 5)
        option_layout.setColumnStretch(4, 1)
        root.addWidget(option_box)

        action_row = QHBoxLayout()
        action_row.setSpacing(6)
        self._btn_analyze = QPushButton("开始分析（只读，不写文件）")
        self._btn_analyze.setDefault(True)
        self._btn_analyze.clicked.connect(self.sid_analyze)
        action_row.addWidget(self._btn_analyze)
        self._btn_export = QPushButton("导出预览 CSV…")
        self._btn_export.clicked.connect(self.sid_export_preview_csv)
        action_row.addWidget(self._btn_export)
        action_row.addStretch(1)
        root.addLayout(action_row)

        # 摘要 / 提醒会有很多行（例如「同编号被两条频道占用」），放进可滚动区，
        # 高度不够时滚动查看，不会被压扁截断。
        self._lbl_summary = QLabel("点「开始分析」查看将要发生的改动。")
        self._lbl_summary.setWordWrap(True)
        self._lbl_summary.setAlignment(Qt.AlignTop | Qt.AlignLeft)
        self._lbl_summary.setTextInteractionFlags(Qt.TextSelectableByMouse)
        self._lbl_summary.setAutoFillBackground(False)
        self._scroll_summary = QScrollArea()
        self._scroll_summary.setWidget(self._lbl_summary)
        self._scroll_summary.setWidgetResizable(True)
        self._scroll_summary.setFrameShape(QFrame.NoFrame)
        self._scroll_summary.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self._scroll_summary.setVerticalScrollBarPolicy(Qt.ScrollBarAsNeeded)
        self._scroll_summary.setMinimumHeight(26)
        self._scroll_summary.setMaximumHeight(130)
        self._scroll_summary.viewport().setAutoFillBackground(False)
        self._scroll_summary.setStyleSheet("QScrollArea{background:transparent;}")
        root.addWidget(self._scroll_summary)

        self._table = QTableWidget(0, len(self.M3ULE_SYNC_PREVIEW_COLUMNS))
        self._table.setHorizontalHeaderLabels(list(self.M3ULE_SYNC_PREVIEW_COLUMNS))
        self._table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self._table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self._table.verticalHeader().setDefaultSectionSize(22)
        header = self._table.horizontalHeader()
        for column, mode in enumerate((QHeaderView.ResizeToContents, QHeaderView.Interactive,
                                       QHeaderView.ResizeToContents, QHeaderView.ResizeToContents,
                                       QHeaderView.Stretch, QHeaderView.Interactive)):
            header.setSectionResizeMode(column, mode)
        self._table.setColumnWidth(1, 190)
        self._table.setColumnWidth(5, 420)
        root.addWidget(self._table, 1)

        bottom = QHBoxLayout()
        bottom.setSpacing(6)
        self._progress = QProgressBar()
        self._progress.setRange(0, 100)
        self._progress.setValue(0)
        self._progress.setMaximumWidth(240)
        bottom.addWidget(self._progress)
        self._lbl_status = QLabel("就绪")
        self._lbl_status.setStyleSheet("color:#5f6368;")
        bottom.addWidget(self._lbl_status, 1)
        self._btn_apply = QPushButton("应用并保存到目标文件")
        self._btn_apply.clicked.connect(self.sid_apply)
        bottom.addWidget(self._btn_apply)
        self._btn_apply_as = QPushButton("另存为副本…")
        self._btn_apply_as.setToolTip("不覆盖目标文件，把同步结果另存成新文件（先看效果再决定）")
        self._btn_apply_as.clicked.connect(self.sid_apply_as)
        bottom.addWidget(self._btn_apply_as)
        self._btn_close = QPushButton("关闭")
        self._btn_close.clicked.connect(self.close)
        bottom.addWidget(self._btn_close)
        root.addLayout(bottom)

    # -- 设置读写 -----------------------------------------------------------
    def sid_config(self):
        return self._main_window.wnd_config_manager()

    def sid_option_widgets(self) -> list:
        """所有会落盘的选项控件（读取/保存/联动都走这一份清单，避免漏项）。"""
        return [self._combo_source_mode, self._combo_match, self._combo_new_title,
                self._combo_mode, self._edit_source, self._edit_target, self._edit_new_group,
                self._edit_id_prefix, self._chk_add_missing, self._chk_new_tvg_name,
                self._chk_write_tvg_name, self._chk_write_title, self._chk_write_ids,
                self._chk_keep_meta, self._chk_skip_dead, self._chk_keep_unnamed]

    def sid_reload_from_config(self) -> None:
        config = self.sid_config()
        widgets = self.sid_option_widgets()
        for widget in widgets:
            widget.blockSignals(True)
        try:
            self._combo_source_mode.setCurrentText(
                self.sid_combo_text(self._combo_source_mode, config.cfg_get("sync/source_mode")))
            self._combo_match.setCurrentText(
                self.sid_combo_text(self._combo_match, config.cfg_get("sync/match_mode")))
            self._combo_new_title.setCurrentText(
                self.sid_combo_text(self._combo_new_title, config.cfg_get("sync/new_title_mode")))
            self._combo_mode.setCurrentText(
                self.sid_combo_text(self._combo_mode, config.cfg_get("sync/mode")))
            self._edit_source.setText(config.cfg_get("sync/source_file"))
            self._edit_target.setText(config.cfg_get("sync/target_file"))
            self._edit_new_group.setText(config.cfg_get("sync/new_group"))
            self._edit_id_prefix.setText(config.cfg_get("sync/id_prefix"))
            self._chk_add_missing.setChecked(config.cfg_get("sync/add_missing", True))
            self._chk_new_tvg_name.setChecked(config.cfg_get("sync/new_tvg_name", True))
            self._chk_write_tvg_name.setChecked(config.cfg_get("sync/write_tvg_name", True))
            self._chk_write_title.setChecked(config.cfg_get("sync/write_title", True))
            self._chk_write_ids.setChecked(config.cfg_get("sync/write_ids", True))
            self._chk_keep_meta.setChecked(config.cfg_get("sync/keep_meta", True))
            self._chk_skip_dead.setChecked(config.cfg_get("sync/skip_dead", True))
            self._chk_keep_unnamed.setChecked(config.cfg_get("sync/keep_unnamed", True))
        finally:
            for widget in widgets:
                widget.blockSignals(False)
        geometry = config.cfg_load_geometry(self.M3ULE_SYNC_GEOMETRY_KEY)
        if not geometry.isEmpty():
            self.restoreGeometry(geometry)
        self.sid_apply_mode_enabled_state()
        self.sid_invalidate_plan()
        self.sid_refresh_source_info()

    @staticmethod
    def sid_combo_text(combo: QComboBox, value: str) -> str:
        text = str(value or "").strip()
        if text and combo.findText(text) < 0:
            combo.addItem(text)
        return text or combo.itemText(0)

    @Slot()
    def sid_on_mode_changed(self) -> None:
        self.sid_apply_mode_enabled_state()
        self.sid_on_option_changed()

    def sid_apply_mode_enabled_state(self) -> None:
        """按同步方式显示/隐藏只有该方式才有意义的选项（避免误以为会生效）。"""
        rebuild = m3ule_sync_mode_is_rebuild(self._combo_mode.currentText())
        for widget in (self._chk_add_missing, self._chk_new_tvg_name, self._edit_new_group):
            widget.setEnabled(not rebuild)
        for widget in (self._chk_keep_meta, self._chk_skip_dead, self._chk_keep_unnamed):
            widget.setEnabled(rebuild)
        if rebuild:
            hint = ("整表替换：目标文件的频道区会按来源重建 —— 旧文件里不在新列表的频道会被清除，"
                    "同名频道沿用原分组与台标，已确认无信号的频道跳过；写盘前自动备份。")
        else:
            hint = ("只更新编号：目标文件里的其它频道原样保留；缺失的名字追加到末尾"
                    "（分组留空）。")
        self._lbl_option_hint.setText(hint)

    @Slot()
    def sid_on_option_changed(self) -> None:
        config = self.sid_config()
        config.cfg_set_many(self.sid_settings_snapshot())
        self.sid_invalidate_plan()
        self.sid_refresh_source_info()

    def sid_settings_snapshot(self) -> dict:
        """当前界面上的选项（用于落盘与关闭时保存）。"""
        return {
            "sync/source_mode": self._combo_source_mode.currentText(),
            "sync/source_file": self._edit_source.text().strip(),
            "sync/target_file": self._edit_target.text().strip(),
            "sync/match_mode": self._combo_match.currentText(),
            "sync/mode": self._combo_mode.currentText(),
            "sync/add_missing": self._chk_add_missing.isChecked(),
            "sync/new_group": self._edit_new_group.text().strip(),
            "sync/new_tvg_name": self._chk_new_tvg_name.isChecked(),
            "sync/new_title_mode": self._combo_new_title.currentText(),
            "sync/write_tvg_name": self._chk_write_tvg_name.isChecked(),
            "sync/write_title": self._chk_write_title.isChecked(),
            "sync/write_ids": self._chk_write_ids.isChecked(),
            "sync/keep_meta": self._chk_keep_meta.isChecked(),
            "sync/skip_dead": self._chk_skip_dead.isChecked(),
            "sync/keep_unnamed": self._chk_keep_unnamed.isChecked(),
            "sync/id_prefix": self._edit_id_prefix.text().strip(),
        }

    def sid_match_options(self) -> dict:
        options = m3ule_sync_match_options(self._combo_match.currentText())
        options["mode"] = self._combo_mode.currentText()
        options["add_missing"] = self._chk_add_missing.isChecked()
        options["new_group"] = self._edit_new_group.text().strip()
        options["new_tvg_name"] = self._chk_new_tvg_name.isChecked()
        options["new_title_mode"] = self._combo_new_title.currentText()
        options["write_tvg_name"] = self._chk_write_tvg_name.isChecked()
        options["write_title"] = self._chk_write_title.isChecked()
        options["write_ids"] = self._chk_write_ids.isChecked()
        options["keep_meta"] = self._chk_keep_meta.isChecked()
        options["skip_dead"] = self._chk_skip_dead.isChecked()
        options["keep_unnamed"] = self._chk_keep_unnamed.isChecked()
        options["id_prefix"] = self._edit_id_prefix.text().strip()
        return options

    def sid_probe_states(self, entries) -> dict:
        """来源条目的信号状态：{链接规范化键: True 有信号 / False 无信号 / None 未测}。

        「只同步有信号的频道」靠它判断；数据库读不到时只能看条目自身的实测结果。
        """
        states: dict = {}
        keys: list = []
        for entry in (entries or []):
            key = m3ule_probe_cache_key(entry.url or "")
            if not key:
                continue
            keys.append(key)
            avail = m3ule_test_state_to_avail(entry.test_state or "")
            if avail is not None:
                states[key] = avail
        store = self._main_window.wnd_history_store()
        if store is not None and store.available and keys:
            try:
                for key, record in (store.dbh_get_probe_cache(keys) or {}).items():
                    if key in states:
                        continue
                    avail = m3ule_test_state_to_avail(str((record or {}).get("state") or ""))
                    if avail is not None:
                        states[key] = avail
            except Exception:  # noqa: BLE001
                pass
        return states

    # -- 文件选择 -----------------------------------------------------------
    def sid_file_dialog_dir(self) -> str:
        config = self.sid_config()
        return (config.cfg_get("io/last_open_dir") or config.cfg_get("io/last_save_dir")
                or m3ule_get_program_dir())

    @Slot()
    def sid_choose_source_file(self) -> None:
        path, _ = QFileDialog.getOpenFileName(
            self, "选择已校对的文件", self.sid_file_dialog_dir(),
            "播放列表 (*.m3u *.m3u8 *.txt);;所有文件 (*.*)")
        if not path:
            return
        self._edit_source.setText(path)
        self.sid_config().cfg_set("io/last_open_dir", os.path.dirname(path))
        self.sid_on_option_changed()
        self.sid_analyze()

    @Slot()
    def sid_choose_target_file(self) -> None:
        path, _ = QFileDialog.getOpenFileName(
            self, "选择要更新的目标文件", self.sid_file_dialog_dir(),
            "播放列表 (*.m3u *.m3u8 *.txt);;所有文件 (*.*)")
        if not path:
            return
        self._edit_target.setText(path)
        self.sid_config().cfg_set("io/last_open_dir", os.path.dirname(path))
        self.sid_on_option_changed()
        self.sid_analyze()

    @Slot()
    def sid_use_current_file(self) -> None:
        path = (self._main_window.wnd_document().path or "").strip()
        if not path:
            QMessageBox.information(self, "提示", "当前还没有打开文件。")
            return
        self._edit_source.setText(path)
        self.sid_on_option_changed()
        self.sid_analyze()

    # -- 读取与计划 ---------------------------------------------------------
    def sid_source_path(self) -> str:
        if self._combo_source_mode.currentText() != M3ULE_SYNC_SOURCE_MODES[0]:
            return ""
        return self._edit_source.text().strip()

    def sid_target_path(self) -> str:
        return self._edit_target.text().strip()

    def sid_load_source_entries(self) -> list:
        path = self.sid_source_path()
        if not path or not os.path.isfile(path):
            return []
        document = M3ULiveEditorDocument()
        document.doc_load_from_path(path)
        self._source_document = document
        return document.entries

    def sid_load_target_document(self) -> bool:
        path = self.sid_target_path()
        if not path or not os.path.isfile(path):
            self._target_document = None
            return False
        document = M3ULiveEditorDocument()
        document.doc_load_from_path(path)
        self._target_document = document
        return True

    def sid_db_remarks(self) -> dict:
        store = self._main_window.wnd_history_store()
        if store is None or not store.available:
            return {}
        try:
            return store.dbh_get_id_remarks()
        except Exception:  # noqa: BLE001
            return {}

    def sid_invalidate_plan(self) -> None:
        self._plan = None
        self._lbl_summary.setText("选项或文件变了，请重新点「开始分析」。")
        self.sid_fit_summary_height()

    def sid_refresh_source_info(self) -> None:
        if self._combo_source_mode.currentText() != M3ULE_SYNC_SOURCE_MODES[0]:
            count = len(self.sid_db_remarks())
            self._lbl_source_info.setText(
                f"来源：数据库编号映射（{count} 条）—— 来自「编号映射表 / ID 扫描页」保存过的映射")
            return
        path = self.sid_source_path()
        if not path:
            self._lbl_source_info.setText("尚未选择来源文件")
            return
        self._lbl_source_info.setText(
            f"来源文件：{path}" if os.path.isfile(path) else f"文件不存在：{path}")

    def sid_build_plan(self) -> dict:
        """读两个文件（校对来源 + 目标）并算出计划；数据不完整时返回空计划。"""
        source_entries = self.sid_load_source_entries()
        remarks = self.sid_db_remarks() if not source_entries else {}
        options = self.sid_match_options()
        match = m3ule_sync_match_options(self._combo_match.currentText())
        confirmed = m3ule_sync_build_confirmed(
            entries=source_entries, remarks=remarks, match=match)
        if not source_entries and not remarks:
            self._lbl_source_info.setText("校对来源是空的：请选择已校对的文件，或先保存编号映射。")
            return {}
        if self.sid_source_path():
            self._lbl_source_info.setText(
                f"来源文件：{self.sid_source_path()} —— {len(source_entries)} 条，"
                f"认出 {confirmed['count']} 个频道名（同名多编号 {confirmed['conflict_count']} 个）")
        if not self.sid_load_target_document():
            self._lbl_target_info.setText(f"目标文件不存在：{self.sid_target_path()}")
            return {}
        target_entries = self._target_document.entries
        template_info = m3ule_sync_dominant_template(target_entries)
        prefix = m3ule_sync_channel_id_prefix(target_entries)
        self._lbl_target_info.setText(
            f"目标文件：{self.sid_target_path()} —— {len(target_entries)} 条；"
            f"最常见地址模板 {template_info['count']} 条（补零 {template_info['width']} 位）；"
            f"channelID 写法 " + (f"「{prefix}编号」" if prefix else "「纯编号」"))
        named_pairs: list = []
        if not source_entries:
            for record in confirmed["names"].values():
                if record["conflict"] or record["number"] is None:
                    continue
                named_pairs.append({"name": record["name"] or record["normalized"],
                                    "number": int(record["number"])})
        options["remarks"] = remarks or None
        options["states"] = (self.sid_probe_states(source_entries)
                             if (m3ule_sync_mode_is_rebuild(options["mode"])
                                 and options["skip_dead"]) else None)
        options["named_pairs"] = named_pairs or None
        return m3ule_sync_plan(source_entries, target_entries, options)

    @Slot()
    def sid_analyze(self) -> None:
        if not self.sid_target_path():
            QMessageBox.information(self, "提示", "请先选择要更新的目标文件。")
            return
        if (self.sid_source_path() and self.sid_target_path()
                and os.path.abspath(self.sid_source_path())
                == os.path.abspath(self.sid_target_path())):
            QMessageBox.information(
                self, "提示", "校对来源与目标文件是同一个文件，无需同步。\n\n"
                "请把「目标文件」指向要更新的那个文件（例如 xteve.m3u）。")
            return
        self.sid_set_progress(5, "正在读取文件…")
        try:
            plan = self.sid_build_plan()
        except Exception as exc:  # noqa: BLE001
            self.sid_set_progress(0, "分析失败")
            QMessageBox.critical(self, "分析失败", f"{type(exc).__name__}: {exc}")
            return
        if not plan:
            self.sid_set_progress(0, "缺少可用的来源或目标")
            return
        self.sid_set_progress(60, "正在生成预览…")
        self._plan = plan
        self.sid_fill_table(m3ule_sync_plan_rows(plan))
        self.sid_set_progress(100, "分析完成（未写任何文件）")
        warnings = "".join("<br>" + html.escape(item) for item in plan["warnings"])
        self._lbl_summary.setText(
            "<b>" + html.escape(m3ule_sync_summary_text(plan)) + "</b>" + warnings)
        self.sid_fit_summary_height()
        mode_note = "整表替换" if m3ule_sync_mode_is_rebuild(plan["mode"]) else "只更新编号"
        prefix_note = ("自动识别" if plan.get("id_prefix_auto") else "手动指定") + \
            f" channelID 前缀「{plan.get('id_prefix') or '（无，纯编号）'}」"
        self._lbl_option_hint.setText(f"{mode_note}；{prefix_note}")
        self._main_window.wnd_append_log(
            "频道同步分析（%s）：%s（来源 %s → 目标 %s）"
            % (mode_note, m3ule_sync_summary_text(plan),
               self.sid_source_path() or "数据库编号映射", self.sid_target_path()))
        self._analyzed_once = True

    def sid_fit_summary_height(self) -> None:
        """按当前宽度算出摘要需要的行数，避免内容被压扁（超出部分滚动查看）。

        同时让面板本身跟着内容伸缩：内容少时只占一行高度（不浪费空间），
        内容多时最多占 84 像素（再多就在面板内滚动）。
        """
        scroll = getattr(self, "_scroll_summary", None)
        label = getattr(self, "_lbl_summary", None)
        if scroll is None or label is None:
            return
        width = max(scroll.viewport().width() - 4, 200)
        # 先清掉上一次设的最小高度再量：QLabel 的 heightForWidth 会被自身最小高度顶住，
        # 不清掉就会出现「内容变短了但高度不回落」。
        label.setMinimumHeight(0)
        needed = label.heightForWidth(width)
        if needed <= 0:
            needed = label.sizeHint().height()
        label.setMinimumHeight(needed)
        scroll.setMinimumHeight(max(min(needed + 8, 84), 26))

    def sid_fill_table(self, rows: list) -> None:
        self._table.setSortingEnabled(False)
        self._table.setRowCount(0)
        for row in rows:
            position = self._table.rowCount()
            self._table.insertRow(position)
            for column, value in enumerate(row):
                item = QTableWidgetItem(str(value))
                if column == 0:
                    color = self.M3ULE_SYNC_ACTION_COLORS.get(str(value))
                    if color is not None:
                        item.setForeground(color)
                if column == 5:
                    item.setToolTip(str(value))
                self._table.setItem(position, column, item)
        self._table.setSortingEnabled(True)

    # -- 应用 ---------------------------------------------------------------
    @Slot()
    def sid_apply(self) -> bool:
        return bool(self.sid_write_target(in_place=True))

    @Slot()
    def sid_apply_as(self) -> None:
        self.sid_write_target(in_place=False)

    def sid_write_target(self, in_place: bool) -> bool:
        if not self.sid_target_path():
            QMessageBox.information(self, "提示", "请先选择目标文件。")
            return False
        try:
            plan = self.sid_build_plan()
        except Exception as exc:  # noqa: BLE001
            QMessageBox.critical(self, "分析失败", f"{type(exc).__name__}: {exc}")
            return False
        if not plan:
            return False
        stats = m3ule_sync_plan_summary(plan)
        rebuild = bool(stats["rebuild"])
        if not rebuild and not stats["update"] and not stats["add"]:
            self._plan = plan
            self.sid_fill_table(m3ule_sync_plan_rows(plan))
            QMessageBox.information(
                self, "无需改动",
                "没有需要更新或新增的条目：\n\n" + m3ule_sync_summary_text(plan))
            return False
        if rebuild and not stats["write"]:
            self._plan = plan
            self.sid_fill_table(m3ule_sync_plan_rows(plan))
            QMessageBox.information(
                self, "没有可写入的频道",
                "整表替换需要至少一条可用的来源频道（有名称 + 有编号 + 未确认无信号）。\n\n"
                + m3ule_sync_summary_text(plan))
            return False
        target = self.sid_target_path()
        if in_place:
            if rebuild:
                message = (
                    f"整表替换：目标文件的频道区会按来源重建。\n\n{target}\n\n"
                    f"· 写入 {stats['write']} 条频道（沿用原分组/台标 {stats['kept_meta']} 条、"
                    f"新增 {stats['fresh']} 条）\n"
                    f"· **删除旧频道 {stats['remove']} 条**（旧文件里不在新列表里的）\n"
                    f"· 跳过 {stats['skip']} 条来源条目（原因见预览「跳过」行）\n"
                    "· channelID / 频道号 / tvg-id 一律对应链接里的编号，名称写入 tvg-name 与标题\n"
                    "· 分组与台标按同名频道沿用；文件头 / 注释行保留\n"
                    "· 写盘前会自动备份原文件（可在「文件与备份」里设置保留份数）\n\n现在写入吗？")
            else:
                message = (
                    f"将更新 {stats['update']} 条同名频道、追加 {stats['add']} 条新频道：\n\n"
                    f"{target}\n\n"
                    "· 同名频道只改链接里的编号（必要时连标题里的编号），并按选项对齐\n"
                    "  channelID / 频道号 / tvg-id / tvg-name —— 分组、台标等其它信息一律不动\n"
                    "· 追加的条目放在文件末尾，分组留空\n"
                    "· 写盘前会自动备份原文件（可在「文件与备份」里设置保留份数）\n\n现在写入吗？")
            reply = QMessageBox.question(
                self, "确认写入目标文件", message,
                QMessageBox.Yes | QMessageBox.No, QMessageBox.Yes)
            if reply != QMessageBox.Yes:
                return False
        else:
            suffix = "_已整表替换.m3u" if rebuild else "_已同步编号.m3u"
            default = os.path.splitext(os.path.basename(target))[0] + suffix
            path, _ = QFileDialog.getSaveFileName(
                self, "另存为副本（先看效果再决定要不要覆盖）",
                os.path.join(self.sid_file_dialog_dir(), default),
                "播放列表 (*.m3u *.m3u8);;所有文件 (*.*)")
            if not path:
                return False
            target = path
        self.sid_set_progress(5, "正在应用改动…")
        try:
            if os.path.isfile(target) and self.sid_config().cfg_get("io/auto_backup_on_save"):
                backup = self._main_window.wnd_backup_file(target)
                if backup:
                    self._main_window.wnd_append_log(f"同步前已备份：{backup}")
            result = m3ule_sync_apply_plan(
                self._target_document, plan,
                progress=lambda value, text: self.sid_set_progress(10 + value * 0.6, text))
            self.sid_set_progress(75, "正在写入文件…")
            QApplication.processEvents()
            self._target_document.doc_save_to_path(
                target,
                progress=lambda value, text: self.sid_set_progress(75 + value * 0.25, text))
            self.sid_set_progress(100, "同步完成")
        except Exception as exc:  # noqa: BLE001
            self.sid_set_progress(0, "写入失败")
            self._main_window.wnd_append_log(
                f"频道同步失败：{type(exc).__name__}: {exc}\n{traceback.format_exc()}")
            QMessageBox.critical(self, "写入失败", f"{type(exc).__name__}: {exc}")
            return False
        self.sid_config().cfg_set("io/last_save_dir", os.path.dirname(target))
        if rebuild:
            done_text = ("整表替换完成：写入 %d 条频道（删除旧条目 %d 条）"
                         % (result.get("written", 0), result.get("removed", 0)))
            self._lbl_status.setText(
                f"已写入 {os.path.basename(target)}：重写 {result.get('written', 0)} 条，"
                f"删除旧条目 {result.get('removed', 0)} 条")
        else:
            done_text = ("频道同步完成：更新 %d 条、新增 %d 条"
                         % (result["updated"], result["added"]))
            self._lbl_status.setText(
                f"已写入 {os.path.basename(target)}：更新 {result['updated']} 条，"
                f"新增 {result['added']} 条")
        self._main_window.wnd_append_log(f"{done_text} → {target}")
        if in_place:
            self.sid_analyze()      # 写完后重新分析，确认结果与文件一致
        QMessageBox.information(
            self, "完成",
            f"已写入：{target}\n\n{self._lbl_status.text().split('：', 1)[-1]}")
        return True

    @Slot()
    def sid_export_preview_csv(self) -> None:
        if not self._plan:
            QMessageBox.information(self, "提示", "请先点「开始分析」。")
            return
        base_dir = (self.sid_config().cfg_get("io/last_save_dir")
                    or self.sid_file_dialog_dir())
        default = os.path.splitext(os.path.basename(self.sid_target_path() or "同步预览"))[0] \
            + "_同步预览.csv"
        path, _ = QFileDialog.getSaveFileName(
            self, "导出同步预览 CSV", os.path.join(base_dir, default), "CSV 文件 (*.csv)")
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8-sig", newline="") as handle:
                writer = csv.writer(handle)
                for row in m3ule_sync_plan_csv_rows(self._plan):
                    writer.writerow(row)
        except OSError as exc:
            QMessageBox.warning(self, "导出失败", str(exc))
            return
        self.sid_config().cfg_set("io/last_save_dir", os.path.dirname(path))
        self._main_window.wnd_append_log(f"已导出同步预览：{path}")
        self._lbl_status.setText(f"已导出预览：{os.path.basename(path)}")

    # -- 状态与关闭 ---------------------------------------------------------
    def sid_set_progress(self, value: int, text: str = "") -> None:
        self._progress.setValue(max(0, min(100, int(value))))
        if text:
            self._lbl_status.setText(text)
        QApplication.processEvents()

    def sid_plan_stats_text(self) -> str:
        return m3ule_sync_summary_text(self._plan) if self._plan else "尚未分析"

    @Slot()
    def sid_auto_analyze(self) -> None:
        """首次打开且两边的文件都已记住时，自动分析一次（只读，不写文件）。"""
        if self._analyzed_once:
            return
        if self.sid_source_path() and not os.path.isfile(self.sid_source_path()):
            return
        if self._combo_source_mode.currentText() != M3ULE_SYNC_SOURCE_MODES[0] \
                and not self.sid_db_remarks():
            return
        if not self.sid_target_path() or not os.path.isfile(self.sid_target_path()):
            return
        self.sid_analyze()

    def showEvent(self, event) -> None:
        super().showEvent(event)
        if not self._analyzed_once:
            QTimer.singleShot(50, self.sid_auto_analyze)

    def closeEvent(self, event) -> None:
        config = self.sid_config()
        config.cfg_save_geometry(self.M3ULE_SYNC_GEOMETRY_KEY, self.saveGeometry())
        config.cfg_set_many(self.sid_settings_snapshot())
        event.accept()


# ----------------------------------------------------------------------------
# ID 扫描页
# ----------------------------------------------------------------------------

class M3ULiveEditorIdScanTab(QWidget):
    """按编号区间批量探测，找出可用的 ID 及其节目情况。"""

    M3ULE_SCAN_COLUMNS = ["编号", "链接", "状态", "HTTP", "耗时(ms)", "分片",
                          "详情", "当前频道(可填)", "备注(可填)"]

    def __init__(self, main_window, parent=None):
        super().__init__(parent)
        self._main_window = main_window
        self._worker = None
        self._row_by_id: dict = {}
        self._result_rows: list = []
        self._build_ui()

    def _build_ui(self) -> None:
        root = QVBoxLayout(self)
        root.setContentsMargins(6, 6, 6, 6)
        root.setSpacing(4)

        template_box = QGroupBox("编号模板（使用 {id} 或 {id:3} 作为编号占位符）")
        template_layout = QHBoxLayout(template_box)
        self._edit_template = QLineEdit()
        self._edit_template.setPlaceholderText(
            "http://116.199.5.51:8114/hls/Fsv_chan_hls_se_idx={id:3}&FvSeid=1&...m3u8")
        self._edit_template.setText(self._main_window.wnd_config_manager().cfg_get("scan/template"))
        template_layout.addWidget(self._edit_template, 1)
        self._btn_extract = QPushButton("从当前文件提取")
        self._btn_extract.setToolTip("取当前文件第一条链接，自动把编号替换为 {id:宽度}")
        self._btn_extract.clicked.connect(self.tab_scan_extract_template)
        template_layout.addWidget(self._btn_extract)
        self._btn_use_selected = QPushButton("用选中行提取")
        self._btn_use_selected.clicked.connect(lambda: self.tab_scan_extract_template(use_selected=True))
        template_layout.addWidget(self._btn_use_selected)
        self._btn_from_titles = QPushButton("从文件标题生成编号映射")
        self._btn_from_titles.setToolTip(
            "把当前文件标题里内嵌的编号（如 [000] 广东民生）解析出来，\n"
            "自动填入下面「当前频道」列，省去逐条手工录入")
        self._btn_from_titles.clicked.connect(self.tab_scan_fill_from_titles)
        template_layout.addWidget(self._btn_from_titles)
        root.addWidget(template_box)

        params = QGridLayout()
        params.setHorizontalSpacing(8)
        params.setVerticalSpacing(4)
        config = self._main_window.wnd_config_manager()

        params.addWidget(QLabel("起始编号："), 0, 0)
        self._spin_start = QSpinBox()
        self._spin_start.setRange(0, 9999999)
        self._spin_start.setValue(config.cfg_get("scan/start"))
        params.addWidget(self._spin_start, 0, 1)
        params.addWidget(QLabel("结束编号："), 0, 2)
        self._spin_end = QSpinBox()
        self._spin_end.setRange(0, 9999999)
        self._spin_end.setValue(config.cfg_get("scan/end"))
        params.addWidget(self._spin_end, 0, 3)
        params.addWidget(QLabel("步长："), 0, 4)
        self._spin_step = QSpinBox()
        self._spin_step.setRange(1, 1000)
        self._spin_step.setValue(config.cfg_get("scan/step"))
        params.addWidget(self._spin_step, 0, 5)
        params.addWidget(QLabel("补零位数："), 0, 6)
        self._spin_pad = QSpinBox()
        self._spin_pad.setRange(0, 8)
        self._spin_pad.setValue(config.cfg_get("scan/pad"))
        params.addWidget(self._spin_pad, 0, 7)
        params.addWidget(QLabel("并发："), 0, 8)
        self._spin_workers = QSpinBox()
        self._spin_workers.setRange(1, 64)
        self._spin_workers.setValue(config.cfg_get("scan/workers"))
        params.addWidget(self._spin_workers, 0, 9)

        params.addWidget(QLabel("超时(s)："), 1, 0)
        self._spin_timeout = QDoubleSpinBox()
        self._spin_timeout.setRange(0.5, 120.0)
        self._spin_timeout.setSingleStep(0.5)
        self._spin_timeout.setValue(config.cfg_get("scan/timeout"))
        params.addWidget(self._spin_timeout, 1, 1)
        self._chk_deep = QCheckBox("深度测试（校验是否有节目）")
        self._chk_deep.setChecked(config.cfg_get("scan/deep"))
        params.addWidget(self._chk_deep, 1, 2, 1, 3)
        self._chk_alive_only = QCheckBox("结果只保留可用编号")
        params.addWidget(self._chk_alive_only, 1, 5, 1, 2)
        params.setColumnStretch(10, 1)
        root.addLayout(params)

        button_row = QHBoxLayout()
        self._btn_start = QPushButton("开始扫描")
        self._btn_start.clicked.connect(self.tab_scan_start)
        button_row.addWidget(self._btn_start)
        self._btn_stop = QPushButton("停止")
        self._btn_stop.setEnabled(False)
        self._btn_stop.clicked.connect(self.tab_scan_stop)
        button_row.addWidget(self._btn_stop)
        self._btn_clear = QPushButton("清空结果")
        self._btn_clear.clicked.connect(self.tab_scan_clear)
        button_row.addWidget(self._btn_clear)
        self._btn_export_csv = QPushButton("导出 CSV")
        self._btn_export_csv.clicked.connect(self.tab_scan_export_csv)
        button_row.addWidget(self._btn_export_csv)
        self._btn_export_m3u = QPushButton("导出 M3U（仅可用）")
        self._btn_export_m3u.clicked.connect(self.tab_scan_export_m3u)
        button_row.addWidget(self._btn_export_m3u)
        self._btn_copy_alive = QPushButton("复制可用链接")
        self._btn_copy_alive.clicked.connect(self.tab_scan_copy_alive)
        button_row.addWidget(self._btn_copy_alive)
        self._btn_html5 = QPushButton("弹窗播放所选")
        self._btn_html5.setToolTip("用内嵌播放器（FFmpeg / VLC 内核）播放选中行，"
                                  "便于确认“这个编号现在是什么台”")
        self._btn_html5.clicked.connect(self.tab_scan_play_html5)
        button_row.addWidget(self._btn_html5)
        self._btn_save_map = QPushButton("保存频道映射")
        self._btn_save_map.setToolTip("把“当前频道/备注”写入本地数据库，便于下次比对")
        self._btn_save_map.clicked.connect(self.tab_scan_save_mapping)
        button_row.addWidget(self._btn_save_map)
        button_row.addStretch(1)
        root.addLayout(button_row)

        progress_row = QHBoxLayout()
        self._progress = QProgressBar()
        self._progress.setRange(0, 100)
        self._progress.setValue(0)
        progress_row.addWidget(self._progress, 1)
        self._lbl_summary = QLabel("就绪")
        progress_row.addWidget(self._lbl_summary)
        root.addLayout(progress_row)

        self._table = QTableWidget(0, len(self.M3ULE_SCAN_COLUMNS))
        self._table.setHorizontalHeaderLabels(self.M3ULE_SCAN_COLUMNS)
        header = self._table.horizontalHeader()
        header.setSectionResizeMode(1, QHeaderView.Stretch)
        for column in (0, 2, 3, 4, 5):
            header.setSectionResizeMode(column, QHeaderView.ResizeToContents)
        for column in (6, 7, 8):
            header.setSectionResizeMode(column, QHeaderView.Interactive)
        self._table.setColumnWidth(6, 220)
        self._table.setColumnWidth(7, 140)
        self._table.setColumnWidth(8, 140)
        self._table.verticalHeader().setVisible(False)
        self._table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self._table.setEditTriggers(QAbstractItemView.DoubleClicked | QAbstractItemView.EditKeyPressed)
        self._table.setAlternatingRowColors(True)
        root.addWidget(self._table, 1)

        self._edit_template.textChanged.connect(self.tab_scan_persist_settings)
        for widget in (self._spin_start, self._spin_end, self._spin_step,
                       self._spin_pad, self._spin_workers):
            widget.valueChanged.connect(self.tab_scan_persist_settings)
        self._spin_timeout.valueChanged.connect(self.tab_scan_persist_settings)
        self._chk_deep.toggled.connect(self.tab_scan_persist_settings)

    # -- 设置持久化 ---------------------------------------------------------
    @Slot()
    def tab_scan_persist_settings(self) -> None:
        config = self._main_window.wnd_config_manager()
        config.cfg_set_many({
            "scan/template": self._edit_template.text(),
            "scan/start": self._spin_start.value(),
            "scan/end": self._spin_end.value(),
            "scan/step": self._spin_step.value(),
            "scan/pad": self._spin_pad.value(),
            "scan/workers": self._spin_workers.value(),
            "scan/timeout": self._spin_timeout.value(),
            "scan/deep": self._chk_deep.isChecked(),
        })

    # -- 模板提取 -----------------------------------------------------------
    @Slot()
    def tab_scan_extract_template(self, use_selected: bool = False) -> None:
        entry = None
        if use_selected:
            rows = self._main_window.wnd_selected_entries()
            if rows:
                entry = rows[0]
        if entry is None:
            model = self._main_window.wnd_document_model()
            entries = model.mdl_entries()
            entry = entries[0] if entries else None
        if entry is None or not (entry.url or "").strip():
            QMessageBox.information(self, "提示", "当前文件没有可用于提取的链接。")
            return
        url = entry.url.strip()
        match = re.search(r"(?P<key>idx|index|id|channel|ch)=(?P<num>\d+)", url, re.IGNORECASE)
        if not match:
            self._edit_template.setText(url)
            QMessageBox.information(
                self, "提示",
                "未能自动识别编号，已填入完整链接。请手动把编号数字替换为 {id}。")
            return
        width = len(match.group("num"))
        placeholder = f"{{id:{width}}}"
        template = url[:match.start("num")] + placeholder + url[match.end("num"):]
        self._edit_template.setText(template)
        self._spin_pad.setValue(width)
        self._spin_start.setValue(0)
        self._spin_end.setValue(10 ** width - 1)
        self._main_window.wnd_append_log(
            f"已从链接提取扫描模板（编号字段 {match.group('key')}，宽度 {width}）：{template}")

    # -- 扫描流程 -----------------------------------------------------------
    @Slot()
    def tab_scan_start(self) -> None:
        if self._worker is not None and self._worker.isRunning():
            return
        template = self._edit_template.text().strip()
        if not template:
            QMessageBox.warning(self, "提示", "请先填写编号模板。")
            return
        if "{id}" not in template and not re.search(r"\{id:\d+\}", template):
            QMessageBox.warning(self, "提示", "模板中必须包含 {id} 或 {id:3} 占位符。")
            return
        start = self._spin_start.value()
        end = self._spin_end.value()
        step = max(1, self._spin_step.value())
        if end < start:
            start, end = end, start
            self._spin_start.setValue(start)
            self._spin_end.setValue(end)
        pad = self._spin_pad.value()
        tasks = []
        for value in range(start, end + 1, step):
            number_text = str(value).zfill(pad) if pad > 0 else str(value)
            url = re.sub(r"\{id(:\d+)?\}", number_text, template)
            tasks.append({"uid": value, "url": url, "label": str(value)})
        if not tasks:
            QMessageBox.information(self, "提示", "区间内没有可扫描的编号。")
            return
        if len(tasks) > 5000:
            reply = QMessageBox.question(
                self, "确认",
                f"将扫描 {len(tasks)} 个编号，可能耗时较长，是否继续？",
                QMessageBox.Yes | QMessageBox.No, QMessageBox.Yes)
            if reply != QMessageBox.Yes:
                return

        self.tab_scan_clear()
        self._row_by_id = {}
        self._table.setRowCount(len(tasks))
        for row, task in enumerate(tasks):
            items = [task["label"], task["url"], "等待…", "", "", "", "", "", ""]
            for column, text in enumerate(items):
                item = QTableWidgetItem(text)
                if column in (2, 7, 8):
                    item.setFlags(Qt.ItemIsEnabled | Qt.ItemIsSelectable | Qt.ItemIsEditable)
                else:
                    item.setFlags(Qt.ItemIsEnabled | Qt.ItemIsSelectable)
                self._table.setItem(row, column, item)
            self._row_by_id[task["uid"]] = row

        config = self._main_window.wnd_config_manager()
        options = {
            "workers": self._spin_workers.value(),
            "timeout": self._spin_timeout.value(),
            "retries": config.cfg_get("probe/retries"),
            "deep": self._chk_deep.isChecked(),
            "user_agent": config.cfg_get_user_agent(),
            "proxy": config.cfg_get_proxy(),
            "ignore_ssl": config.cfg_get("probe/ignore_ssl"),
        }
        self._progress.setRange(0, len(tasks))
        self._progress.setValue(0)
        self._btn_start.setEnabled(False)
        self._btn_stop.setEnabled(True)
        self._alive_count = 0
        self._finished_count = 0

        self._worker = M3ULiveEditorProbeWorker(tasks, options, parent=self)
        self._worker.sig_worker_results.connect(self.tab_scan_on_results)
        self._worker.sig_worker_progress.connect(self.tab_scan_on_progress)
        self._worker.sig_worker_log.connect(self._main_window.wnd_append_log)
        self._worker.sig_worker_finished.connect(self.tab_scan_on_finished)
        self._worker.start()
        self._main_window.wnd_append_log(
            f"ID 扫描启动：范围 {start}~{end}，步长 {step}，共 {len(tasks)} 个编号。")

    @Slot()
    def tab_scan_stop(self) -> None:
        if self._worker is not None and self._worker.isRunning():
            self._worker.worker_request_cancel()
            self._btn_stop.setEnabled(False)

    @Slot(object)
    def tab_scan_on_results(self, payloads: list) -> None:
        for payload in payloads:
            number = payload.get("uid", -1)
            row = self._row_by_id.get(number)
            if row is None:
                continue
            state = payload.get("state", "")
            icon = M3ULE_TEST_STATE_ICON_MAP.get(state, "")
            values = [
                str(number),
                payload.get("url", ""),
                f"{icon} {state}".strip(),
                str(payload.get("http_status", -1)) if payload.get("http_status", -1) >= 0 else "",
                str(payload.get("ms", -1)) if payload.get("ms", -1) >= 0 else "",
                str(payload.get("segments", -1)) if payload.get("segments", -1) >= 0 else "",
                payload.get("detail", ""),
            ]
            for column, text in enumerate(values):
                item = self._table.item(row, column)
                if item is None:
                    item = QTableWidgetItem()
                    self._table.setItem(row, column, item)
                item.setText(text)
                if column == 2:
                    color = M3ULE_TEST_STATE_COLORS.get(state)
                    if color is not None:
                        item.setForeground(QBrush(color))
                    background = M3ULE_TEST_STATE_BG.get(state)
                    if background is not None:
                        item.setBackground(QBrush(background))
            if payload.get("state") in (M3ULE_STATUS_OK, M3ULE_STATUS_PARTIAL):
                self._alive_count = getattr(self, "_alive_count", 0) + 1
            self._finished_count = getattr(self, "_finished_count", 0) + 1

    @Slot(int, int)
    def tab_scan_on_progress(self, done: int, total: int) -> None:
        self._progress.setRange(0, max(1, total))
        self._progress.setValue(done)
        self._lbl_summary.setText(
            f"进度 {done}/{total} · 可用 {getattr(self, '_alive_count', 0)}")

    @Slot(dict)
    def tab_scan_on_finished(self, summary: dict) -> None:
        self._btn_start.setEnabled(True)
        self._btn_stop.setEnabled(False)
        self._progress.setValue(self._progress.maximum())
        self._lbl_summary.setText(
            f"完成：可用 {summary.get('ok', 0) + summary.get('partial', 0)} / "
            f"共 {summary.get('total', 0)} · 用时 {summary.get('elapsed_ms', 0) / 1000:.1f}s")
        self._main_window.wnd_append_log(
            f"ID 扫描完成：可用 {summary.get('ok', 0) + summary.get('partial', 0)}，"
            f"失败 {summary.get('fail', 0)}，超时 {summary.get('timeout', 0)}。")
        if self._chk_alive_only.isChecked():
            self.tab_scan_filter_alive_only()
        store = self._main_window.wnd_history_store()
        if store is not None:
            store.dbh_record_scan_run(
                self._edit_template.text(), self._spin_start.value(),
                self._spin_end.value(), self._spin_step.value(),
                summary.get("total", 0),
                summary.get("ok", 0) + summary.get("partial", 0),
                "深度测试" if self._chk_deep.isChecked() else "浅测试")
        self._worker = None

    def tab_scan_filter_alive_only(self) -> None:
        for row in range(self._table.rowCount()):
            item = self._table.item(row, 2)
            text = item.text() if item else ""
            alive = (M3ULE_STATUS_OK in text) or (M3ULE_STATUS_PARTIAL in text)
            self._table.setRowHidden(row, not alive)

    # -- 结果导出 -----------------------------------------------------------
    def tab_scan_collect_rows(self, alive_only: bool = False) -> list:
        rows = []
        for row in range(self._table.rowCount()):
            number_item = self._table.item(row, 0)
            url_item = self._table.item(row, 1)
            state_item = self._table.item(row, 2)
            http_item = self._table.item(row, 3)
            ms_item = self._table.item(row, 4)
            seg_item = self._table.item(row, 5)
            detail_item = self._table.item(row, 6)
            name_item = self._table.item(row, 7)
            remark_item = self._table.item(row, 8)
            state_text = state_item.text() if state_item else ""
            if alive_only and not (M3ULE_STATUS_OK in state_text or M3ULE_STATUS_PARTIAL in state_text):
                continue
            rows.append({
                "number": number_item.text() if number_item else "",
                "url": url_item.text() if url_item else "",
                "state": state_text, "http": http_item.text() if http_item else "",
                "ms": ms_item.text() if ms_item else "", "segments": seg_item.text() if seg_item else "",
                "detail": detail_item.text() if detail_item else "",
                "channel": name_item.text() if name_item else "",
                "remark": remark_item.text() if remark_item else "",
            })
        return rows

    @Slot()
    def tab_scan_export_csv(self) -> None:
        rows = self.tab_scan_collect_rows()
        if not rows:
            QMessageBox.information(self, "提示", "没有可导出的扫描结果。")
            return
        default_dir = self._main_window.wnd_config_manager().cfg_get("io/last_save_dir")
        path, _ = QFileDialog.getSaveFileName(
            self, "导出扫描结果", os.path.join(default_dir, "ID扫描结果.csv"), "CSV 文件 (*.csv)")
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8-sig", newline="") as handle:
                writer = csv.writer(handle)
                writer.writerow(["编号", "链接", "状态", "HTTP", "耗时(ms)", "分片", "详情", "当前频道", "备注"])
                for row in rows:
                    writer.writerow([row["number"], row["url"], row["state"], row["http"],
                                     row["ms"], row["segments"], row["detail"],
                                     row["channel"], row["remark"]])
        except OSError as exc:
            QMessageBox.warning(self, "导出失败", str(exc))
            return
        self._main_window.wnd_config_manager().cfg_set("io/last_save_dir", os.path.dirname(path))
        self._main_window.wnd_append_log(f"扫描结果已导出：{path}")
        QMessageBox.information(self, "完成", f"已导出 {len(rows)} 行到：\n{path}")

    @Slot()
    def tab_scan_export_m3u(self) -> None:
        rows = self.tab_scan_collect_rows(alive_only=True)
        if not rows:
            QMessageBox.information(self, "提示", "没有可用的编号可导出。")
            return
        default_dir = self._main_window.wnd_config_manager().cfg_get("io/last_save_dir")
        path, _ = QFileDialog.getSaveFileName(
            self, "导出可用编号", os.path.join(default_dir, "ID扫描可用.m3u"), "M3U 文件 (*.m3u *.m3u8)")
        if not path:
            return
        group = f"ID扫描 {datetime.now().strftime('%Y-%m-%d %H:%M')}"
        lines = ['#EXTM3U']
        for row in rows:
            name = row["channel"] or row["remark"] or f"ID-{row['number']}"
            attrs = OrderedDict()
            attrs["channelID"] = f"x-ID.{row['number']}"
            attrs["tvg-chno"] = row["number"]
            attrs["tvg-name"] = name
            attrs["tvg-id"] = row["number"]
            attrs["group-title"] = group
            lines.append(m3ule_format_extinf_line("0", attrs, name))
            lines.append(row["url"])
        try:
            with open(path, "w", encoding="utf-8") as handle:
                handle.write("\n".join(lines) + "\n")
        except OSError as exc:
            QMessageBox.warning(self, "导出失败", str(exc))
            return
        self._main_window.wnd_config_manager().cfg_set("io/last_save_dir", os.path.dirname(path))
        self._main_window.wnd_append_log(f"可用编号已导出为 M3U：{path}（{len(rows)} 条）")
        QMessageBox.information(self, "完成", f"已导出 {len(rows)} 条可用编号到：\n{path}")

    @Slot()
    def tab_scan_copy_alive(self) -> None:
        rows = self.tab_scan_collect_rows(alive_only=True)
        if not rows:
            QMessageBox.information(self, "提示", "没有可用的链接。")
            return
        text = "\n".join(row["url"] for row in rows)
        QApplication.clipboard().setText(text)
        self._main_window.wnd_append_log(f"已复制 {len(rows)} 条可用链接到剪贴板。")
        QMessageBox.information(self, "完成", f"已复制 {len(rows)} 条可用链接到剪贴板。")

    def tab_scan_playable_entries(self) -> tuple:
        """返回扫描结果表里 (带链接的条目列表, 当前选中行在列表中的索引)。

        整表一起带走，播放弹窗里的「上一个 / 下一个」就能直接连着翻看，不用回表格重新选行。
        """
        row = self._table.currentRow()
        entries = []
        start_index = 0
        for index in range(self._table.rowCount()):
            url_item = self._table.item(index, 1)
            row_url = url_item.text().strip() if url_item else ""
            if not row_url:
                continue
            if index == row:
                start_index = len(entries)
            name_item = self._table.item(index, 7)
            number_item = self._table.item(index, 0)
            row_title = (name_item.text().strip() if name_item else "") or (
                f"ID-{number_item.text()}" if number_item else "")
            entries.append(M3ULiveEditorEntry(url=row_url, title=row_title))
        return entries, start_index

    @Slot()
    def tab_scan_play_html5(self) -> None:
        """播放扫描结果里选中那一行的链接，便于人工确认“这个编号现在是什么台”。"""
        if self._table.currentRow() < 0:
            QMessageBox.information(self, "提示", "请先在下方结果表中选择一行。")
            return
        entries, start_index = self.tab_scan_playable_entries()
        if not entries:
            QMessageBox.information(self, "提示", "该行没有可用链接。")
            return
        current = entries[start_index]
        self._main_window.wnd_open_url_in_html5(current.url, current.title,
                                                entries=entries, start_index=start_index)

    @Slot()
    def tab_scan_fill_from_titles(self) -> None:
        """把当前文件标题里内嵌的编号 → 频道名，填进扫描表的「当前频道」列。

        不会新建行：只为表格里已存在的编号填名，并可选择把尚未出现的编号补成新行。
        """
        document = self._main_window.wnd_document()
        store = self._main_window.wnd_history_store()
        existing = store.dbh_get_id_remarks() if store is not None and store.available else {}
        mapping = m3ule_build_index_name_map(document.entries, existing)
        if not mapping:
            QMessageBox.information(
                self, "提示",
                "没有从当前文件解析出编号映射。\n\n"
                "本功能识别两种写法：\n"
                "  · 标题带编号：[000] 广东民生\n"
                "  · 链接带编号参数：...se_idx=000...")
            return

        filled = 0
        appended = 0
        unknown = 0
        for number in sorted(mapping):
            record = mapping[number]
            name = (record.get("name") or "").strip()
            row = self._row_by_id.get(number)
            if row is None:
                row = self._table.rowCount()
                self._table.insertRow(row)
                self._row_by_id[number] = row
                self._table.setItem(row, 0, QTableWidgetItem(str(number)))
                self._table.setItem(row, 1, QTableWidgetItem(record.get("url", "") or ""))
                appended += 1
            if not name:
                # 标题里只有编号没有名称：保留该行但标注“待确认”，方便后续人工补名
                unknown += 1
                item = self._table.item(row, 7)
                if item is None:
                    item = QTableWidgetItem()
                    self._table.setItem(row, 7, item)
                if not item.text().strip():
                    item.setText("待确认")
                continue
            item = self._table.item(row, 7)
            if item is None:
                item = QTableWidgetItem()
                self._table.setItem(row, 7, item)
            if not item.text().strip() or item.text().strip() == "待确认":
                item.setText(name)
                filled += 1
            remark_item = self._table.item(row, 8)
            if remark_item is None:
                self._table.setItem(row, 8, QTableWidgetItem(record.get("remark", "") or ""))
        text = (f"已从文件标题生成映射：填入 {filled} 条"
                + (f"，新增 {appended} 行" if appended else "")
                + (f"，其中 {unknown} 条标题里没有频道名（标记为「待确认」）" if unknown else ""))
        self._lbl_summary.setText(text)
        self._main_window.wnd_append_log(
            f"编号映射：从当前文件标题解析出 {len(mapping)} 条，"
            f"填入「当前频道」{filled} 条"
            + (f"，新增 {appended} 行" if appended else "")
            + (f"，待确认 {unknown} 条。" if unknown else "。"))

    @Slot()
    def tab_scan_save_mapping(self, notify: bool = True) -> int:
        store = self._main_window.wnd_history_store()
        if store is None:
            if notify:
                QMessageBox.information(self, "提示", "历史数据库不可用。")
            return 0
        rows = self.tab_scan_collect_rows()
        saved = 0
        for row in rows:
            if not (row["channel"] or "").strip() and not (row["remark"] or "").strip():
                continue
            store.dbh_set_id_remark(f"idx:{row['number']}", row["channel"], row["remark"])
            saved += 1
        self._main_window.wnd_append_log(f"已保存 {saved} 条频道映射到数据库。")
        if notify:
            QMessageBox.information(self, "完成", f"已保存 {saved} 条频道映射。")
        return saved

    @Slot()
    def tab_scan_clear(self) -> None:
        self._table.setRowCount(0)
        self._row_by_id = {}
        self._progress.setValue(0)
        self._lbl_summary.setText("就绪")
        self._alive_count = 0
        self._finished_count = 0


# ----------------------------------------------------------------------------
# 对比分析页
# ----------------------------------------------------------------------------

class M3ULiveEditorDiffTab(QWidget):
    """比较新旧两个 m3u 文件，找出编号 / 名称 / 链接变化及增删。"""

    M3ULE_DIFF_COLUMNS = ["变化类型", "频道名称", "匹配键", "A频道号", "B频道号",
                          "A编号", "B编号", "A链接", "B链接", "说明"]
    # 编号双列对比：按「编号」对齐，左右两列分别是旧文件与新扫描的结果
    M3ULE_PAIR_COLUMNS = ["编号", "旧（以前）", "新（现在）", "变化", "旧链接", "新链接"]
    # 信号过滤：把「没信号」的噪音排掉，只看真正在用的那些编号
    M3ULE_PAIR_SIGNAL_FILTERS = [
        "全部（不按信号过滤）",
        "只看两侧都有信号",
        "只看旧侧有信号（查缺失）",
        "只看新侧有信号",
        "只看缺失项（旧有→现无）",
        "只看待确认（旧有→现未测）",
    ]
    M3ULE_PAIR_SIGNAL_KEYS = ["all", "both_alive", "old_alive", "new_alive", "missing",
                              "unclear"]
    # 两侧来源的设置键（下次启动自动恢复记忆的选择）
    M3ULE_PAIR_SOURCE_KEYS = {"_edit_pair_old": "diff/pair_old",
                              "_edit_pair_new": "diff/pair_new"}
    M3ULE_PAIR_CHANGE_COLORS = {
        "新增可用": QColor("#137333"),
        "新失效": QColor("#c5221f"),
        "仍然可用": QColor("#5f6368"),
        "仍然不可用": QColor("#9aa0a6"),
        "仅旧有": QColor("#9a6b00"),
        "仅新有": QColor("#1a73e8"),
        "未测": QColor("#9aa0a6"),
    }
    # 「以前有信号、现在没测过」用橙色提示，与「确实没了」的红色区分开
    M3ULE_PAIR_UNCLEAR_COLOR = QColor("#c05621")

    def __init__(self, main_window, parent=None):
        super().__init__(parent)
        self._main_window = main_window
        self._diff_rows: list = []
        self._pair_rows: list = []
        self._pair_old: tuple = ("current",)
        self._pair_new: tuple = ("current",)
        self._build_ui()

    def _build_ui(self) -> None:
        root = QVBoxLayout(self)
        root.setContentsMargins(6, 6, 6, 6)
        root.setSpacing(4)

        self._modes = QTabWidget()
        self._modes.setDocumentMode(True)
        self._modes.addTab(self.tab_diff_build_file_page(), "文件对比（按频道匹配键）")
        self._modes.addTab(self.tab_diff_pair_build_page(), "编号双列对比（ID 增删 / 失效）")
        self._modes.currentChanged.connect(self.tab_diff_mode_changed)
        root.addWidget(self._modes, 1)

    def tab_diff_mode_changed(self, index: int) -> None:
        self._main_window.wnd_config_manager().cfg_set("diff/mode", int(index))

    # ------------------------------------------------------------------
    # 页 1：原有「文件对比」
    # ------------------------------------------------------------------
    def tab_diff_build_file_page(self) -> QWidget:
        page = QWidget()
        root = QVBoxLayout(page)
        root.setContentsMargins(0, 4, 0, 0)
        root.setSpacing(4)

        for label, attr_name in (("文件 A（旧）", "_edit_path_a"), ("文件 B（新）", "_edit_path_b")):
            row = QHBoxLayout()
            row.addWidget(QLabel(f"{label}："))
            editor = QLineEdit()
            editor.setReadOnly(True)
            setattr(self, attr_name, editor)
            row.addWidget(editor, 1)
            button = QPushButton("浏览…")
            button.clicked.connect(lambda _checked=False, target=attr_name: self.tab_diff_browse(target))
            row.addWidget(button)
            root.addLayout(row)

        tools = QHBoxLayout()
        self._btn_use_current = QPushButton("把当前打开文件作为 A")
        self._btn_use_current.clicked.connect(self.tab_diff_use_current)
        tools.addWidget(self._btn_use_current)
        self._btn_swap = QPushButton("交换 A / B")
        self._btn_swap.clicked.connect(self.tab_diff_swap)
        tools.addWidget(self._btn_swap)
        self._btn_run = QPushButton("开始对比")
        self._btn_run.clicked.connect(self.tab_diff_run)
        tools.addWidget(self._btn_run)
        self._chk_only_diff = QCheckBox("只看有差异的条目")
        self._chk_only_diff.setChecked(True)
        self._chk_only_diff.toggled.connect(self.tab_diff_refresh_view)
        tools.addWidget(self._chk_only_diff)
        self._btn_export = QPushButton("导出 CSV")
        self._btn_export.clicked.connect(self.tab_diff_export_csv)
        tools.addWidget(self._btn_export)
        self._btn_apply = QPushButton("把 B 的变化应用到当前文件")
        self._btn_apply.setToolTip("用文件 B 中相同匹配键的链接/频道名更新当前打开的文件")
        self._btn_apply.clicked.connect(self.tab_diff_apply_to_current)
        tools.addWidget(self._btn_apply)
        tools.addStretch(1)
        root.addLayout(tools)

        progress_row = QHBoxLayout()
        self._progress = QProgressBar()
        self._progress.setRange(0, 100)
        progress_row.addWidget(self._progress, 1)
        self._lbl_summary = QLabel("就绪")
        progress_row.addWidget(self._lbl_summary)
        root.addLayout(progress_row)

        self._table = QTableWidget(0, len(self.M3ULE_DIFF_COLUMNS))
        self._table.setHorizontalHeaderLabels(self.M3ULE_DIFF_COLUMNS)
        header = self._table.horizontalHeader()
        for column in (0, 2, 3, 4, 5, 6):
            header.setSectionResizeMode(column, QHeaderView.ResizeToContents)
        header.setSectionResizeMode(1, QHeaderView.Interactive)
        self._table.setColumnWidth(1, 170)
        for column in (7, 8):
            header.setSectionResizeMode(column, QHeaderView.Stretch)
        header.setSectionResizeMode(9, QHeaderView.Interactive)
        self._table.setColumnWidth(9, 260)
        self._table.verticalHeader().setVisible(False)
        self._table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self._table.setAlternatingRowColors(True)
        self._table.setSelectionBehavior(QAbstractItemView.SelectRows)
        root.addWidget(self._table, 1)
        return page

    # ------------------------------------------------------------------
    # 页 2：编号双列对比（旧 vs 新，按 ID 对齐）
    # ------------------------------------------------------------------
    def tab_diff_pair_build_page(self) -> QWidget:
        page = QWidget()
        root = QVBoxLayout(page)
        root.setContentsMargins(0, 4, 0, 0)
        root.setSpacing(4)

        hint = QLabel(
            "按 <b>编号（ID）</b> 对齐左右两列，用于回答：「跟以前那份文件比，"
            "现在多了哪些台、哪些台失效了」。<br>"
            "左侧通常选<b>以前的文件</b>，右侧选<b>当前扫描结果</b>；"
            "某一侧是否「有信号」优先取实测结果，没有实测时自动查检测缓存。<br>"
            "两侧的选择会<b>自动记住</b>，下次启动直接点「开始双列对比」即可。")
        hint.setWordWrap(True)
        hint.setStyleSheet("color:#5f6368;")
        root.addWidget(hint)

        for label, attr_name, default in (
                ("旧（以前）", "_edit_pair_old", "文件 / 当前文件 / ID 扫描结果"),
                ("新（现在）", "_edit_pair_new", "文件 / 当前文件 / ID 扫描结果")):
            row = QHBoxLayout()
            row.addWidget(QLabel(f"{label}："))
            editor = QLineEdit()
            editor.setReadOnly(True)
            editor.setPlaceholderText(default)
            setattr(self, attr_name, editor)
            row.addWidget(editor, 1)
            btn_file = QPushButton("选择文件…")
            btn_file.clicked.connect(
                lambda _checked=False, attr=attr_name: self.tab_diff_pair_browse(attr))
            row.addWidget(btn_file)
            btn_current = QPushButton("当前文件")
            btn_current.setToolTip("使用当前打开的文件（含已实测的状态）")
            btn_current.clicked.connect(
                lambda _checked=False, attr=attr_name: self.tab_diff_pair_use_current(attr))
            row.addWidget(btn_current)
            btn_scan = QPushButton("ID 扫描结果")
            btn_scan.setToolTip("使用「ID 扫描」页刚扫描出来的结果（适合 0–999 这种区间扫描）")
            btn_scan.clicked.connect(
                lambda _checked=False, attr=attr_name: self.tab_diff_pair_use_scan(attr))
            row.addWidget(btn_scan)
            btn_db = QPushButton("数据库映射")
            btn_db.setToolTip("使用数据库里保存过的「编号 → 频道名」映射（只含编号，不含信号状态）")
            btn_db.clicked.connect(
                lambda _checked=False, attr=attr_name: self.tab_diff_pair_use_db(attr))
            row.addWidget(btn_db)
            if attr_name == "_edit_pair_new":
                btn_scan.setDefault(True)
            root.addLayout(row)

        tools = QHBoxLayout()
        self._btn_pair_run = QPushButton("开始双列对比")
        self._btn_pair_run.clicked.connect(self.tab_diff_pair_run)
        tools.addWidget(self._btn_pair_run)
        self._btn_pair_swap = QPushButton("交换 旧 / 新")
        self._btn_pair_swap.clicked.connect(self.tab_diff_pair_swap)
        tools.addWidget(self._btn_pair_swap)

        tools.addWidget(QLabel("信号过滤："))
        self._combo_pair_signal = QComboBox()
        for label in self.M3ULE_PAIR_SIGNAL_FILTERS:
            self._combo_pair_signal.addItem(label)
        self._combo_pair_signal.setToolTip(
            "「只看旧侧有信号」＝ 只看以前能播的台，用来检查现在有没有缺失。\n"
            "「只看缺失项」＝ 直接列出「以前有信号、现在确实没了」的编号。\n"
            "「只看待确认」＝ 以前有信号、现在还没测过（既不能说没了，也不能说还在）。")
        self._combo_pair_signal.currentIndexChanged.connect(
            self.tab_diff_pair_signal_changed)
        tools.addWidget(self._combo_pair_signal)

        self._chk_pair_only_changed = QCheckBox("只看有变化")
        self._chk_pair_only_changed.setChecked(True)
        self._chk_pair_only_changed.toggled.connect(self.tab_diff_pair_refresh_view)
        tools.addWidget(self._chk_pair_only_changed)
        self._chk_pair_history_old = QCheckBox("旧侧用最早历史记录")
        self._chk_pair_history_old.setToolTip(
            "勾选后，「旧（以前）」一侧优先取该链接在「测试历史」里**最早**的一次实测结果。\n"
            "检测缓存只保留每个链接的最新结果；若新旧文件用的是同一批链接，\n"
            "不勾选就永远看不到「以前能播、现在不能」的缺失。")
        self._chk_pair_history_old.setChecked(True)
        self._chk_pair_history_old.toggled.connect(self.tab_diff_pair_history_old_changed)
        tools.addWidget(self._chk_pair_history_old)
        self._btn_pair_export = QPushButton("导出 CSV")
        self._btn_pair_export.clicked.connect(self.tab_diff_pair_export_csv)
        tools.addWidget(self._btn_pair_export)
        tools.addStretch(1)
        root.addLayout(tools)

        progress_row = QHBoxLayout()
        self._pair_progress = QProgressBar()
        self._pair_progress.setRange(0, 100)
        progress_row.addWidget(self._pair_progress, 1)
        self._lbl_pair_summary = QLabel("就绪")
        self._lbl_pair_summary.setWordWrap(True)
        progress_row.addWidget(self._lbl_pair_summary, 3)
        root.addLayout(progress_row)

        self._lbl_pair_filter_hint = QLabel("")
        self._lbl_pair_filter_hint.setStyleSheet("color:#1a73e8;")
        root.addWidget(self._lbl_pair_filter_hint)

        self._pair_table = QTableWidget(0, len(self.M3ULE_PAIR_COLUMNS))
        self._pair_table.setHorizontalHeaderLabels(self.M3ULE_PAIR_COLUMNS)
        header = self._pair_table.horizontalHeader()
        for column in (0, 3):
            header.setSectionResizeMode(column, QHeaderView.ResizeToContents)
        for column in (1, 2):
            header.setSectionResizeMode(column, QHeaderView.Interactive)
            self._pair_table.setColumnWidth(column, 210)
        for column in (4, 5):
            header.setSectionResizeMode(column, QHeaderView.Stretch)
        self._pair_table.verticalHeader().setVisible(False)
        self._pair_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self._pair_table.setAlternatingRowColors(True)
        self._pair_table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self._pair_table.setSortingEnabled(True)
        root.addWidget(self._pair_table, 1)
        return page

    # -- 来源选择 -----------------------------------------------------------
    def tab_diff_pair_source_label(self, source: tuple) -> str:
        """把来源元组渲染成界面说明文字（手动选择与启动恢复共用同一套文案）。"""
        if not source:
            return ""
        kind = source[0]
        if kind == "file":
            path = source[1] if len(source) > 1 else ""
            label = f"文件：{path}"
            if path and not os.path.isfile(path):
                label += "（文件不存在）"
            return label
        if kind == "current":
            path = self._main_window.wnd_current_path()
            return (f"当前文件：{os.path.basename(path)}（含实测结果）" if path
                    else "当前打开的文件（含实测结果）")
        if kind == "scan":
            count = self._main_window._tab_scan._table.rowCount()
            return (f"ID 扫描结果：{count} 个编号" if count
                    else "ID 扫描结果（需先在「ID 扫描」页扫描）")
        if kind == "db":
            store = self._main_window.wnd_history_store()
            count = store.dbh_count_rows("id_remarks") if store is not None else 0
            return f"数据库映射：{count} 条" if count else "数据库映射（库里还没有映射）"
        return ""

    def tab_diff_pair_set_source(self, target_attr: str, source: tuple,
                                 persist: bool = True) -> None:
        """设置某一侧的来源（同时更新说明文字，并记住以便下次启动沿用）。"""
        editor = getattr(self, target_attr, None)
        if editor is None:
            return
        if target_attr == "_edit_pair_old":
            self._pair_old = tuple(source)
        else:
            self._pair_new = tuple(source)
        editor.setText(self.tab_diff_pair_source_label(source))
        if persist:
            self.tab_diff_pair_persist_sources()

    def tab_diff_pair_persist_sources(self) -> None:
        """把两侧来源写进设置（下次启动自动恢复）。"""
        config = self._main_window.wnd_config_manager()
        for attr, key in self.M3ULE_PAIR_SOURCE_KEYS.items():
            source = self._pair_old if attr == "_edit_pair_old" else self._pair_new
            config.cfg_set(key, json.dumps(
                {"kind": source[0] if source else "",
                 "path": source[1] if source and len(source) > 1 else ""},
                ensure_ascii=False))

    def tab_diff_pair_restore_sources(self) -> int:
        """启动时恢复上次两侧的对比来源，返回恢复成功的侧数。"""
        config = self._main_window.wnd_config_manager()
        restored = 0
        for attr, key in self.M3ULE_PAIR_SOURCE_KEYS.items():
            raw = str(config.cfg_get(key, "") or "").strip()
            if not raw:
                continue
            try:
                payload = json.loads(raw)
            except (ValueError, TypeError):
                continue
            if not isinstance(payload, dict):
                continue
            kind = str(payload.get("kind") or "")
            path = str(payload.get("path") or "")
            if kind == "file":
                if not path:
                    continue
                source = ("file", path)
                if not os.path.isfile(path):
                    self._main_window.wnd_append_log(
                        f"对比分析：上次的对比文件已不存在，仍按原样恢复：{path}")
            elif kind in ("current", "scan", "db"):
                source = (kind,)
            else:
                continue
            self.tab_diff_pair_set_source(attr, source, persist=False)
            restored += 1
        return restored

    @Slot()
    def tab_diff_pair_browse(self, target_attr: str) -> None:
        default_dir = self._main_window.wnd_config_manager().cfg_get("io/last_open_dir")
        path, _ = QFileDialog.getOpenFileName(
            self, "选择 M3U 文件", default_dir,
            "播放列表 (*.m3u *.m3u8 *.txt);;所有文件 (*.*)")
        if not path:
            return
        self.tab_diff_pair_set_source(target_attr, ("file", path))
        self._main_window.wnd_config_manager().cfg_set("io/last_open_dir", os.path.dirname(path))

    @Slot()
    def tab_diff_pair_use_current(self, target_attr: str) -> None:
        self.tab_diff_pair_set_source(target_attr, ("current",))

    @Slot()
    def tab_diff_pair_use_scan(self, target_attr: str) -> None:
        count = self._main_window._tab_scan._table.rowCount()
        if not count:
            QMessageBox.information(
                self, "提示",
                "「ID 扫描」页还没有结果。\n\n请先到「ID 扫描」页设置区间（例如 0–999）"
                "并「开始扫描」，再回来对比。")
            return
        self.tab_diff_pair_set_source(target_attr, ("scan",))

    @Slot()
    def tab_diff_pair_use_db(self, target_attr: str) -> None:
        store = self._main_window.wnd_history_store()
        if store is None or not store.available:
            QMessageBox.information(self, "提示", "历史数据库不可用。")
            return
        count = store.dbh_count_rows("id_remarks")
        if not count:
            QMessageBox.information(
                self, "提示", "数据库里还没有「编号 → 频道名」映射。\n\n"
                "可在「编号映射表」里解析后点「保存到数据库」。")
            return
        self.tab_diff_pair_set_source(target_attr, ("db",))

    @Slot()
    def tab_diff_pair_swap(self) -> None:
        old_source, new_source = self._pair_new, self._pair_old
        self.tab_diff_pair_set_source("_edit_pair_old", old_source)
        self.tab_diff_pair_set_source("_edit_pair_new", new_source)

    # -- 数据收集 -----------------------------------------------------------
    @staticmethod
    def tab_diff_pair_state_to_avail(state: str):
        """把状态文本转成三态：True 有信号 / False 无信号 / None 未测。"""
        text = (state or "").strip()
        if not text:
            return None
        if M3ULE_STATUS_OK in text or M3ULE_STATUS_PARTIAL in text:
            return True
        if (M3ULE_STATUS_FAIL in text or M3ULE_STATUS_TIMEOUT in text
                or M3ULE_STATUS_ERROR in text or M3ULE_STATUS_CANCEL in text):
            return False
        return None

    def tab_diff_pair_collect(self, source: tuple, prefer_history: bool = False) -> tuple:
        """收集一侧数据。返回 (字典 {编号: 记录}, 来源描述)。

        `prefer_history=True` 时（用在「旧（以前）」一侧）优先取该链接**最早**的实测记录，
        这样即使新旧文件用的是同一批链接，也能看出「以前有信号、现在没了」。
        """
        result: dict = {}
        if not source:
            return result, "（未选择）"
        kind = source[0]

        if kind == "scan":
            table = self._main_window._tab_scan._table
            for row in range(table.rowCount()):
                number_item = table.item(row, 0)
                if number_item is None:
                    continue
                try:
                    number = int(number_item.text().strip())
                except ValueError:
                    continue
                state_item = table.item(row, 2)
                name_item = table.item(row, 7)
                url_item = table.item(row, 1)
                name = (name_item.text() if name_item else "").strip()
                if name == "待确认":
                    name = ""
                result[number] = {
                    "name": name,
                    "url": (url_item.text() if url_item else "").strip(),
                    "avail": self.tab_diff_pair_state_to_avail(
                        state_item.text() if state_item else ""),
                }
            return result, f"ID 扫描结果（{len(result)} 个编号）"

        if kind == "db":
            store = self._main_window.wnd_history_store()
            records = store.dbh_get_id_remarks() if store is not None else {}
            for key, value in records.items():
                number = m3ule_safe_int(str(key).replace("idx:", ""), -1)
                if number < 0:
                    continue
                name = (value.get("channel_name") if isinstance(value, dict) else value) or ""
                result[number] = {"name": str(name).strip(), "url": "", "avail": None}
            return result, f"数据库映射（{len(result)} 个编号）"

        if kind == "current":
            entries = self._main_window.wnd_document().entries
            label = "当前文件"
        else:
            path = source[1]
            if not os.path.isfile(path):
                raise FileNotFoundError(f"文件不存在：{path}")
            document = M3ULiveEditorDocument()
            document.doc_load_from_path(path)
            entries = document.entries
            label = f"文件 {os.path.basename(path)}"

        # 没有实测状态的条目，回落到检测缓存（同一链接历史测过的结果）
        store = self._main_window.wnd_history_store()
        cache: dict = {}
        history: dict = {}
        if store is not None and store.available:
            keys = [m3ule_probe_cache_key(entry.url or "") for entry in entries]
            keys = [key for key in keys if key]
            if keys:
                cache = store.dbh_get_probe_cache(keys)
            if prefer_history:
                history = store.dbh_probe_history_states(
                    [entry.url or "" for entry in entries], earliest=True)

        index_map = m3ule_build_index_name_map(entries)
        for entry in entries:
            number = m3ule_extract_index_from_url(entry.url or "")
            if number is None:
                title_index, _, _ = m3ule_parse_indexed_title(entry.title or "")
                number = title_index
            if number is None:
                continue
            url_key = m3ule_probe_cache_key(entry.url or "")
            hit = cache.get(url_key)
            past = history.get(url_key) if (prefer_history and url_key) else None
            avail = None
            state_from = "未测"
            state_ts = ""
            if past:
                avail = self.tab_diff_pair_state_to_avail(past.get("state", ""))
                if avail is not None:
                    state_from, state_ts = "最早历史记录", past.get("ts", "")
            if avail is None and entry.test_state:
                avail = self.tab_diff_pair_state_to_avail(entry.test_state)
                if avail is not None:
                    state_from = "本次实测"
            if avail is None and hit:
                avail = self.tab_diff_pair_state_to_avail(hit.get("state", ""))
                if avail is not None:
                    state_from, state_ts = "检测缓存（最新）", hit.get("checked_at", "")
            record = index_map.get(number, {})
            name = (record.get("name") or "").strip()
            if not name:
                # 标题里若只有 `[NNN]` 则不算名字，避免把编号当频道名
                title_index, title_name, _ = m3ule_parse_indexed_title(entry.title or "")
                name = (title_name if title_index is not None
                        else (entry.title or "").strip())
            previous = result.get(number)
            # 同一编号出现多次时，优先保留「有信号」或「有名字」的那个
            if previous is None or (previous.get("avail") is not True and avail is True) \
                    or (not previous.get("name") and name):
                result[number] = {
                    "name": name, "url": entry.url or "", "avail": avail,
                    "state_from": state_from, "state_ts": state_ts,
                }
        return result, f"{label}（{len(result)} 个编号）"

    @staticmethod
    def tab_diff_pair_classify(old_record, new_record) -> str:
        """判定某个编号的变化类型。"""
        old_exists = old_record is not None
        new_exists = new_record is not None
        if old_exists and not new_exists:
            return "仅旧有"
        if new_exists and not old_exists:
            return "仅新有"
        old_avail = old_record.get("avail")
        new_avail = new_record.get("avail")
        if old_avail is None or new_avail is None:
            if old_avail is None and new_avail is None:
                return "未测"
            # 一侧测过、另一侧没测过：按「有信号的那侧」给结论，但标注不确定
            if old_avail is True or new_avail is True:
                return "未测"
            return "仍然不可用"
        if old_avail and new_avail:
            return "仍然可用"
        if old_avail and not new_avail:
            return "新失效"
        if not old_avail and new_avail:
            return "新增可用"
        return "仍然不可用"

    @Slot()
    def tab_diff_pair_signal_changed(self, index: int) -> None:
        self._main_window.wnd_config_manager().cfg_set("diff/pair_signal_filter", int(index))
        # 选了「按信号过滤」就是想看这些编号的完整情况，别被「只看有变化」藏掉行
        if 0 <= index < len(self.M3ULE_PAIR_SIGNAL_KEYS) \
                and self.M3ULE_PAIR_SIGNAL_KEYS[index] != "all":
            checkbox = getattr(self, "_chk_pair_only_changed", None)
            if checkbox is not None and checkbox.isChecked():
                checkbox.setChecked(False)
        self.tab_diff_pair_refresh_view()

    @Slot()
    def tab_diff_pair_history_old_changed(self, checked: bool) -> None:
        """切换「旧侧用最早历史记录」；已有对比结果时立即重新收集一次。"""
        self._main_window.wnd_config_manager().cfg_set("diff/pair_history_old", bool(checked))
        if self._pair_rows:
            self.tab_diff_pair_run(notify=False)

    def tab_diff_pair_history_old_enabled(self) -> bool:
        checkbox = getattr(self, "_chk_pair_history_old", None)
        return bool(checkbox is not None and checkbox.isChecked())

    def tab_diff_pair_signal_mode(self) -> str:
        """当前信号过滤模式（返回关键字）。"""
        combo = getattr(self, "_combo_pair_signal", None)
        index = combo.currentIndex() if combo is not None else 0
        if 0 <= index < len(self.M3ULE_PAIR_SIGNAL_KEYS):
            return self.M3ULE_PAIR_SIGNAL_KEYS[index]
        return "all"

    @staticmethod
    def tab_diff_pair_signal_match(record_old, record_new, mode: str) -> bool:
        """按信号三态判断该编号是否通过过滤。"""
        if mode == "all":
            return True
        old_avail = (record_old or {}).get("avail")
        new_avail = (record_new or {}).get("avail")
        if mode == "both_alive":
            return old_avail is True and new_avail is True
        if mode == "old_alive":
            return old_avail is True
        if mode == "new_alive":
            return new_avail is True
        if mode == "missing":
            return (old_avail is True
                    and (record_new is None or new_avail is False))
        if mode == "unclear":
            return (old_avail is True and record_new is not None and new_avail is None)
        return True

    @staticmethod
    def tab_diff_pair_is_missing(record_old, record_new) -> bool:
        """「缺失」＝ 以前有信号，现在**确实**没了。

        判定条件：旧侧有信号，且（该编号在新侧已不存在，或新侧实测为无信号）。
        新侧「未测」不算缺失 —— 否则会把「还没测」误报成「失效」，见
        `tab_diff_pair_is_unclear()`。
        """
        if (record_old or {}).get("avail") is not True:
            return False
        if record_new is None:
            return True
        return record_new.get("avail") is False

    @staticmethod
    def tab_diff_pair_is_unclear(record_old, record_new) -> bool:
        """「待确认」＝ 以前有信号，新侧存在但还没测过（既不能说没了，也不能说还在）。"""
        return ((record_old or {}).get("avail") is True
                and record_new is not None
                and record_new.get("avail") is None)

    @Slot()
    def tab_diff_pair_run(self, notify: bool = True) -> int:
        self._pair_progress.setValue(5)
        self._lbl_pair_summary.setText("正在收集两侧数据…")
        QApplication.processEvents()
        try:
            use_history = self.tab_diff_pair_history_old_enabled()
            old_map, old_label = self.tab_diff_pair_collect(
                self._pair_old, prefer_history=use_history)
            if use_history:
                old_label += "·旧侧取最早历史记录"
            self._pair_progress.setValue(45)
            QApplication.processEvents()
            new_map, new_label = self.tab_diff_pair_collect(self._pair_new)
        except Exception as exc:  # noqa: BLE001
            self._pair_progress.setValue(0)
            self._lbl_pair_summary.setText("收集失败")
            if notify:
                QMessageBox.warning(self, "对比失败", f"{type(exc).__name__}: {exc}")
            else:
                self._main_window.wnd_append_log(f"编号双列对比失败：{exc}")
            return -1
        if not old_map and not new_map:
            self._pair_progress.setValue(0)
            self._lbl_pair_summary.setText("两侧都没有数据，无法对比")
            if notify:
                QMessageBox.information(
                    self, "提示",
                    "两侧都没有取到编号数据。\n\n"
                    "· 选文件：文件里要有编号（标题里的 [000] 或链接里的 se_idx=000）\n"
                    "· 选 ID 扫描结果：需要先在「ID 扫描」页扫过\n"
                    "· 选当前文件：需要先打开一个文件\n"
                    "· 选数据库映射：需要有保存过的编号映射")
            return 0

        self._pair_progress.setValue(70)
        numbers = sorted(set(old_map) | set(new_map))
        rows: list = []
        for number in numbers:
            old_record = old_map.get(number)
            new_record = new_map.get(number)
            change = self.tab_diff_pair_classify(old_record, new_record)
            rows.append({
                "number": number,
                "old": old_record,
                "new": new_record,
                "change": change,
                "missing": self.tab_diff_pair_is_missing(old_record, new_record),
                "unclear": self.tab_diff_pair_is_unclear(old_record, new_record),
            })
        self._pair_rows = rows
        self._pair_progress.setValue(100)
        self.tab_diff_pair_refresh_view()

        counts = {}
        for row in rows:
            counts[row["change"]] = counts.get(row["change"], 0) + 1
        # 信号维度统计：只看真正在用的编号，回答「有没有缺失」
        old_alive = sum(1 for row in rows if (row["old"] or {}).get("avail") is True)
        new_alive = sum(1 for row in rows if (row["new"] or {}).get("avail") is True)
        both_alive = sum(1 for row in rows
                         if (row["old"] or {}).get("avail") is True
                         and (row["new"] or {}).get("avail") is True)
        missing = sum(1 for row in rows if row["missing"])
        unclear = sum(1 for row in rows if row["unclear"])
        gained = sum(1 for row in rows
                     if (row["old"] or {}).get("avail") is not True
                     and (row["new"] or {}).get("avail") is True)
        self._pair_signal_stats = {
            "old_alive": old_alive, "new_alive": new_alive, "both_alive": both_alive,
            "missing": missing, "unclear": unclear, "gained": gained,
        }
        # 旧侧状态从哪来，决定「无缺失」这个结论可信不可信（旧侧没有该编号的不计）
        old_sources: dict = {}
        for row in rows:
            if row["old"] is None:
                continue
            source = row["old"].get("state_from") or "未测"
            old_sources[source] = old_sources.get(source, 0) + 1
        self._pair_old_sources = old_sources
        summary = (
            f"旧：{old_label} · 新：{new_label} · 共 {len(rows)} 个编号 · "
            f"旧侧有信号 {old_alive} → 现在仍可用 {both_alive}"
            + (f" · ★缺失 {missing}" if missing else " · 无缺失")
            + (f" · ❓待确认 {unclear}" if unclear else "")
            + (f" · 新增可用 {gained}" if gained else "")
            + f" · 仅旧有 {counts.get('仅旧有', 0)} · 仅新有 {counts.get('仅新有', 0)}"
            + " · 旧侧状态来源 " + " / ".join(
                f"{name} {count}" for name, count in
                sorted(old_sources.items(), key=lambda item: -item[1])))
        self._lbl_pair_summary.setText(summary)
        self._main_window.wnd_append_log(
            "编号双列对比完成：" + summary.replace(" · ", "，"))
        return len(rows)

    @staticmethod
    def tab_diff_pair_cell(record) -> str:
        """把一侧的记录渲染成单元格文本。"""
        if record is None:
            return "— 不存在"
        name = (record.get("name") or "").strip()
        avail = record.get("avail")
        if avail is True:
            icon = M3ULE_TEST_STATE_ICON_MAP.get(M3ULE_STATUS_OK, "🟢")
            state_text = "有信号"
        elif avail is False:
            icon = M3ULE_TEST_STATE_ICON_MAP.get(M3ULE_STATUS_FAIL, "🔴")
            state_text = "无信号"
        else:
            icon = "⚪"
            state_text = "未测"
        return f"{icon} {name or '（未命名）'} · {state_text}"

    @staticmethod
    def tab_diff_pair_cell_tooltip(record) -> str:
        """说明这一格的状态从哪来（实测 / 检测缓存 / 最早历史记录）与时间。"""
        if record is None:
            return "该编号在这一侧不存在"
        lines = []
        if record.get("url"):
            lines.append(record["url"])
        source = record.get("state_from") or ""
        stamp = record.get("state_ts") or ""
        if source:
            lines.append("状态来源：" + source + (f"（{stamp}）" if stamp else ""))
        return "\n".join(lines)

    def tab_diff_pair_refresh_view(self) -> None:
        only_changed = bool(getattr(self, "_chk_pair_only_changed", None)
                            and self._chk_pair_only_changed.isChecked())
        signal_mode = self.tab_diff_pair_signal_mode()
        visible = []
        for row in self._pair_rows:
            if not self.tab_diff_pair_signal_match(row["old"], row["new"], signal_mode):
                continue
            if only_changed and row["change"] in ("仍然可用", "仍然不可用"):
                continue
            visible.append(row)
        self._pair_table.setSortingEnabled(False)
        self._pair_table.setRowCount(0)
        for row in visible:
            position = self._pair_table.rowCount()
            self._pair_table.insertRow(position)
            old_record = row["old"]
            new_record = row["new"]
            values = [
                str(row["number"]),
                self.tab_diff_pair_cell(old_record),
                self.tab_diff_pair_cell(new_record),
                ("★缺失 · " if row["missing"] else "")
                + ("❓待确认 · " if row.get("unclear") else "") + row["change"],
                (old_record or {}).get("url", ""),
                (new_record or {}).get("url", ""),
            ]
            for column, text in enumerate(values):
                item = QTableWidgetItem(text)
                if column in (0, 3):
                    item.setTextAlignment(Qt.AlignCenter)
                if column == 3:
                    color = self.M3ULE_PAIR_CHANGE_COLORS.get(row["change"])
                    if row.get("unclear"):
                        color = self.M3ULE_PAIR_UNCLEAR_COLOR
                    if color is not None:
                        item.setForeground(QBrush(color))
                    font = item.font()
                    if row["missing"] or row["change"] in ("新增可用", "新失效"):
                        font.setBold(True)
                    item.setFont(font)
                if row["missing"] and column in (1, 2):
                    background = M3ULE_TEST_STATE_BG.get(M3ULE_STATUS_FAIL)
                    if background is not None:
                        item.setBackground(QBrush(background))
                if row.get("unclear") and column == 2:
                    background = M3ULE_TEST_STATE_BG.get(M3ULE_STATUS_TIMEOUT)
                    if background is not None:
                        item.setBackground(QBrush(background))
                if column in (1, 2):
                    source_record = old_record if column == 1 else new_record
                    item.setToolTip(self.tab_diff_pair_cell_tooltip(source_record))
                self._pair_table.setItem(position, column, item)
        self._pair_table.setSortingEnabled(True)
        if signal_mode != "all" or only_changed:
            label = self.M3ULE_PAIR_SIGNAL_FILTERS[
                self.M3ULE_PAIR_SIGNAL_KEYS.index(signal_mode)] if signal_mode != "all" else ""
            stats = getattr(self, "_pair_signal_stats", {})
            extra = ""
            if stats:
                extra = (f" · 过滤后 {len(visible)} 行"
                         f"（旧有信号 {stats.get('old_alive', 0)} · "
                         f"缺失 {stats.get('missing', 0)}"
                         + (f" · 待确认 {stats.get('unclear', 0)}"
                            if stats.get('unclear') else "")
                         + "）")
            if label:
                extra = f"[{label}]" + extra
            else:
                extra = f"[只看有变化]{extra}"
            self._lbl_pair_filter_hint.setText(extra)
        else:
            self._lbl_pair_filter_hint.setText("")

    @Slot()
    def tab_diff_pair_export_csv(self) -> None:
        if not self._pair_rows:
            QMessageBox.information(self, "提示", "还没有对比结果可导出。")
            return
        last_dir = self._main_window.wnd_config_manager().cfg_get("io/last_save_dir")
        path, _ = QFileDialog.getSaveFileName(
            self, "导出编号双列对比 CSV",
            os.path.join(last_dir, "编号双列对比.csv"), "CSV 文件 (*.csv)")
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8-sig", newline="") as handle:
                writer = csv.writer(handle)
                writer.writerow(["编号", "旧频道名", "旧状态", "旧状态来源", "新频道名", "新状态",
                                 "新状态来源", "变化", "是否缺失", "是否待确认",
                                 "旧链接", "新链接"])
                for row in self._pair_rows:
                    old_record = row["old"] or {}
                    new_record = row["new"] or {}
                    writer.writerow([
                        row["number"],
                        old_record.get("name", "") if row["old"] else "（不存在）",
                        self.tab_diff_pair_avail_text(row["old"]),
                        self.tab_diff_pair_source_text(row["old"]),
                        new_record.get("name", "") if row["new"] else "（不存在）",
                        self.tab_diff_pair_avail_text(row["new"]),
                        self.tab_diff_pair_source_text(row["new"]),
                        row["change"],
                        "是" if row.get("missing") else "",
                        "是" if row.get("unclear") else "",
                        old_record.get("url", ""),
                        new_record.get("url", ""),
                    ])
        except OSError as exc:
            QMessageBox.warning(self, "导出失败", str(exc))
            return
        self._main_window.wnd_config_manager().cfg_set("io/last_save_dir", os.path.dirname(path))
        self._main_window.wnd_append_log(f"已导出编号双列对比：{path}")
        QMessageBox.information(self, "完成", f"已导出到：\n{path}")

    @staticmethod
    def tab_diff_pair_avail_text(record) -> str:
        if record is None:
            return "（不存在）"
        avail = record.get("avail")
        if avail is True:
            return "有信号"
        if avail is False:
            return "无信号"
        return "未测"

    @staticmethod
    def tab_diff_pair_source_text(record) -> str:
        """该侧状态的来源（含时间），便于事后核对结论。"""
        if record is None:
            return ""
        source = record.get("state_from") or ""
        stamp = record.get("state_ts") or ""
        if source and stamp:
            return f"{source} {stamp}"
        return source

    # -- 文件选择 -----------------------------------------------------------
    @Slot()
    def tab_diff_browse(self, target_attr: str) -> None:
        default_dir = self._main_window.wnd_config_manager().cfg_get("io/last_open_dir")
        path, _ = QFileDialog.getOpenFileName(
            self, "选择 M3U 文件", default_dir, "播放列表 (*.m3u *.m3u8 *.txt);;所有文件 (*.*)")
        if not path:
            return
        getattr(self, target_attr).setText(path)
        self._main_window.wnd_config_manager().cfg_set("io/last_open_dir", os.path.dirname(path))

    @Slot()
    def tab_diff_use_current(self) -> None:
        path = self._main_window.wnd_current_path()
        if not path:
            QMessageBox.information(self, "提示", "当前没有已保存路径的文件，请先保存。")
            return
        self._edit_path_a.setText(path)

    @Slot()
    def tab_diff_swap(self) -> None:
        a, b = self._edit_path_a.text(), self._edit_path_b.text()
        self._edit_path_a.setText(b)
        self._edit_path_b.setText(a)

    # -- 对比 ---------------------------------------------------------------
    @staticmethod
    def tab_diff_extract_index(url: str) -> str:
        match = re.search(r"(?:idx|index|id)=(?P<num>\d+)", url or "", re.IGNORECASE)
        return match.group("num") if match else ""

    @staticmethod
    def tab_diff_key(entry) -> str:
        tvg_id = entry.entry_get_attr("tvg-id").strip()
        if tvg_id:
            return f"id:{tvg_id}"
        channel_id = entry.entry_get_attr("channelID").strip()
        if channel_id:
            return f"cid:{channel_id}"
        name = entry.entry_effective_name().strip()
        return f"name:{name}"

    @Slot()
    def tab_diff_run(self) -> None:
        path_a = self._edit_path_a.text().strip()
        path_b = self._edit_path_b.text().strip()
        if not path_a or not path_b:
            QMessageBox.warning(self, "提示", "请先选择文件 A 与文件 B。")
            return
        if not os.path.isfile(path_a) or not os.path.isfile(path_b):
            QMessageBox.warning(self, "提示", "所选文件不存在。")
            return
        self._progress.setValue(10)
        self._lbl_summary.setText("正在解析文件…")
        QApplication.processEvents()
        try:
            document_a = M3ULiveEditorDocument()
            document_a.doc_load_from_path(path_a)
            self._progress.setValue(45)
            document_b = M3ULiveEditorDocument()
            document_b.doc_load_from_path(path_b)
        except Exception as exc:  # noqa: BLE001
            QMessageBox.warning(self, "解析失败", f"{type(exc).__name__}: {exc}")
            self._progress.setValue(0)
            return
        self._progress.setValue(60)
        self._lbl_summary.setText("正在比对…")
        QApplication.processEvents()

        index_a: dict = {}
        for entry in document_a.entries:
            index_a.setdefault(self.tab_diff_key(entry), entry)
        index_b: dict = {}
        for entry in document_b.entries:
            index_b.setdefault(self.tab_diff_key(entry), entry)

        rows: list = []
        all_keys = list(index_a.keys()) + [key for key in index_b.keys() if key not in index_a]
        total = max(1, len(all_keys))
        for position, key in enumerate(all_keys):
            entry_a = index_a.get(key)
            entry_b = index_b.get(key)
            if entry_a is not None and entry_b is None:
                rows.append(self._build_diff_row("仅A(缺失)", entry_a, None, "文件 B 中未找到该频道"))
            elif entry_a is None and entry_b is not None:
                rows.append(self._build_diff_row("仅B(新增)", None, entry_b, "文件 B 中新增的频道"))
            else:
                rows.append(self._diff_compare_entries(entry_a, entry_b))
            if position % 200 == 0:
                self._progress.setValue(60 + int(position * 40 / total))
        self._diff_rows = rows
        self._progress.setValue(100)
        self.tab_diff_refresh_view()
        changed = sum(1 for row in rows if row["type"] not in ("相同",))
        self._lbl_summary.setText(
            f"A {len(document_a.entries)} 条 · B {len(document_b.entries)} 条 · 差异 {changed} 条")
        self._main_window.wnd_append_log(
            f"对比完成：A {len(document_a.entries)} 条，B {len(document_b.entries)} 条，差异 {changed} 条。")

    def _build_diff_row(self, type_text: str, entry_a, entry_b, note: str) -> dict:
        entry = entry_a if entry_a is not None else entry_b
        return {
            "type": type_text,
            "name": entry.entry_effective_name() if entry else "",
            "key": self.tab_diff_key(entry) if entry else "",
            "chno_a": entry_a.entry_get_attr("tvg-chno") if entry_a else "",
            "chno_b": entry_b.entry_get_attr("tvg-chno") if entry_b else "",
            "idx_a": self.tab_diff_extract_index(entry_a.url if entry_a else ""),
            "idx_b": self.tab_diff_extract_index(entry_b.url if entry_b else ""),
            "url_a": entry_a.url if entry_a else "",
            "url_b": entry_b.url if entry_b else "",
            "note": note,
        }

    def _diff_compare_entries(self, entry_a, entry_b) -> dict:
        idx_a = self.tab_diff_extract_index(entry_a.url or "")
        idx_b = self.tab_diff_extract_index(entry_b.url or "")
        chno_a = entry_a.entry_get_attr("tvg-chno")
        chno_b = entry_b.entry_get_attr("tvg-chno")
        name_a = entry_a.entry_effective_name()
        name_b = entry_b.entry_effective_name()
        notes: list = []
        if idx_a and idx_b and idx_a != idx_b:
            notes.append(f"流编号 {idx_a} → {idx_b}")
        if chno_a != chno_b:
            notes.append(f"频道号 {chno_a or '空'} → {chno_b or '空'}")
        if name_a != name_b:
            notes.append(f"名称 {name_a} → {name_b}")
        if (entry_a.url or "") != (entry_b.url or ""):
            notes.append("链接不同")
        if notes:
            if idx_a and idx_b and idx_a != idx_b:
                type_text = "编号变化"
            elif name_a != name_b:
                type_text = "名称变化"
            elif chno_a != chno_b:
                type_text = "频道号变化"
            else:
                type_text = "链接变化"
        else:
            type_text = "相同"
        return {
            "type": type_text,
            "name": name_b or name_a,
            "key": self.tab_diff_key(entry_b),
            "chno_a": chno_a, "chno_b": chno_b,
            "idx_a": idx_a, "idx_b": idx_b,
            "url_a": entry_a.url or "", "url_b": entry_b.url or "",
            "note": "；".join(notes),
        }

    @Slot()
    def tab_diff_refresh_view(self) -> None:
        only_diff = self._chk_only_diff.isChecked()
        visible = [row for row in self._diff_rows if (not only_diff) or row["type"] != "相同"]
        self._table.setRowCount(len(visible))
        for row_index, row in enumerate(visible):
            values = [row["type"], row["name"], row["key"], row["chno_a"], row["chno_b"],
                      row["idx_a"], row["idx_b"], row["url_a"], row["url_b"], row["note"]]
            for column, value in enumerate(values):
                item = QTableWidgetItem("" if value is None else str(value))
                item.setFlags(Qt.ItemIsEnabled | Qt.ItemIsSelectable)
                if column == 0:
                    color_map = {
                        "相同": "#137333", "仅A(缺失)": "#c5221f", "仅B(新增)": "#1a73e8",
                        "编号变化": "#c05621", "名称变化": "#9a6b00",
                        "频道号变化": "#9a6b00", "链接变化": "#5f6368",
                    }
                    color = color_map.get(row["type"])
                    if color:
                        item.setForeground(QBrush(QColor(color)))
                if column in (7, 8) and row["type"] in ("编号变化", "链接变化"):
                    item.setBackground(QBrush(QColor("#fef7e0")))
                self._table.setItem(row_index, column, item)

    @Slot()
    def tab_diff_export_csv(self) -> None:
        if not self._diff_rows:
            QMessageBox.information(self, "提示", "没有可导出的对比结果。")
            return
        default_dir = self._main_window.wnd_config_manager().cfg_get("io/last_save_dir")
        path, _ = QFileDialog.getSaveFileName(
            self, "导出对比结果", os.path.join(default_dir, "对比结果.csv"), "CSV 文件 (*.csv)")
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8-sig", newline="") as handle:
                writer = csv.writer(handle)
                writer.writerow(self.M3ULE_DIFF_COLUMNS)
                for row in self._diff_rows:
                    writer.writerow([row["type"], row["name"], row["key"], row["chno_a"], row["chno_b"],
                                     row["idx_a"], row["idx_b"], row["url_a"], row["url_b"], row["note"]])
        except OSError as exc:
            QMessageBox.warning(self, "导出失败", str(exc))
            return
        self._main_window.wnd_config_manager().cfg_set("io/last_save_dir", os.path.dirname(path))
        self._main_window.wnd_append_log(f"对比结果已导出：{path}")

    @Slot()
    def tab_diff_apply_to_current(self) -> None:
        if not self._diff_rows:
            QMessageBox.information(self, "提示", "请先执行对比。")
            return
        document = self._main_window.wnd_document_model().mdl_document()
        if not document.entries:
            QMessageBox.information(self, "提示", "当前没有打开的文件。")
            return
        reply = QMessageBox.question(
            self, "确认",
            "将按匹配键把文件 B 的“链接 / 频道号 / 名称”更新到当前文件，是否继续？\n"
            "（建议先保存或备份当前文件）",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if reply != QMessageBox.Yes:
            return
        update_map = {}
        for row in self._diff_rows:
            if row["type"] in ("相同", "仅A(缺失)"):
                continue
            if not row["key"] or not row["url_b"]:
                continue
            update_map[row["key"]] = row
        changed = 0
        for entry in document.entries:
            row = update_map.get(self.tab_diff_key(entry))
            if not row:
                continue
            if row["url_b"] and (entry.url or "") != row["url_b"]:
                entry.url = row["url_b"]
                changed += 1
            if row["chno_b"] and entry.entry_get_attr("tvg-chno") != row["chno_b"]:
                entry.entry_set_attr("tvg-chno", row["chno_b"])
                changed += 1
            if row["name"] and entry.title != row["name"]:
                entry.title = row["name"]
                entry.entry_rebuild_extinf_line()
                changed += 1
        if changed:
            document.modified = True
            self._main_window.wnd_document_model().mdl_refresh_all()
            self._main_window.wnd_mark_modified()
        self._main_window.wnd_append_log(f"已应用对比结果，更新 {changed} 处字段。")
        QMessageBox.information(self, "完成", f"已更新 {changed} 处字段。")


# ----------------------------------------------------------------------------
# 设置页
# ----------------------------------------------------------------------------

class M3ULiveEditorSettingsTab(QWidget):
    """全部设置的界面（按用途分成多个设置分类页，避免一长条堆在一起）。

    任何改动都会立即持久化保存；当前打开的设置分类也会记住（`ui/settings_category`）。
    """

    M3ULE_SETTINGS_CATEGORY_KEY = "ui/settings_category"

    def __init__(self, main_window, parent=None):
        super().__init__(parent)
        self._main_window = main_window
        self._building = True
        self._build_ui()
        self._building = False
        self.stt_reload_from_config()

    # -- 构建界面 -----------------------------------------------------------
    def _build_ui(self) -> None:
        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        self._category_tabs = QTabWidget()
        self._category_tabs.setDocumentMode(True)
        outer.addWidget(self._category_tabs)

        categories = (
            ("链接测试", (self.stt_build_probe_group, self.stt_build_cache_group)),
            ("播放", (self.stt_build_player_group, self.stt_build_html5_group)),
            ("文件与备份", (self.stt_build_io_group,)),
            ("界面", (self.stt_build_ui_group,)),
            ("密钥与环境", (self.stt_build_env_group,)),
            ("维护与关于", (self.stt_build_maintenance_group, self.stt_build_about_group)),
        )
        for title, builders in categories:
            page = self.stt_build_category_page(tuple(builder() for builder in builders))
            self._category_tabs.addTab(page, title)
        self._category_tabs.currentChanged.connect(self.stt_on_category_changed)

    def stt_build_category_page(self, groups: tuple) -> QWidget:
        """把一个或多个设置分组装进带滚动条的分类页（各页独立滚动，互不影响）。"""
        page = QWidget()
        outer = QVBoxLayout(page)
        outer.setContentsMargins(0, 0, 0, 0)
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.NoFrame)
        outer.addWidget(scroll)

        container = QWidget()
        scroll.setWidget(container)
        layout = QVBoxLayout(container)
        layout.setContentsMargins(8, 8, 8, 8)
        layout.setSpacing(6)
        for group in groups:
            layout.addWidget(group)
        layout.addStretch(1)
        return page

    def stt_category_names(self) -> list:
        """设置分类名称（供自动化测试检查分页结构）。"""
        return [self._category_tabs.tabText(index)
                for index in range(self._category_tabs.count())]

    def stt_select_category(self, name: str, persist: bool = True) -> bool:
        """按名称切换到某个设置分类（persist=False 供测试使用，避免污染设置）。"""
        for index in range(self._category_tabs.count()):
            if self._category_tabs.tabText(index) == name:
                self._category_tabs.setCurrentIndex(index)
                if not persist:
                    self._category_tabs.blockSignals(True)
                    self._category_tabs.setCurrentIndex(index)
                    self._category_tabs.blockSignals(False)
                return True
        return False

    @Slot(int)
    def stt_on_category_changed(self, index: int) -> None:
        if self._building:
            return
        self._main_window.wnd_config_manager().cfg_set(
            self.M3ULE_SETTINGS_CATEGORY_KEY, int(index))

    def stt_build_probe_group(self) -> QGroupBox:
        box = QGroupBox("链接测试设置")
        grid = QGridLayout(box)
        grid.setHorizontalSpacing(8)
        grid.setVerticalSpacing(4)

        self._spin_probe_workers = QSpinBox()
        self._spin_probe_workers.setRange(1, 64)
        grid.addWidget(QLabel("并发线程："), 0, 0)
        grid.addWidget(self._spin_probe_workers, 0, 1)

        self._spin_probe_timeout = QDoubleSpinBox()
        self._spin_probe_timeout.setRange(0.5, 300.0)
        self._spin_probe_timeout.setSingleStep(0.5)
        grid.addWidget(QLabel("超时(秒)："), 0, 2)
        grid.addWidget(self._spin_probe_timeout, 0, 3)

        self._spin_probe_retries = QSpinBox()
        self._spin_probe_retries.setRange(0, 5)
        grid.addWidget(QLabel("重试次数："), 0, 4)
        grid.addWidget(self._spin_probe_retries, 0, 5)

        self._chk_probe_deep = QCheckBox("默认深度测试（下载首个分片，判断是否有节目）")
        grid.addWidget(self._chk_probe_deep, 1, 0, 1, 4)
        self._chk_probe_ignore_ssl = QCheckBox("忽略 SSL 证书错误")
        grid.addWidget(self._chk_probe_ignore_ssl, 1, 4, 1, 3)

        grid.addWidget(QLabel("User-Agent："), 2, 0)
        self._edit_probe_ua = QLineEdit()
        grid.addWidget(self._edit_probe_ua, 2, 1, 1, 6)
        self._btn_reset_ua = QPushButton("恢复默认")
        self._btn_reset_ua.clicked.connect(
            lambda: self._edit_probe_ua.setText(M3ULE_DEFAULT_USER_AGENT))
        grid.addWidget(self._btn_reset_ua, 2, 7)

        grid.addWidget(QLabel("代理地址："), 3, 0)
        self._edit_probe_proxy = QLineEdit()
        self._edit_probe_proxy.setPlaceholderText("如 http://127.0.0.1:7890（留空表示不使用代理）")
        grid.addWidget(self._edit_probe_proxy, 3, 1, 1, 7)
        grid.setColumnStretch(8, 1)

        for widget in (self._spin_probe_workers, self._spin_probe_timeout, self._spin_probe_retries):
            widget.valueChanged.connect(self.stt_on_changed)
        for widget in (self._chk_probe_deep, self._chk_probe_ignore_ssl):
            widget.toggled.connect(self.stt_on_changed)
        self._edit_probe_ua.editingFinished.connect(self.stt_on_changed)
        self._edit_probe_proxy.editingFinished.connect(self.stt_on_changed)
        return box

    def stt_build_cache_group(self) -> QGroupBox:
        box = QGroupBox("检测缓存（已测过的链接不重复检测）")
        grid = QGridLayout(box)
        grid.setHorizontalSpacing(8)
        grid.setVerticalSpacing(4)

        self._chk_cache_enabled = QCheckBox(
            "启用检测缓存：保存每次检测结果，下次打开同一链接时直接复用")
        self._chk_cache_enabled.setToolTip(
            "检测结果按链接保存在本地数据库，程序重启后依然有效。")
        self._chk_cache_enabled.toggled.connect(self.stt_on_changed)
        grid.addWidget(self._chk_cache_enabled, 0, 0, 1, 6)

        self._chk_cache_auto_apply = QCheckBox("打开文件后自动套用缓存中的检测结果")
        self._chk_cache_auto_apply.toggled.connect(self.stt_on_changed)
        grid.addWidget(self._chk_cache_auto_apply, 1, 0, 1, 6)

        self._chk_cache_skip_fresh = QCheckBox("测试时跳过缓存有效期内已检测的链接")
        self._chk_cache_skip_fresh.toggled.connect(self.stt_on_changed)
        grid.addWidget(self._chk_cache_skip_fresh, 2, 0, 1, 6)

        grid.addWidget(QLabel("检测缓存有效期："), 3, 0)
        self._spin_cache_ttl = QSpinBox()
        self._spin_cache_ttl.setRange(0, 8760)
        self._spin_cache_ttl.setSuffix(" 小时")
        self._spin_cache_ttl.setSpecialValueText("永久有效")
        self._spin_cache_ttl.setToolTip(
            "0 表示永久有效。超出有效期的缓存仍会显示（标注检测时间），"
            "但再次测试时会重新检测。")
        self._spin_cache_ttl.valueChanged.connect(self.stt_on_changed)
        grid.addWidget(self._spin_cache_ttl, 3, 1)

        btn_apply = QPushButton("立即套用缓存")
        btn_apply.setToolTip("把已保存的检测结果套用到当前打开的文件")
        btn_apply.clicked.connect(self._main_window.wnd_act_apply_probe_cache)
        grid.addWidget(btn_apply, 3, 2)
        btn_prune = QPushButton("清理过期缓存")
        btn_prune.clicked.connect(self._main_window.wnd_act_prune_probe_cache)
        grid.addWidget(btn_prune, 3, 3)
        btn_clear = QPushButton("清空检测缓存")
        btn_clear.clicked.connect(self._main_window.wnd_act_clear_probe_cache)
        grid.addWidget(btn_clear, 3, 4)

        self._lbl_cache_stats = QLabel("检测缓存：—")
        self._lbl_cache_stats.setStyleSheet("color:#5f6368;")
        self._lbl_cache_stats.setTextInteractionFlags(Qt.TextSelectableByMouse)
        grid.addWidget(self._lbl_cache_stats, 4, 0, 1, 6)
        grid.setColumnStretch(6, 1)
        return box

    def stt_build_player_group(self) -> QGroupBox:
        box = QGroupBox("播放器设置（用于验证“现在是哪个台”）")
        row = QHBoxLayout(box)
        self._edit_player_path = QLineEdit()
        self._edit_player_path.setPlaceholderText("例如 C:\\Program Files\\VideoLAN\\VLC\\vlc.exe（留空则用系统默认程序打开）")
        row.addWidget(self._edit_player_path, 1)
        btn_browse = QPushButton("浏览…")
        btn_browse.clicked.connect(self.stt_browse_player)
        row.addWidget(btn_browse)
        btn_test = QPushButton("测试打开")
        btn_test.clicked.connect(self.stt_test_player)
        row.addWidget(btn_test)
        self._edit_player_path.editingFinished.connect(self.stt_on_changed)
        return box

    def stt_build_html5_group(self) -> QGroupBox:
        box = QGroupBox("弹窗播放（FFmpeg / VLC）")
        grid = QGridLayout(box)
        grid.setHorizontalSpacing(8)
        grid.setVerticalSpacing(4)

        grid.addWidget(QLabel("播放方式："), 0, 0)
        self._combo_html5_mode = QComboBox()
        self._combo_html5_mode.addItems(["内嵌窗口", "系统浏览器"])
        grid.addWidget(self._combo_html5_mode, 0, 1)
        self._chk_html5_autoplay = QCheckBox("打开后自动播放")
        grid.addWidget(self._chk_html5_autoplay, 0, 2)
        self._chk_html5_local_hls = QCheckBox("优先使用本地 hls.min.js（离线可用）")
        grid.addWidget(self._chk_html5_local_hls, 0, 3, 1, 3)

        self._lbl_html5_engine = QLabel("")
        self._lbl_html5_engine.setWordWrap(True)
        grid.addWidget(self._lbl_html5_engine, 2, 0, 1, 6)

        grid.addWidget(QLabel("播放内核："), 3, 0)
        self._combo_player_backend = QComboBox()
        self._combo_player_backend.setMinimumWidth(180)
        self._combo_player_backend.setToolTip(
            "内嵌弹窗只有两个内核（默认 FFmpeg）：\n"
            "· FFmpeg（内嵌 Qt 多媒体）：PySide6 自带的 FFmpeg 解码，直连拉流，不需要额外安装；\n"
            "· VLC（libvlc）：兼容性最好，需要本机已安装 VLC，并 pip install python-vlc；\n"
            "当前内核打不开画面时会自动换用另一个可用内核。")
        grid.addWidget(self._combo_player_backend, 3, 1)
        btn_backend_test = QPushButton("内核检查")
        btn_backend_test.setToolTip("检查本机各播放内核是否可用（未安装的会给出安装指引）")
        btn_backend_test.clicked.connect(self.stt_show_player_backend_report)
        grid.addWidget(btn_backend_test, 3, 2)
        self._lbl_player_backend_state = QLabel("")
        self._lbl_player_backend_state.setWordWrap(True)
        grid.addWidget(self._lbl_player_backend_state, 4, 0, 1, 7)

        self._lbl_libvlc_caption = QLabel("libvlc 路径：")
        grid.addWidget(self._lbl_libvlc_caption, 8, 0)
        self._edit_libvlc_path = QLineEdit()
        self._edit_libvlc_path.setPlaceholderText("libvlc.dll 的位置（留空＝自动查找）")
        self._edit_libvlc_path.setToolTip(
            "VLC 内核需要已安装的 VLC 与 python-vlc；VLC 不在默认目录时在这里指定 libvlc.dll。")
        grid.addWidget(self._edit_libvlc_path, 8, 1, 1, 4)
        self._btn_libvlc_browse = QPushButton("浏览…")
        self._btn_libvlc_browse.setToolTip("选择 libvlc.dll")
        self._btn_libvlc_browse.clicked.connect(lambda: self.stt_browse_player_library("vlc"))
        grid.addWidget(self._btn_libvlc_browse, 8, 5)
        self._btn_libvlc_clear = QPushButton("清除")
        self._btn_libvlc_clear.setToolTip("清除后恢复为自动查找")
        self._btn_libvlc_clear.clicked.connect(lambda: self.stt_clear_player_library("vlc"))
        grid.addWidget(self._btn_libvlc_clear, 8, 6)

        button_row = QHBoxLayout()
        btn_check = QPushButton("检查播放环境")
        btn_check.clicked.connect(self.stt_show_html5_status)
        button_row.addWidget(btn_check)
        btn_test = QPushButton("测试播放选中条目")
        btn_test.setToolTip("用当前选中的频道打开播放弹窗")
        btn_test.clicked.connect(self.stt_test_html5_playback)
        button_row.addWidget(btn_test)
        button_row.addStretch(1)
        grid.addLayout(button_row, 5, 0, 1, 7)

        hint = QLabel(
            "说明：内嵌播放只有 <b>FFmpeg</b>（Qt 多媒体，PySide6 自带）与 <b>VLC</b>（libvlc）两个内核，"
            "都<b>直连拉流</b>；当前内核打不开画面时自动换另一个可用内核。"
            "“系统浏览器”方式会把播放页交给 Chrome/Edge，地址经本机 <code>127.0.0.1</code> 回环中转"
            "（用于解决跨域与混合内容限制，并可改写 m3u8 内的分片地址），仅在程序运行期间有效。")
        hint.setWordWrap(True)
        hint.setStyleSheet("color:#5f6368;")
        grid.addWidget(hint, 6, 0, 1, 7)
        grid.setColumnStretch(1, 1)

        self._combo_html5_mode.currentIndexChanged.connect(self.stt_on_changed)
        self._chk_html5_autoplay.toggled.connect(self.stt_on_changed)
        self._chk_html5_local_hls.toggled.connect(self.stt_on_changed)
        self._combo_player_backend.currentIndexChanged.connect(self.stt_on_changed)
        self._edit_libvlc_path.editingFinished.connect(
            lambda: self.stt_apply_player_library("vlc", self._edit_libvlc_path.text()))
        return box

    @Slot()
    def stt_restart_application(self) -> None:
        self._main_window.wnd_restart_application()

    @Slot()
    def stt_show_player_backend_report(self) -> None:
        QMessageBox.information(self, "播放内核检查", m3ule_player_backend_report_text())

    def stt_browse_player_library(self, key: str) -> None:
        """选择第三方内核的库文件（libvlc.dll）并立即生效。"""
        names = m3ule_player_backend_library_names(key)
        start_dir = os.path.dirname(self._edit_libvlc_path.text().strip()
                                   or m3ule_get_program_dir())
        path, _ = QFileDialog.getOpenFileName(
            self, f"选择 {m3ule_player_backend_label(key)} 的库文件",
            start_dir, "库文件 (%s);;所有文件 (*)" % " ".join(names))
        if not path:
            return
        if m3ule_player_backend_set_library(key, path):
            self.stt_refresh_player_backend_label()
            self.stt_reload_from_config()
            QMessageBox.information(
                self, "已启用",
                f"{m3ule_player_backend_label(key)} 内核现在可用了：\n{path}\n\n"
                "播放弹窗里选它（或保持「自动」）即可用这个内核播放。")
        else:
            QMessageBox.warning(
                self, "仍然不可用",
                m3ule_player_backend_status(key)[1] + "\n\n" + m3ule_player_backend_library_hint(key))

    def stt_clear_player_library(self, key: str) -> None:
        """清除手动指定的库文件路径，恢复自动查找。"""
        if m3ule_player_backend_set_library(key, ""):
            pass
        self.stt_reload_from_config()
        self.stt_refresh_player_backend_label()
        self._main_window.wnd_append_log(
            f"已清除 {m3ule_player_backend_label(key)} 的库文件路径，改为自动查找。")

    @Slot()
    def stt_show_html5_status(self) -> None:
        relay = self._main_window.wnd_relay_server()
        local_js = relay.relay_local_hlsjs_path()
        lines = [
            f"内嵌播放内核（只有两个）：{'、'.join(M3ULE_PLAYER_BACKENDS)}",
            f"默认内核：{M3ULE_PLAYER_BACKEND_LABELS[M3ULE_PLAYER_BACKEND_DEFAULT]}",
        ]
        for _key, label, ok, reason in m3ule_player_backend_report():
            lines.append(f"  {'✔' if ok else '✘'} {label}：{reason}")
        lines.append(f"本地 hls.js（系统浏览器播放页用）："
                     f"{local_js or '未找到（将回退到 CDN，需要联网）'}")
        lines.append(f"本机中转服务（系统浏览器播放页用）："
                     f"{'运行中 ' + relay.relay_base_url() if relay.relay_is_running() else '未启动（首次播放时自动启动）'}")
        if m3ule_remote_session_detected():
            lines.append("检测到远程桌面会话：内嵌播放对显卡要求不高，若出不了画请换另一个内核。")
        lines.append("")
        lines.append("提示：把 hls.min.js 放到程序目录的 assets\\ 子目录即可离线播放（系统浏览器方式）。")
        lines.append("若 FFmpeg 内核显示不可用：源码运行请 pip install PySide6；编译版请确认打包时带上了 "
                     "Qt 的 multimedia 插件（见《软件升级迭代记录.md》的编译说明）。")
        QMessageBox.information(self, "播放环境", "\n".join(lines))

    @Slot()
    def stt_test_html5_playback(self) -> None:
        self._main_window.wnd_act_open_in_html5()

    def stt_fill_player_backend_combo(self) -> None:
        """填充「播放内核」下拉：只列 FFmpeg 与 VLC，不可用的加后缀提示。"""
        config = self._main_window.wnd_config_manager()
        target = m3ule_player_backend_key(config.cfg_get("player/backend"))
        self._combo_player_backend.blockSignals(True)
        self._combo_player_backend.clear()
        keys = []
        for key, label, ok, reason in m3ule_player_backend_report():
            self._combo_player_backend.addItem(label if ok else f"{label}（不可用）")
            keys.append(key)
            if not ok:
                self._combo_player_backend.setItemData(
                    self._combo_player_backend.count() - 1, reason, Qt.ToolTipRole)
        self._combo_player_backend.setCurrentIndex(keys.index(target) if target in keys else 0)
        self._combo_player_backend.blockSignals(False)
        self.stt_refresh_player_backend_label()

    def stt_refresh_html5_engine_label(self) -> None:
        relay = self._main_window.wnd_relay_server()
        local_js = relay.relay_local_hlsjs_path()
        usable = [label for _key, label, ok, _reason in m3ule_player_backend_report() if ok]
        hls_text = "本地 hls.js 已就绪" if local_js else "本地 hls.js 缺失（回退 CDN）"
        self._lbl_html5_engine.setText(
            "<span style='color:#5f6368'>内嵌内核："
            + html.escape("、".join(usable) or "无可用内核（可改用系统浏览器播放）")
            + f" · {hls_text}（系统浏览器播放页用）</span>")
        self.stt_refresh_player_backend_label()

    def stt_apply_player_library(self, key: str, text: str) -> bool:
        """保存「库文件路径」输入框的内容（供编辑完成 / 浏览 / 自动化测试调用，不弹窗）。

        输入框会以「实际落盘的值」为准回填：路径不存在时写入被拒绝，输入框自动还原。
        """
        setting_key = m3ule_player_backend_library_key(key)
        ok = m3ule_player_backend_set_library(key, text)
        saved = m3ule_settings_read_text(setting_key)
        target = self._edit_libvlc_path
        if target.text() != saved:
            target.setText(saved)
        self.stt_refresh_player_backend_label()
        return ok

    def stt_refresh_player_backend_label(self) -> None:
        """显示当前内核与可用内核概览（未安装的内核给出安装指引）。"""
        current = m3ule_player_backend_label(m3ule_player_backend_key(
            self._combo_player_backend.currentText()
            or self._main_window.wnd_config_manager().cfg_get("player/backend")))
        usable = [label for _key, label, ok, _reason in m3ule_player_backend_report() if ok]
        missing = []
        for _key, label, ok, reason in m3ule_player_backend_report():
            if not ok:
                missing.append(f"{label}（{reason}）")
        parts = [f"<span style='color:#5f6368'>当前选择：<b>{html.escape(current)}</b>"
                 f" · 本机可用：{html.escape('、'.join(usable) or '无')}</span>"]
        if missing:
            parts.append("<span style='color:#9a6b00'>不可用：" + html.escape("；".join(missing)) + "</span>")
        self._lbl_player_backend_state.setText("<br>".join(parts))

    def stt_build_io_group(self) -> QGroupBox:
        box = QGroupBox("文件与备份")
        grid = QGridLayout(box)
        grid.setHorizontalSpacing(8)
        grid.setVerticalSpacing(4)

        self._chk_backup_on_save = QCheckBox("保存时自动备份原文件到 backups 目录")
        grid.addWidget(self._chk_backup_on_save, 0, 0, 1, 3)
        self._spin_backup_keep = QSpinBox()
        self._spin_backup_keep.setRange(1, 999)
        grid.addWidget(QLabel("备份保留份数："), 0, 3)
        grid.addWidget(self._spin_backup_keep, 0, 4)

        grid.addWidget(QLabel("最近打开目录："), 1, 0)
        self._edit_last_open = QLineEdit()
        self._edit_last_open.setReadOnly(True)
        grid.addWidget(self._edit_last_open, 1, 1, 1, 3)
        grid.addWidget(QLabel("最近保存目录："), 2, 0)
        self._edit_last_save = QLineEdit()
        self._edit_last_save.setReadOnly(True)
        grid.addWidget(self._edit_last_save, 2, 1, 1, 3)

        grid.addWidget(QLabel("上次打开的文件："), 3, 0)
        self._edit_last_file = QLineEdit()
        self._edit_last_file.setReadOnly(True)
        self._edit_last_file.setToolTip("下次启动会自动加载这个文件（可在下面关闭）")
        grid.addWidget(self._edit_last_file, 3, 1, 1, 3)

        self._chk_auto_open_last = QCheckBox("启动时自动打开上次的文件（不用每次重新选）")
        self._chk_auto_open_last.setToolTip(
            "把上次打开的文件记下来，下次启动自动加载并回填检测缓存。\n"
            "命令行已经指定文件时不受影响。")
        grid.addWidget(self._chk_auto_open_last, 4, 0, 1, 4)

        self._chk_auto_save_settings = QCheckBox("设置改动立即写入磁盘（推荐开启）")
        grid.addWidget(self._chk_auto_save_settings, 5, 0, 1, 3)
        self._btn_open_program_dir = QPushButton("打开程序目录")
        self._btn_open_program_dir.clicked.connect(self.stt_open_program_dir)
        grid.addWidget(self._btn_open_program_dir, 5, 4)
        grid.setColumnStretch(5, 1)

        self._chk_backup_on_save.toggled.connect(self.stt_on_changed)
        self._spin_backup_keep.valueChanged.connect(self.stt_on_changed)
        self._chk_auto_save_settings.toggled.connect(self.stt_on_changed)
        self._chk_auto_open_last.toggled.connect(self.stt_on_changed)
        return box

    def stt_build_ui_group(self) -> QGroupBox:
        box = QGroupBox("界面")
        grid = QGridLayout(box)
        grid.setHorizontalSpacing(8)
        grid.setVerticalSpacing(4)

        grid.addWidget(QLabel("界面字体大小："), 0, 0)
        self._spin_font_size = QSpinBox()
        self._spin_font_size.setRange(8, 20)
        grid.addWidget(self._spin_font_size, 0, 1)
        grid.addWidget(QLabel("表格行高："), 0, 2)
        self._spin_row_height = QSpinBox()
        self._spin_row_height.setRange(18, 60)
        grid.addWidget(self._spin_row_height, 0, 3)
        grid.addWidget(QLabel("主题："), 0, 4)
        self._combo_theme = QComboBox()
        self._combo_theme.addItems(["浅色", "深色"])
        grid.addWidget(self._combo_theme, 0, 5)
        self._chk_log_auto_scroll = QCheckBox("日志自动滚动")
        grid.addWidget(self._chk_log_auto_scroll, 1, 0, 1, 2)
        self._chk_test_failed_only = QCheckBox("测试页默认只看失败项")
        grid.addWidget(self._chk_test_failed_only, 1, 2, 1, 2)

        self._btn_reset_layout = QPushButton("重置窗口布局")
        self._btn_reset_layout.clicked.connect(self.stt_reset_layout)
        grid.addWidget(self._btn_reset_layout, 1, 4, 1, 2)
        grid.setColumnStretch(6, 1)

        self._spin_font_size.valueChanged.connect(self.stt_on_changed)
        self._spin_row_height.valueChanged.connect(self.stt_on_changed)
        self._combo_theme.currentIndexChanged.connect(self.stt_on_changed)
        self._chk_log_auto_scroll.toggled.connect(self.stt_on_changed)
        self._chk_test_failed_only.toggled.connect(self.stt_on_changed)
        return box

    def stt_build_env_group(self) -> QGroupBox:
        box = QGroupBox("密钥与数据库（保存在程序目录 .env，不写入源码）")
        grid = QGridLayout(box)
        grid.setHorizontalSpacing(8)
        grid.setVerticalSpacing(4)

        grid.addWidget(QLabel("EPG / 接口 API Key："), 0, 0)
        self._edit_env_api_key = QLineEdit()
        self._edit_env_api_key.setPlaceholderText("M3ULE_EPG_API_KEY（可选，用于台标/节目单扩展）")
        grid.addWidget(self._edit_env_api_key, 0, 1, 1, 3)

        grid.addWidget(QLabel("数据库密码："), 1, 0)
        self._edit_env_db_password = QLineEdit()
        self._edit_env_db_password.setEchoMode(QLineEdit.Password)
        self._edit_env_db_password.setPlaceholderText("M3ULE_DB_PASSWORD（本地 SQLite 无需密码，留空即可）")
        grid.addWidget(self._edit_env_db_password, 1, 1, 1, 3)
        self._chk_show_db_password = QCheckBox("显示")
        self._chk_show_db_password.toggled.connect(
            lambda checked: self._edit_env_db_password.setEchoMode(
                QLineEdit.Normal if checked else QLineEdit.Password))
        grid.addWidget(self._chk_show_db_password, 1, 4)

        grid.addWidget(QLabel("数据库文件："), 2, 0)
        self._edit_db_path = QLineEdit()
        self._edit_db_path.setReadOnly(True)
        grid.addWidget(self._edit_db_path, 2, 1, 1, 3)

        button_row = QHBoxLayout()
        btn_save = QPushButton("保存到 .env")
        btn_save.clicked.connect(self.stt_save_env)
        button_row.addWidget(btn_save)
        btn_reload = QPushButton("重新加载 .env")
        btn_reload.clicked.connect(self.stt_reload_env)
        button_row.addWidget(btn_reload)
        btn_open = QPushButton("打开 .env")
        btn_open.clicked.connect(self.stt_open_env_file)
        button_row.addWidget(btn_open)
        btn_template = QPushButton("生成 .env 模板")
        btn_template.clicked.connect(self.stt_write_env_template)
        button_row.addWidget(btn_template)
        button_row.addStretch(1)
        grid.addLayout(button_row, 3, 0, 1, 5)

        hint = QLabel("提示：本地使用 SQLite，无需数据库密码；该字段用于将来切换数据库时保留凭据。")
        hint.setStyleSheet("color:#5f6368;")
        grid.addWidget(hint, 4, 0, 1, 5)
        grid.setColumnStretch(5, 1)
        return box

    def stt_build_maintenance_group(self) -> QGroupBox:
        box = QGroupBox("维护")
        grid = QGridLayout(box)
        grid.setHorizontalSpacing(8)
        grid.setVerticalSpacing(4)

        self._lbl_db_stats = QLabel("数据库统计：—")
        grid.addWidget(self._lbl_db_stats, 0, 0, 1, 2)
        btn_refresh = QPushButton("刷新统计")
        btn_refresh.clicked.connect(self.stt_refresh_db_stats)
        grid.addWidget(btn_refresh, 0, 2)
        btn_clear_history = QPushButton("清空测试历史")
        btn_clear_history.clicked.connect(self.stt_clear_history)
        grid.addWidget(btn_clear_history, 0, 3)
        btn_clear_scan = QPushButton("清空扫描记录")
        btn_clear_scan.clicked.connect(self.stt_open_backup_dir)
        btn_clear_scan.setText("打开备份目录")
        grid.addWidget(btn_clear_scan, 0, 4)
        btn_reset = QPushButton("恢复默认设置")
        btn_reset.clicked.connect(self.stt_restore_defaults)
        grid.addWidget(btn_reset, 0, 5)
        grid.setColumnStretch(6, 1)

        self._lbl_settings_path = QLabel("")
        self._lbl_settings_path.setStyleSheet("color:#5f6368;")
        self._lbl_settings_path.setTextInteractionFlags(Qt.TextSelectableByMouse)
        grid.addWidget(self._lbl_settings_path, 1, 0, 1, 6)
        return box

    def stt_build_about_group(self) -> QGroupBox:
        box = QGroupBox("关于")
        layout = QVBoxLayout(box)
        info = QLabel(
            f"<b>{M3ULE_APP_NAME_CN}</b>　版本 <b>v{M3ULE_VERSION}</b>　构建日期 {M3ULE_BUILD_DATE}<br>"
            f"技术栈：Python 3.10 · PySide6 (Qt6) · requests · SQLite3<br>"
            f"用途：m3u / m3u8 直播源文件的编辑、测试、ID 扫描与新旧对比。")
        info.setWordWrap(True)
        layout.addWidget(info)
        row = QHBoxLayout()
        btn_help = QPushButton("使用说明")
        btn_help.clicked.connect(self._main_window.wnd_act_show_help)
        row.addWidget(btn_help)
        btn_about = QPushButton("关于本程序")
        btn_about.clicked.connect(self._main_window.wnd_act_show_about)
        row.addWidget(btn_about)
        btn_icon = QPushButton("图标状态")
        btn_icon.clicked.connect(self.stt_show_icon_status)
        row.addWidget(btn_icon)
        row.addStretch(1)
        layout.addLayout(row)
        return box

    # -- 读写 ---------------------------------------------------------------
    def stt_reload_from_config(self) -> None:
        config = self._main_window.wnd_config_manager()
        category = m3ule_safe_int(config.cfg_get(self.M3ULE_SETTINGS_CATEGORY_KEY), 0)
        if 0 <= category < self._category_tabs.count() and \
                self._category_tabs.currentIndex() != category:
            self._category_tabs.blockSignals(True)
            self._category_tabs.setCurrentIndex(category)
            self._category_tabs.blockSignals(False)
        self._building = True
        self._spin_probe_workers.setValue(config.cfg_get("probe/workers"))
        self._spin_probe_timeout.setValue(config.cfg_get("probe/timeout"))
        self._spin_probe_retries.setValue(config.cfg_get("probe/retries"))
        self._chk_probe_deep.setChecked(config.cfg_get("probe/deep"))
        self._chk_probe_ignore_ssl.setChecked(config.cfg_get("probe/ignore_ssl"))
        self._chk_cache_enabled.setChecked(config.cfg_get("cache/enabled"))
        self._chk_cache_auto_apply.setChecked(config.cfg_get("cache/auto_apply"))
        self._chk_cache_skip_fresh.setChecked(config.cfg_get("cache/skip_fresh"))
        self._spin_cache_ttl.setValue(config.cfg_get("cache/ttl_hours"))
        self._edit_probe_ua.setText(config.cfg_get("probe/user_agent"))
        self._edit_probe_proxy.setText(config.cfg_get("probe/proxy"))
        self._edit_player_path.setText(config.cfg_get("player/path"))
        self._edit_libvlc_path.setText(config.cfg_get("player/libvlc_path"))
        self._combo_html5_mode.setCurrentText(config.cfg_get("player/html5_mode"))
        self.stt_fill_player_backend_combo()
        self._chk_html5_autoplay.setChecked(config.cfg_get("player/html5_autoplay"))
        self._chk_html5_local_hls.setChecked(config.cfg_get("player/html5_local_hlsjs"))
        self.stt_refresh_html5_engine_label()
        self._chk_backup_on_save.setChecked(config.cfg_get("io/auto_backup_on_save"))
        self._spin_backup_keep.setValue(config.cfg_get("io/backup_keep"))
        self._chk_auto_save_settings.setChecked(config.cfg_get("io/auto_save_settings"))
        self._chk_auto_open_last.setChecked(config.cfg_get("io/auto_open_last"))
        self._edit_last_open.setText(config.cfg_get("io/last_open_dir"))
        self._edit_last_save.setText(config.cfg_get("io/last_save_dir"))
        self._edit_last_file.setText(config.cfg_get("io/last_file"))
        self._spin_font_size.setValue(config.cfg_get("ui/font_size"))
        self._spin_row_height.setValue(config.cfg_get("ui/table_row_height"))
        self._combo_theme.setCurrentText(config.cfg_get("ui/theme"))
        self._chk_log_auto_scroll.setChecked(config.cfg_get("ui/log_auto_scroll"))
        self._chk_test_failed_only.setChecked(config.cfg_get("ui/test_failed_only"))
        self._edit_env_api_key.setText(config.cfg_env_value("M3ULE_EPG_API_KEY", ""))
        self._edit_env_db_password.setText(config.cfg_env_value("M3ULE_DB_PASSWORD", ""))
        self._edit_db_path.setText(m3ule_get_db_path())
        self._lbl_settings_path.setText(
            f"设置文件：{m3ule_get_settings_path()}　·　配置文件：{m3ule_get_env_path()}")
        self._building = False
        self.stt_refresh_db_stats()

    @Slot()
    def stt_on_changed(self) -> None:
        if self._building:
            return
        config = self._main_window.wnd_config_manager()
        config.cfg_set_many({
            "probe/workers": self._spin_probe_workers.value(),
            "probe/timeout": self._spin_probe_timeout.value(),
            "probe/retries": self._spin_probe_retries.value(),
            "probe/deep": self._chk_probe_deep.isChecked(),
            "probe/ignore_ssl": self._chk_probe_ignore_ssl.isChecked(),
            "probe/user_agent": self._edit_probe_ua.text(),
            "probe/proxy": self._edit_probe_proxy.text(),
            "cache/enabled": self._chk_cache_enabled.isChecked(),
            "cache/auto_apply": self._chk_cache_auto_apply.isChecked(),
            "cache/skip_fresh": self._chk_cache_skip_fresh.isChecked(),
            "cache/ttl_hours": self._spin_cache_ttl.value(),
            "player/path": self._edit_player_path.text(),
            "player/html5_mode": self._combo_html5_mode.currentText(),
            "player/backend": m3ule_player_backend_label(
                m3ule_player_backend_key(self._combo_player_backend.currentText())),
            "player/libvlc_path": self._edit_libvlc_path.text().strip(),
            "player/html5_autoplay": self._chk_html5_autoplay.isChecked(),
            "player/html5_local_hlsjs": self._chk_html5_local_hls.isChecked(),
            "io/auto_backup_on_save": self._chk_backup_on_save.isChecked(),
            "io/backup_keep": self._spin_backup_keep.value(),
            "io/auto_save_settings": self._chk_auto_save_settings.isChecked(),
            "io/auto_open_last": self._chk_auto_open_last.isChecked(),
            "ui/font_size": self._spin_font_size.value(),
            "ui/table_row_height": self._spin_row_height.value(),
            "ui/theme": self._combo_theme.currentText(),
            "ui/log_auto_scroll": self._chk_log_auto_scroll.isChecked(),
            "ui/test_failed_only": self._chk_test_failed_only.isChecked(),
        })
        self._main_window.wnd_apply_appearance()
        test_checkbox = getattr(self._main_window, "_chk_test_skip_cached", None)
        if test_checkbox is not None and test_checkbox.isChecked() != self._chk_cache_skip_fresh.isChecked():
            test_checkbox.blockSignals(True)
            test_checkbox.setChecked(self._chk_cache_skip_fresh.isChecked())
            test_checkbox.blockSignals(False)
        self._main_window.wnd_refresh_cache_stats()

    def stt_refresh_display_paths(self) -> None:
        config = self._main_window.wnd_config_manager()
        self._edit_last_open.setText(config.cfg_get("io/last_open_dir"))
        self._edit_last_save.setText(config.cfg_get("io/last_save_dir"))
        self._edit_last_file.setText(config.cfg_get("io/last_file"))

    @Slot()
    def stt_browse_player(self) -> None:
        current = self._edit_player_path.text().strip()
        start_dir = os.path.dirname(current) if current and os.path.isfile(current) else ""
        path, _ = QFileDialog.getOpenFileName(
            self, "选择播放器可执行文件", start_dir,
            "可执行文件 (*.exe);;所有文件 (*.*)")
        if path:
            self._edit_player_path.setText(path)
            self.stt_on_changed()

    @Slot()
    def stt_test_player(self) -> None:
        path = self._edit_player_path.text().strip()
        if path and not os.path.isfile(path):
            QMessageBox.warning(self, "提示", f"播放器路径不存在：\n{path}")
            return
        if not path:
            QMessageBox.information(self, "提示", "未设置播放器，将使用系统默认程序打开链接。")
            return
        QMessageBox.information(self, "提示", f"播放器路径有效：\n{path}")

    @Slot()
    def stt_open_program_dir(self) -> None:
        path = m3ule_get_program_dir()
        try:
            os.startfile(path)  # type: ignore[attr-defined]
        except Exception:
            QDesktopServices.openUrl(QUrl.fromLocalFile(path))

    @Slot()
    def stt_open_backup_dir(self) -> None:
        path = m3ule_get_backup_dir()
        try:
            os.startfile(path)  # type: ignore[attr-defined]
        except Exception:
            QDesktopServices.openUrl(QUrl.fromLocalFile(path))

    @Slot()
    def stt_save_env(self) -> None:
        api_key = self._edit_env_api_key.text().strip()
        db_password = self._edit_env_db_password.text().strip()
        proxy_text = self._edit_probe_proxy.text().strip()
        ok = True
        ok = m3ule_save_env_key("M3ULE_EPG_API_KEY", api_key) and ok
        ok = m3ule_save_env_key("M3ULE_DB_PASSWORD", db_password) and ok
        if proxy_text:
            ok = m3ule_save_env_key("M3ULE_PROXY", proxy_text) and ok
        if not ok:
            QMessageBox.warning(self, "保存失败", f"无法写入 {m3ule_get_env_path()}")
            return
        self._main_window.wnd_config_manager().cfg_reload_env_secrets()
        self._main_window.wnd_append_log("密钥已保存到 .env。")
        QMessageBox.information(self, "完成", f"已保存到：\n{m3ule_get_env_path()}")

    @Slot()
    def stt_reload_env(self) -> None:
        config = self._main_window.wnd_config_manager()
        config.cfg_reload_env_secrets()
        self._building = True
        self._edit_env_api_key.setText(config.cfg_env_value("M3ULE_EPG_API_KEY", ""))
        self._edit_env_db_password.setText(config.cfg_env_value("M3ULE_DB_PASSWORD", ""))
        env_proxy = config.cfg_env_value("M3ULE_PROXY", "")
        if env_proxy:
            self._edit_probe_proxy.setText(env_proxy)
        self._building = False
        self._main_window.wnd_append_log("已重新加载 .env。")

    @Slot()
    def stt_open_env_file(self) -> None:
        path = m3ule_get_env_path()
        if not os.path.isfile(path):
            m3ule_save_env_key("M3ULE_DB_PASSWORD", "")
        try:
            os.startfile(path)  # type: ignore[attr-defined]
        except Exception:
            QDesktopServices.openUrl(QUrl.fromLocalFile(path))

    @Slot()
    def stt_write_env_template(self) -> None:
        path = os.path.join(m3ule_get_program_dir(), ".env.example")
        content = (
            "# M3U 直播源编辑管理系统 - 配置文件示例\n"
            "# 复制本文件为 .env 并按需填写，程序启动时会自动加载。\n"
            "# 注意：.env 不要上传到公开仓库。\n\n"
            "# 可选：EPG / 接口 API Key\n"
            "M3ULE_EPG_API_KEY=\n\n"
            "# 可选：数据库密码（本地 SQLite 无需密码）\n"
            "M3ULE_DB_PASSWORD=\n\n"
            "# 可选：网络代理\n"
            "# M3ULE_PROXY=http://127.0.0.1:7890\n\n"
            "# 可选：自定义 User-Agent\n"
            f"# M3ULE_USER_AGENT={M3ULE_DEFAULT_USER_AGENT}\n\n"
            "# 可选：自定义数据库文件位置\n"
            "# M3ULE_DB_PATH=\n"
        )
        try:
            with open(path, "w", encoding="utf-8") as handle:
                handle.write(content)
        except OSError as exc:
            QMessageBox.warning(self, "写入失败", str(exc))
            return
        QMessageBox.information(self, "完成", f"已生成模板：\n{path}")

    @Slot()
    def stt_refresh_db_stats(self) -> None:
        store = self._main_window.wnd_history_store()
        if store is None or not store.available:
            self._lbl_db_stats.setText(f"数据库不可用：{store.error if store else '未初始化'}")
            return
        self._lbl_db_stats.setText(
            f"数据库统计：测试历史 {store.dbh_count_rows('test_history')} 条 · "
            f"扫描记录 {store.dbh_count_rows('scan_runs')} 条 · "
            f"频道映射 {store.dbh_count_rows('id_remarks')} 条 · "
            f"检测缓存 {store.dbh_count_rows('probe_cache')} 条")

    @Slot()
    def stt_clear_history(self) -> None:
        store = self._main_window.wnd_history_store()
        if store is None or not store.available:
            return
        reply = QMessageBox.question(self, "确认", "确定清空所有测试历史与扫描记录吗？",
                                     QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if reply != QMessageBox.Yes:
            return
        store.dbh_clear_all_history()
        self.stt_refresh_db_stats()
        self._main_window.wnd_append_log("已清空历史记录。")

    @Slot()
    def stt_restore_defaults(self) -> None:
        reply = QMessageBox.question(
            self, "确认", "确定把所有设置恢复为默认值吗？（不影响频道的备注与测试结果）",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if reply != QMessageBox.Yes:
            return
        self._main_window.wnd_config_manager().cfg_reset_all()
        self.stt_reload_from_config()
        self._main_window.wnd_apply_appearance()
        self._main_window.wnd_append_log("已恢复默认设置。")

    @Slot()
    def stt_reset_layout(self) -> None:
        self._main_window.wnd_reset_layout()
        self._main_window.wnd_append_log("已重置窗口布局。")

    @Slot()
    def stt_show_icon_status(self) -> None:
        path = m3ule_get_icon_path()
        if path:
            QMessageBox.information(self, "图标状态", f"已加载图标：\n{path}")
        else:
            QMessageBox.information(self, "图标状态", "程序目录下未找到 icon.ico，将使用默认图标。")


# ----------------------------------------------------------------------------
# 主窗口
# ----------------------------------------------------------------------------

class M3ULiveEditorMainWindow(QMainWindow):
    """主窗口：整合文件编辑、链接测试、ID 扫描、对比分析与设置。"""

    M3ULE_MAIN_SPLITTER_KEY = "ui/geometry/main_splitter"
    M3ULE_EDIT_SPLITTER_KEY = "ui/geometry/edit_splitter"
    M3ULE_GEOMETRY_KEY = "ui/geometry/window"
    M3ULE_WINDOW_STATE_KEY = "ui/geometry/window_state"
    M3ULE_RECENT_KEY = "io/recent_files"
    M3ULE_COLUMN_WIDTH_KEY = "ui/column_widths"

    def __init__(self):
        super().__init__()
        self.setWindowTitle(M3ULE_WINDOW_TITLE)
        self.setMinimumSize(1024, 640)
        self.resize(1440, 860)
        self.setAcceptDrops(True)

        self._config = M3ULiveEditorConfigManager(self)
        self._history = M3ULiveEditorHistoryStore()
        self._document = M3ULiveEditorDocument()
        self._model = M3ULiveEditorTableModel(self)
        self._model.mdl_set_document(self._document)
        self._model.sig_model_entry_edited.connect(self.wnd_on_model_entry_edited)

        self._proxy_edit = M3ULiveEditorSortFilterProxyModel(self)
        self._proxy_edit.setSourceModel(self._model)
        self._proxy_test = M3ULiveEditorSortFilterProxyModel(self)
        self._proxy_test.setSourceModel(self._model)

        self._test_worker = None
        self._relay = None
        self._html5_dialog = None
        self._index_map_dialog = None
        self._sync_dialog = None
        self._detail_updating = False
        self._last_skipped_cached = 0
        self._test_cache_written = 0
        self._cache_total_cache = -1
        self._test_total = 0
        self._test_done = 0
        self._test_summary_counts = {"ok": 0, "bad": 0}
        self._recent_files: list = []
        self._filter_timer = QTimer(self)
        self._filter_timer.setSingleShot(True)
        self._filter_timer.setInterval(280)
        self._filter_timer.timeout.connect(self.wnd_refresh_filter)
        self._save_timer = QTimer(self)
        self._save_timer.setSingleShot(True)
        self._save_timer.setInterval(400)
        self._save_timer.timeout.connect(self.wnd_save_runtime_settings)

        self.wnd_build_actions()
        self.wnd_build_ui()
        self.wnd_build_menus()
        self.wnd_build_toolbar()
        self.wnd_restore_settings()
        self.wnd_apply_appearance()
        self.wnd_update_title()
        self.wnd_update_counts()
        self.wnd_rebuild_group_filter()

        self.wnd_append_log(f"{M3ULE_APP_NAME_CN} v{M3ULE_VERSION} 已启动。")
        if self._history.available:
            self.wnd_append_log(f"历史数据库：{self._history.db_path}")
        else:
            self.wnd_append_log(f"历史数据库不可用：{self._history.error}")
        icon_path = m3ule_get_icon_path()
        self.wnd_append_log(f"图标：{icon_path or '未找到 icon.ico（已跳过）'}")
        self.wnd_append_log(
            "弹窗播放内核：" + m3ule_player_backend_label(
                m3ule_player_backend_key(self._config.cfg_get("player/backend")))
            + "（本机可用：" + "、".join(
                label for _key, label, ok, _reason in m3ule_player_backend_report() if ok) + "）")
        if self._history.available:
            if self.wnd_probe_cache_enabled():
                self.wnd_append_log(
                    f"检测缓存：已保存 {self._history.dbh_count_probe_cache()} 条历史检测结果，"
                    "打开文件时会自动套用（可在“设置 → 检测缓存”调整）。")
            self.wnd_refresh_cache_stats()
        if not m3ule_get_requests_module():
            QMessageBox.warning(
                self, "缺少依赖",
                "未检测到 requests 库，链接测试功能不可用。\n请执行：pip install requests")

    # ------------------------------------------------------------------
    # 对外访问器
    # ------------------------------------------------------------------
    def wnd_config_manager(self) -> M3ULiveEditorConfigManager:
        return self._config

    def wnd_history_store(self):
        return self._history

    def wnd_document_model(self) -> M3ULiveEditorTableModel:
        return self._model

    def wnd_document(self) -> M3ULiveEditorDocument:
        return self._document

    def wnd_current_path(self) -> str:
        return self._document.path or ""

    def wnd_icon_available(self) -> bool:
        return bool(m3ule_get_icon_path())

    # ------------------------------------------------------------------
    # 构建：动作
    # ------------------------------------------------------------------
    def wnd_build_actions(self) -> None:
        style = self.style()

        def make(text, shortcut=None, slot=None, tip=None):
            action = QAction(text, self)
            if shortcut:
                action.setShortcut(QKeySequence(shortcut))
            if tip:
                action.setToolTip(tip)
                action.setStatusTip(tip)
            if slot:
                action.triggered.connect(slot)
            return action

        self.qact_new_file = make("新建", "Ctrl+N", self.wnd_act_new_file, "新建空的 m3u 文件")
        self.qact_open_file = make("打开…", "Ctrl+O", self.wnd_act_open_file, "打开 m3u / m3u8 文件")
        self.qact_import_append = make("追加导入…", None, self.wnd_act_import_append, "把另一个 m3u 文件的内容追加到当前文件")
        self.qact_save_file = make("保存", "Ctrl+S", self.wnd_act_save_file, "保存到当前文件")
        self.qact_save_file_as = make("另存为…", "Ctrl+Shift+S", self.wnd_act_save_file_as, "另存为新文件")
        self.qact_export_csv = make("导出为 CSV…", None, self.wnd_act_export_csv, "把频道列表导出为 CSV")
        self.qact_export_m3u = make("导出为 M3U…", None, self.wnd_act_export_m3u, "把频道列表导出为 m3u 文件")
        self.qact_backup_now = make("备份当前文件", None, self.wnd_act_backup_now, "立即把当前文件复制到 backups 目录")
        self.qact_exit = make("退出", "Ctrl+Q", self.close, "退出程序")

        self.qact_add_link = make("添加链接…", "Insert", self.wnd_act_add_link, "添加一条频道链接")
        self.qact_batch_add = make("批量添加…", "Ctrl+Shift+N", self.wnd_act_batch_add, "批量添加多条链接")
        self.qact_edit_entry = make("编辑选中项…", "F2", self.wnd_act_edit_entry, "编辑当前选中的频道")
        self.qact_delete_selected = make("删除选中项", "Ctrl+D", self.wnd_act_delete_selected, "删除选中的频道（Ctrl+D）")
        self.qact_batch_delete = make("批量删除…", "Ctrl+Shift+Delete", self.wnd_act_batch_delete, "按条件批量删除")
        self.qact_delete_all = make("删除全部", None, self.wnd_act_delete_all, "清空所有频道条目")
        self.qact_remove_duplicates = make("删除重复链接", None, self.wnd_act_remove_duplicates, "按链接去重（保留第一条）")
        self.qact_batch_replace = make("批量查找替换…", "Ctrl+H", self.wnd_act_batch_replace, "在指定字段中批量替换")
        self.qact_batch_group = make(
            "批量修改分组…", "Ctrl+G", self.wnd_act_batch_group,
            "把多条频道的分组一次改掉：设为新分组、加入已有分组，或清除分组\n"
            "（先在列表里多选，或按当前筛选结果整批处理）")
        self.qact_move_up = make("上移", "Ctrl+Up", lambda: self.wnd_act_move_entry(-1), "把选中条目上移一行")
        self.qact_move_down = make("下移", "Ctrl+Down", lambda: self.wnd_act_move_entry(1), "把选中条目下移一行")
        self.qact_find_focus = make("查找/筛选", "Ctrl+F", self.wnd_act_find_focus, "聚焦搜索框")

        self.qact_columns_edit = make(
            "文件编辑列…", None, lambda: self.wnd_act_choose_columns(self._view_edit),
            "自定义「文件编辑」表显示哪些列、按什么顺序显示")
        self.qact_columns_test = make(
            "链接测试列…", None, lambda: self.wnd_act_choose_columns(self._view_test),
            "自定义「链接测试」表显示哪些列、按什么顺序显示")
        self.qact_columns_reset = make(
            "恢复默认列", None, lambda: self.wnd_act_reset_columns(None),
            "把当前表的列恢复成默认（全部显示、源码顺序）")
        self.qact_columns_fit = make(
            "适应内容宽度", None, lambda: self.wnd_active_table_view().resizeColumnsToContents(),
            "按当前内容自动调整列宽")

        self.qact_test_all = make("测试全部", "Ctrl+T", lambda: self.wnd_act_start_test("all"), "测试所有链接")
        self.qact_test_selected = make("测试选中", "Ctrl+Shift+T", lambda: self.wnd_act_start_test("selected"), "只测试选中的链接")
        self.qact_test_failed = make("重测失败项", None, lambda: self.wnd_act_start_test("failed"), "重新测试失败/超时/错误的链接")
        self.qact_test_untested = make("测试未测试项", None, lambda: self.wnd_act_start_test("untested"), "只测试尚未测试过的链接")
        self.qact_test_stop = make("停止测试", "Esc", self.wnd_act_stop_test, "停止当前测试")
        self.qact_test_force_all = make("忽略缓存重测全部", None, lambda: self.wnd_act_start_test("force"),
                                        "无视检测缓存，重新检测所有链接")
        self.qact_clear_test_results = make("清空测试结果", None, self.wnd_act_clear_test_results, "清除所有测试状态（不影响检测缓存）")
        self.qact_apply_probe_cache = make("应用检测缓存", None, self.wnd_act_apply_probe_cache,
                                           "把之前保存的检测结果套用到当前文件")
        self.qact_clear_probe_cache = make("清空检测缓存", None, self.wnd_act_clear_probe_cache,
                                           "删除所有已保存的检测结果")
        self.qact_clear_selected_cache = make("清除所选链接的缓存", None, self.wnd_act_clear_selected_cache,
                                              "删除所选链接已保存的检测结果")

        self.qact_open_in_player = make("用播放器打开选中", "Ctrl+Enter", self.wnd_act_open_in_player, "用 VLC/默认播放器打开链接")
        self.qact_open_in_html5 = make("用弹窗播放", "Ctrl+Alt+Enter", self.wnd_act_open_in_html5,
                                        "在当前文件的频道间连续播放（FFmpeg / VLC 内核）")
        self.qact_copy_url = make("复制链接", "Ctrl+Shift+C", self.wnd_act_copy_url, "复制选中条目的链接")
        self.qact_open_in_browser = make("在浏览器打开", None, self.wnd_act_open_in_browser, "用浏览器打开链接")
        self.qact_open_program_dir = make("打开程序目录", None, self.wnd_act_open_program_dir)
        self.qact_open_env_file = make("打开 .env", None, self.wnd_act_open_env_file)
        self.qact_open_data_dir = make("打开数据目录", None, self.wnd_act_open_data_dir)
        self.qact_id_scan = make("ID 扫描", None, lambda: self._tabs.setCurrentWidget(self._tab_scan))
        self.qact_diff_analysis = make("对比分析", None, lambda: self._tabs.setCurrentWidget(self._tab_diff))
        self.qact_index_map = make("编号映射表…", "Ctrl+M", self.wnd_act_show_index_map,
                                   "把标题/链接里的编号解析成「编号 → 频道名」对照表，并叠加实测状态")
        self.qact_sync_ids = make(
            "频道同步…", "Ctrl+Shift+M", self.wnd_act_sync_index_ids,
            "把已校对文件里确认的频道同步到另一个文件（例如 xteve.m3u）：\n"
            "· 只更新编号：只改同名频道的编号，其它频道原样保留、分组/台标不动；\n"
            "· 整表替换：直接用来源的频道重建目标文件，旧文件里不在新列表的频道清除\n"
            "（同名频道沿用原分组与台标，可只同步有信号的频道）")

        self.qact_match_logos = make(
            "台标自动匹配…", "Ctrl+Shift+L", self.wnd_act_match_logos,
            "按频道名称自动补 tvg-logo（台标）：\n"
            "· 参考文件/网址：从另一个已带台标的 m3u（或 EPG、iptv-org 中国频道列表）学「频道名 → 台标」；\n"
            "· 台标库：每次匹配成功的都会存下来，跨启动复用；\n"
            "· 台标文件夹：把图片文件名当频道名（CCTV1.png → 频道 CCTV1）；\n"
            "匹配结果先在预览里列出来（精确 / 去噪 / 相似建议 / 未匹配），勾选后才写回")

        self.qact_show_help = make("使用说明", "F1", self.wnd_act_show_help)
        self.qact_show_about = make("关于", None, self.wnd_act_show_about)
        self.qact_check_icon = make("检查图标状态", None, self.wnd_act_check_icon)

    # ------------------------------------------------------------------
    # 构建：界面
    # ------------------------------------------------------------------
    def wnd_build_ui(self) -> None:
        central = QWidget()
        self.setCentralWidget(central)
        root = QVBoxLayout(central)
        root.setContentsMargins(4, 4, 4, 2)
        root.setSpacing(4)

        self._main_splitter = QSplitter(Qt.Vertical)
        self._main_splitter.setChildrenCollapsible(True)
        root.addWidget(self._main_splitter, 1)

        self._tabs = QTabWidget()
        self._tabs.setDocumentMode(True)
        self._main_splitter.addWidget(self._tabs)

        self._tab_edit = self.wnd_build_edit_tab()
        self._tab_test = self.wnd_build_test_tab()
        self._tab_scan = M3ULiveEditorIdScanTab(self)
        self._tab_diff = M3ULiveEditorDiffTab(self)
        self._tab_settings = M3ULiveEditorSettingsTab(self)

        self._tabs.addTab(self._tab_edit, "文件编辑")
        self._tabs.addTab(self._tab_test, "链接测试")
        self._tabs.addTab(self._tab_scan, "ID 扫描")
        self._tabs.addTab(self._tab_diff, "对比分析")
        self._tabs.addTab(self._tab_settings, "设置")

        self._main_splitter.addWidget(self.wnd_build_log_panel())
        self._main_splitter.setStretchFactor(0, 5)
        self._main_splitter.setStretchFactor(1, 1)
        self._main_splitter.setSizes([720, 180])

        self.wnd_build_statusbar()

    def wnd_build_edit_tab(self) -> QWidget:
        tab = QWidget()
        layout = QVBoxLayout(tab)
        layout.setContentsMargins(4, 4, 4, 4)
        layout.setSpacing(4)

        filter_row = QHBoxLayout()
        filter_row.setSpacing(4)
        filter_row.addWidget(QLabel("筛选："))
        self._edit_filter_keyword = QLineEdit()
        self._edit_filter_keyword.setPlaceholderText("输入关键词（频道名 / 分组 / ID / 链接 / 备注）")
        self._edit_filter_keyword.setClearButtonEnabled(True)
        self._edit_filter_keyword.textChanged.connect(lambda _text: self._filter_timer.start())
        filter_row.addWidget(self._edit_filter_keyword, 3)

        filter_row.addWidget(QLabel("分组："))
        self._combo_filter_group = QComboBox()
        self._combo_filter_group.setMinimumWidth(140)
        self._combo_filter_group.currentIndexChanged.connect(self.wnd_refresh_filter)
        filter_row.addWidget(self._combo_filter_group, 1)

        filter_row.addWidget(QLabel("状态："))
        self._combo_filter_state = QComboBox()
        self._combo_filter_state.addItems(["全部", M3ULE_STATUS_OK, M3ULE_STATUS_PARTIAL,
                                           M3ULE_STATUS_FAIL, M3ULE_STATUS_TIMEOUT,
                                           M3ULE_STATUS_ERROR, "未测试"])
        self._combo_filter_state.currentIndexChanged.connect(self.wnd_refresh_filter)
        filter_row.addWidget(self._combo_filter_state)

        self._chk_filter_failed = QCheckBox("仅显示不可用")
        self._chk_filter_failed.toggled.connect(self.wnd_refresh_filter)
        filter_row.addWidget(self._chk_filter_failed)

        btn_clear_filter = QPushButton("清除筛选")
        btn_clear_filter.clicked.connect(self.wnd_act_clear_filter)
        filter_row.addWidget(btn_clear_filter)
        filter_row.addStretch(1)
        layout.addLayout(filter_row)

        edit_splitter = QSplitter(Qt.Vertical)
        self._edit_splitter = edit_splitter

        self._view_edit = QTableView()
        self.wnd_configure_table_view(self._view_edit)
        self._view_edit.setModel(self._proxy_edit)
        self._view_edit.setSortingEnabled(True)
        self._view_edit.sortByColumn(0, Qt.AscendingOrder)
        self._view_edit.doubleClicked.connect(self.wnd_on_edit_view_double_clicked)
        edit_splitter.addWidget(self._view_edit)

        detail_box = QGroupBox("选中条目详情（修改后点“应用修改”或双击其他行自动应用）")
        detail_grid = QGridLayout(detail_box)
        detail_grid.setHorizontalSpacing(6)
        detail_grid.setVerticalSpacing(2)
        self._detail_editors: dict = {}
        field_defs = [
            ("name", "频道名称"), ("tvg-name", "tvg名称"), ("group-title", "分组"),
            ("tvg-id", "tvg-id"), ("channelID", "channelID"), ("tvg-chno", "频道号"),
            ("tvg-logo", "台标"), ("duration", "时长"), ("remark", "备注"),
        ]
        for position, (key, label) in enumerate(field_defs):
            row = position // 3
            column = (position % 3) * 2
            detail_grid.addWidget(QLabel(f"{label}："), row, column)
            editor = QLineEdit()
            editor.editingFinished.connect(self.wnd_apply_detail_fields)
            self._detail_editors[key] = editor
            detail_grid.addWidget(editor, row, column + 1)

        url_row = (len(field_defs) + 2) // 3
        detail_grid.addWidget(QLabel("链接："), url_row, 0)
        self._detail_url_editor = QLineEdit()
        self._detail_url_editor.editingFinished.connect(self.wnd_apply_detail_fields)
        detail_grid.addWidget(self._detail_url_editor, url_row, 1, 1, 5)
        self._detail_editors["url"] = self._detail_url_editor

        button_row = QHBoxLayout()
        self._btn_apply_detail = QPushButton("应用修改")
        self._btn_apply_detail.clicked.connect(self.wnd_apply_detail_fields)
        button_row.addWidget(self._btn_apply_detail)
        btn_play = QPushButton("用播放器打开")
        btn_play.clicked.connect(self.wnd_act_open_in_player)
        button_row.addWidget(btn_play)
        btn_html5 = QPushButton("弹窗播放")
        btn_html5.setToolTip("在内嵌播放器中打开（FFmpeg / VLC 内核，Ctrl+Alt+Enter）")
        btn_html5.clicked.connect(self.wnd_act_open_in_html5)
        button_row.addWidget(btn_html5)
        btn_copy = QPushButton("复制链接")
        btn_copy.clicked.connect(self.wnd_act_copy_url)
        button_row.addWidget(btn_copy)
        btn_test_one = QPushButton("测试该条")
        btn_test_one.clicked.connect(lambda: self.wnd_act_start_test("selected"))
        button_row.addWidget(btn_test_one)
        btn_delete_one = QPushButton("删除该条")
        btn_delete_one.clicked.connect(self.wnd_act_delete_selected)
        button_row.addWidget(btn_delete_one)
        button_row.addStretch(1)
        self._lbl_detail_info = QLabel("未选中")
        self._lbl_detail_info.setStyleSheet("color:#5f6368;")
        button_row.addWidget(self._lbl_detail_info)
        detail_grid.addLayout(button_row, url_row + 1, 0, 1, 6)
        detail_box.setMaximumHeight(190)
        edit_splitter.addWidget(detail_box)

        edit_splitter.setStretchFactor(0, 5)
        edit_splitter.setStretchFactor(1, 2)
        edit_splitter.setSizes([560, 170])
        layout.addWidget(edit_splitter, 1)

        edit_progress_row = QHBoxLayout()
        self._edit_progress = QProgressBar()
        self._edit_progress.setRange(0, 100)
        self._edit_progress.setValue(0)
        self._edit_progress.setTextVisible(True)
        edit_progress_row.addWidget(self._edit_progress, 1)
        self._lbl_edit_stats = QLabel("—")
        edit_progress_row.addWidget(self._lbl_edit_stats)
        layout.addLayout(edit_progress_row)

        self._view_edit.selectionModel().selectionChanged.connect(self.wnd_on_selection_changed)
        self._view_edit.setContextMenuPolicy(Qt.CustomContextMenu)
        self._view_edit.customContextMenuRequested.connect(self.wnd_show_table_context_menu)
        return tab

    def wnd_build_test_tab(self) -> QWidget:
        tab = QWidget()
        layout = QVBoxLayout(tab)
        layout.setContentsMargins(4, 4, 4, 4)
        layout.setSpacing(4)

        options_row = QHBoxLayout()
        options_row.setSpacing(6)
        options_row.addWidget(QLabel("范围："))
        self._combo_test_scope = QComboBox()
        self._combo_test_scope.addItems(["全部条目", "当前选中", "仅失败项", "仅未测试项",
                                         "仅缓存过期项", "忽略缓存全部重测"])
        self._combo_test_scope.setToolTip(
            "选择要检测的范围。“忽略缓存全部重测”会无视检测缓存，重新检测所有链接。")
        options_row.addWidget(self._combo_test_scope)

        options_row.addWidget(QLabel("并发："))
        self._spin_test_workers = QSpinBox()
        self._spin_test_workers.setRange(1, 64)
        self._spin_test_workers.setValue(self._config.cfg_get("probe/workers"))
        self._spin_test_workers.valueChanged.connect(
            lambda value: self._config.cfg_set("probe/workers", value))
        options_row.addWidget(self._spin_test_workers)

        options_row.addWidget(QLabel("超时(s)："))
        self._spin_test_timeout = QDoubleSpinBox()
        self._spin_test_timeout.setRange(0.5, 300.0)
        self._spin_test_timeout.setSingleStep(0.5)
        self._spin_test_timeout.setValue(self._config.cfg_get("probe/timeout"))
        self._spin_test_timeout.valueChanged.connect(
            lambda value: self._config.cfg_set("probe/timeout", value))
        options_row.addWidget(self._spin_test_timeout)

        options_row.addWidget(QLabel("重试："))
        self._spin_test_retries = QSpinBox()
        self._spin_test_retries.setRange(0, 5)
        self._spin_test_retries.setValue(self._config.cfg_get("probe/retries"))
        self._spin_test_retries.valueChanged.connect(
            lambda value: self._config.cfg_set("probe/retries", value))
        options_row.addWidget(self._spin_test_retries)

        self._chk_test_deep = QCheckBox("深度测试（判断是否有节目）")
        self._chk_test_deep.setChecked(self._config.cfg_get("probe/deep"))
        self._chk_test_deep.toggled.connect(lambda value: self._config.cfg_set("probe/deep", value))
        options_row.addWidget(self._chk_test_deep)

        self._chk_test_ssl = QCheckBox("忽略 SSL 错误")
        self._chk_test_ssl.setChecked(self._config.cfg_get("probe/ignore_ssl"))
        self._chk_test_ssl.toggled.connect(lambda value: self._config.cfg_set("probe/ignore_ssl", value))
        options_row.addWidget(self._chk_test_ssl)

        options_row.addStretch(1)
        layout.addLayout(options_row)

        button_row = QHBoxLayout()
        btn_start = QPushButton("开始测试")
        btn_start.setDefault(True)
        btn_start.clicked.connect(lambda: self.wnd_act_start_test("scope"))
        button_row.addWidget(btn_start)
        btn_selected = QPushButton("测试选中")
        btn_selected.clicked.connect(lambda: self.wnd_act_start_test("selected"))
        button_row.addWidget(btn_selected)
        self._btn_test_stop = QPushButton("停止")
        self._btn_test_stop.setEnabled(False)
        self._btn_test_stop.clicked.connect(self.wnd_act_stop_test)
        button_row.addWidget(self._btn_test_stop)
        btn_clear = QPushButton("清空测试结果")
        btn_clear.clicked.connect(self.wnd_act_clear_test_results)
        button_row.addWidget(btn_clear)
        btn_export = QPushButton("导出测试结果")
        btn_export.clicked.connect(self.wnd_act_export_test_results)
        button_row.addWidget(btn_export)
        btn_history = QPushButton("测试历史统计")
        btn_history.clicked.connect(self.wnd_act_show_test_history)
        button_row.addWidget(btn_history)

        self._chk_test_failed_only = QCheckBox("只看失败项")
        self._chk_test_failed_only.setChecked(self._config.cfg_get("ui/test_failed_only"))
        self._chk_test_failed_only.toggled.connect(self.wnd_on_test_failed_only_toggled)
        button_row.addWidget(self._chk_test_failed_only)
        button_row.addStretch(1)
        layout.addLayout(button_row)

        progress_row = QHBoxLayout()
        self._test_progress = QProgressBar()
        self._test_progress.setRange(0, 100)
        self._test_progress.setValue(0)
        progress_row.addWidget(self._test_progress, 1)
        self._lbl_test_summary = QLabel("就绪")
        progress_row.addWidget(self._lbl_test_summary)
        layout.addLayout(progress_row)

        cache_row = QHBoxLayout()
        cache_row.setSpacing(6)
        self._chk_test_skip_cached = QCheckBox("跳过有效缓存")
        self._chk_test_skip_cached.setChecked(self._config.cfg_get("cache/skip_fresh"))
        self._chk_test_skip_cached.setToolTip(
            "勾选后：已经检测过、且结果仍在“检测缓存有效期”内的链接会被直接跳过，不再重复检测。\n"
            "缓存有效期可在“设置 → 检测缓存”里调整（0 表示永久有效）。")
        self._chk_test_skip_cached.toggled.connect(
            lambda value: self._config.cfg_set("cache/skip_fresh", value))
        cache_row.addWidget(self._chk_test_skip_cached)

        btn_apply_cache = QPushButton("应用检测缓存")
        btn_apply_cache.setToolTip("把之前保存的检测结果套用到当前文件（不需要重新检测）")
        btn_apply_cache.clicked.connect(self.wnd_act_apply_probe_cache)
        cache_row.addWidget(btn_apply_cache)

        btn_clear_cache = QPushButton("清空检测缓存")
        btn_clear_cache.setToolTip("删除所有已保存的检测结果，下次测试将全部重新检测")
        btn_clear_cache.clicked.connect(self.wnd_act_clear_probe_cache)
        cache_row.addWidget(btn_clear_cache)

        self._lbl_test_cache_stats = QLabel("缓存：—")
        self._lbl_test_cache_stats.setStyleSheet("color:#5f6368;")
        cache_row.addWidget(self._lbl_test_cache_stats)
        cache_row.addStretch(1)
        layout.addLayout(cache_row)

        self._view_test = QTableView()
        self.wnd_configure_table_view(self._view_test)
        self._view_test.setModel(self._proxy_test)
        self._view_test.setSortingEnabled(True)
        self._view_test.sortByColumn(0, Qt.AscendingOrder)
        self._view_test.doubleClicked.connect(self.wnd_on_edit_view_double_clicked)
        self._view_test.setContextMenuPolicy(Qt.CustomContextMenu)
        self._view_test.customContextMenuRequested.connect(self.wnd_show_table_context_menu)
        layout.addWidget(self._view_test, 1)
        return tab

    def wnd_build_log_panel(self) -> QWidget:
        panel = QWidget()
        layout = QVBoxLayout(panel)
        layout.setContentsMargins(4, 2, 4, 2)
        layout.setSpacing(3)

        header = QHBoxLayout()
        header.addWidget(QLabel("运行日志"))
        self._chk_log_autoscroll = QCheckBox("自动滚动")
        self._chk_log_autoscroll.setChecked(self._config.cfg_get("ui/log_auto_scroll"))
        self._chk_log_autoscroll.toggled.connect(
            lambda value: self._config.cfg_set("ui/log_auto_scroll", value))
        header.addWidget(self._chk_log_autoscroll)
        header.addStretch(1)
        btn_clear = QPushButton("清空")
        btn_clear.clicked.connect(lambda: self._log_view.clear())
        header.addWidget(btn_clear)
        btn_save = QPushButton("保存日志")
        btn_save.clicked.connect(self.wnd_act_save_log)
        header.addWidget(btn_save)
        layout.addLayout(header)

        self._log_view = QPlainTextEdit()
        self._log_view.setReadOnly(True)
        self._log_view.setMaximumBlockCount(5000)
        self._log_view.setPlaceholderText("程序运行日志将显示在这里…")
        layout.addWidget(self._log_view, 1)
        return panel

    def wnd_build_statusbar(self) -> None:
        status = QStatusBar()
        self.setStatusBar(status)
        self._status_label = QLabel("就绪")
        status.addWidget(self._status_label, 1)
        self._status_counts = QLabel("—")
        status.addPermanentWidget(self._status_counts)
        self._status_progress = QProgressBar()
        self._status_progress.setRange(0, 100)
        self._status_progress.setValue(0)
        self._status_progress.setFixedWidth(220)
        self._status_progress.setTextVisible(True)
        status.addPermanentWidget(self._status_progress)

    def wnd_configure_table_view(self, view: QTableView) -> None:
        view.setSelectionBehavior(QAbstractItemView.SelectRows)
        view.setSelectionMode(QAbstractItemView.ExtendedSelection)
        view.setEditTriggers(QAbstractItemView.DoubleClicked | QAbstractItemView.EditKeyPressed
                             | QAbstractItemView.SelectedClicked)
        view.setAlternatingRowColors(True)
        view.setWordWrap(False)
        view.setSortingEnabled(False)
        view.verticalHeader().setVisible(False)
        view.setHorizontalScrollMode(QAbstractItemView.ScrollPerPixel)
        view.setVerticalScrollMode(QAbstractItemView.ScrollPerPixel)
        header = view.horizontalHeader()
        header.setStretchLastSection(True)
        header.setSectionsMovable(True)
        header.setContextMenuPolicy(Qt.CustomContextMenu)
        header.customContextMenuRequested.connect(
            lambda point, target=view: self.wnd_show_header_context_menu(target, point))

    # ------------------------------------------------------------------
    # 构建：菜单 / 工具栏
    # ------------------------------------------------------------------
    def wnd_build_menus(self) -> None:
        menubar = self.menuBar()

        file_menu = menubar.addMenu("文件(&F)")
        file_menu.addAction(self.qact_new_file)
        file_menu.addAction(self.qact_open_file)
        file_menu.addAction(self.qact_import_append)
        file_menu.addSeparator()
        file_menu.addAction(self.qact_save_file)
        file_menu.addAction(self.qact_save_file_as)
        file_menu.addSeparator()
        file_menu.addAction(self.qact_export_csv)
        file_menu.addAction(self.qact_export_m3u)
        file_menu.addAction(self.qact_backup_now)
        file_menu.addSeparator()
        self._recent_menu = file_menu.addMenu("最近打开")
        file_menu.addSeparator()
        file_menu.addAction(self.qact_exit)

        edit_menu = menubar.addMenu("编辑(&E)")
        edit_menu.addAction(self.qact_add_link)
        edit_menu.addAction(self.qact_batch_add)
        edit_menu.addAction(self.qact_edit_entry)
        edit_menu.addSeparator()
        edit_menu.addAction(self.qact_delete_selected)
        edit_menu.addAction(self.qact_batch_delete)
        edit_menu.addAction(self.qact_delete_all)
        edit_menu.addAction(self.qact_remove_duplicates)
        edit_menu.addSeparator()
        edit_menu.addAction(self.qact_batch_replace)
        edit_menu.addAction(self.qact_batch_group)
        edit_menu.addSeparator()
        edit_menu.addAction(self.qact_move_up)
        edit_menu.addAction(self.qact_move_down)
        edit_menu.addSeparator()
        edit_menu.addAction(self.qact_find_focus)

        view_menu = menubar.addMenu("视图(&V)")
        view_menu.addAction(self.qact_columns_edit)
        view_menu.addAction(self.qact_columns_test)
        view_menu.addSeparator()
        view_menu.addAction(self.qact_columns_reset)
        view_menu.addAction(self.qact_columns_fit)

        test_menu = menubar.addMenu("测试(&T)")
        test_menu.addAction(self.qact_test_all)
        test_menu.addAction(self.qact_test_selected)
        test_menu.addAction(self.qact_test_failed)
        test_menu.addAction(self.qact_test_untested)
        test_menu.addSeparator()
        test_menu.addAction(self.qact_test_stop)
        test_menu.addAction(self.qact_test_force_all)
        test_menu.addAction(self.qact_clear_test_results)
        test_menu.addSeparator()
        test_menu.addAction(self.qact_apply_probe_cache)
        test_menu.addAction(self.qact_clear_probe_cache)

        tools_menu = menubar.addMenu("工具(&O)")
        tools_menu.addAction(self.qact_id_scan)
        tools_menu.addAction(self.qact_diff_analysis)
        tools_menu.addAction(self.qact_index_map)
        tools_menu.addAction(self.qact_sync_ids)
        tools_menu.addAction(self.qact_match_logos)
        tools_menu.addSeparator()
        tools_menu.addAction(self.qact_open_in_player)
        tools_menu.addAction(self.qact_open_in_html5)
        tools_menu.addAction(self.qact_open_in_browser)
        tools_menu.addAction(self.qact_copy_url)
        tools_menu.addSeparator()
        tools_menu.addAction(self.qact_open_program_dir)
        tools_menu.addAction(self.qact_open_data_dir)
        tools_menu.addAction(self.qact_open_env_file)

        help_menu = menubar.addMenu("帮助(&H)")
        help_menu.addAction(self.qact_show_help)
        help_menu.addAction(self.qact_check_icon)
        help_menu.addAction(self.qact_show_about)

    def wnd_build_toolbar(self) -> None:
        toolbar = QToolBar("主工具栏")
        toolbar.setObjectName("M3ULE_MAIN_TOOLBAR")
        toolbar.setMovable(False)
        toolbar.setIconSize(QSize(18, 18))
        toolbar.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        style = self.style()

        def add(action, standard_icon=None):
            if standard_icon is not None:
                action.setIcon(style.standardIcon(standard_icon))
            toolbar.addAction(action)

        add(self.qact_open_file, QStyle.SP_DialogOpenButton)
        add(self.qact_save_file, QStyle.SP_DialogSaveButton)
        toolbar.addSeparator()
        add(self.qact_add_link, QStyle.SP_FileDialogNewFolder)
        add(self.qact_batch_add)
        add(self.qact_batch_group)
        add(self.qact_delete_selected, QStyle.SP_TrashIcon)
        toolbar.addSeparator()
        add(self.qact_test_all, QStyle.SP_MediaPlay)
        add(self.qact_test_selected)
        add(self.qact_test_stop, QStyle.SP_MediaStop)
        toolbar.addSeparator()
        add(self.qact_open_in_player)
        add(self.qact_show_help, QStyle.SP_DialogHelpButton)
        self.addToolBar(toolbar)

    # ==================================================================
    # 状态 / 外观
    # ==================================================================
    def wnd_append_log(self, message: str) -> None:
        timestamp = datetime.now().strftime("%H:%M:%S")
        line = f"[{timestamp}] {message}"
        self._log_view.appendPlainText(line)
        if self._chk_log_autoscroll.isChecked():
            self._log_view.moveCursor(QTextCursor.End)
        if self._config.cfg_get("log/to_file"):
            try:
                log_path = os.path.join(
                    m3ule_get_log_dir(), f"m3u_live_editor_{datetime.now():%Y%m%d}.log")
                with open(log_path, "a", encoding="utf-8") as handle:
                    handle.write(line + "\n")
            except OSError:
                pass

    def wnd_set_progress(self, value: int, maximum: int, text: str = "") -> None:
        self._status_progress.setRange(0, max(1, maximum))
        self._status_progress.setValue(value)
        if text:
            self._status_label.setText(text)

    @Slot()
    def wnd_update_title(self) -> None:
        mark = " *" if self._document.modified else ""
        name = os.path.basename(self._document.path) if self._document.path else "未命名"
        self.setWindowTitle(f"{M3ULE_WINDOW_TITLE} — {name}{mark}")

    @Slot()
    def wnd_mark_modified(self) -> None:
        self._document.modified = True
        self.wnd_update_title()

    @Slot()
    def wnd_update_counts(self) -> None:
        stats = self._document.doc_statistics()
        entries = self._document.entries
        tested = sum(1 for entry in entries if entry.test_state)
        ok_count = sum(1 for entry in entries if entry.test_state == M3ULE_STATUS_OK)
        bad_count = sum(1 for entry in entries if entry.test_state in
                        (M3ULE_STATUS_FAIL, M3ULE_STATUS_TIMEOUT, M3ULE_STATUS_ERROR))
        cached = sum(1 for entry in entries if entry.test_cached)
        tested_text = f"已测 {tested}" + (f"（缓存 {cached}）" if cached else "")
        self._status_counts.setText(
            f"共 {stats['entries']} 条 · 分组 {stats['groups']} · {tested_text} · "
            f"可用 {ok_count} · 异常 {bad_count}")
        self._lbl_edit_stats.setText(
            f"共 {stats['entries']} 条 · 分组 {stats['groups']} · 唯一链接 {stats['unique_urls']}")
        self._model_count_cache = stats["entries"]
        self.wnd_refresh_cache_stats()

    @Slot()
    def wnd_apply_appearance(self) -> None:
        font_size = self._config.cfg_get("ui/font_size")
        row_height = self._config.cfg_get("ui/table_row_height")
        theme = self._config.cfg_get("ui/theme")
        font = QFont(self.font())
        font.setPointSize(int(font_size))
        QApplication.instance().setFont(font)
        for view in (self._view_edit, self._view_test):
            view.verticalHeader().setDefaultSectionSize(int(row_height))
        self._apply_view_column_widths(self._view_edit)
        self._apply_view_column_widths(self._view_test)
        if theme == "深色":
            QApplication.instance().setStyleSheet(M3ULE_DARK_STYLESHEET)
        else:
            QApplication.instance().setStyleSheet("")

    def wnd_apply_font_size(self, size: int) -> None:
        self._config.cfg_set("ui/font_size", int(size))
        self.wnd_apply_appearance()

    def wnd_apply_theme(self, theme: str) -> None:
        self._config.cfg_set("ui/theme", theme)
        self.wnd_apply_appearance()

    def wnd_reset_layout(self) -> None:
        self._main_splitter.setSizes([720, 180])
        self._edit_splitter.setSizes([560, 170])
        self.showMaximized() if self.isMaximized() else self.resize(1440, 860)
        self._tabs.setCurrentIndex(0)

    # ==================================================================
    # 表格 / 详情 / 筛选
    # ==================================================================
    def wnd_active_table_view(self) -> QTableView:
        if self._tabs.currentWidget() is self._tab_test:
            return self._view_test
        return self._view_edit

    def wnd_selected_entries(self) -> list:
        view = self.wnd_active_table_view()
        model = view.model()
        selection = view.selectionModel()
        if selection is None:
            return []
        rows = sorted({index.row() for index in selection.selectedRows()})
        if not rows:
            rows = sorted({index.row() for index in selection.selectedIndexes()})
        entries = []
        seen: set = set()
        for row in rows:
            source_index = model.mapToSource(model.index(row, 0)) \
                if isinstance(model, QSortFilterProxyModel) else model.index(row, 0)
            entry = self._model.mdl_entry_at(source_index.row())
            if entry is not None and entry.uid not in seen:
                seen.add(entry.uid)
                entries.append(entry)
        return entries

    def wnd_visible_entries(self) -> list:
        """当前表格视图里可见的全部条目（已按筛选与排序）——用于整表播放/切换频道。"""
        view = self.wnd_active_table_view()
        model = view.model()
        if model is None:
            return []
        entries = []
        for row in range(model.rowCount()):
            source_index = model.mapToSource(model.index(row, 0)) \
                if isinstance(model, QSortFilterProxyModel) else model.index(row, 0)
            entry = self._model.mdl_entry_at(source_index.row())
            if entry is not None:
                entries.append(entry)
        return entries

    def wnd_selected_uids(self) -> list:
        return [entry.uid for entry in self.wnd_selected_entries()]

    @Slot()
    def wnd_on_selection_changed(self, *_args) -> None:
        entries = self.wnd_selected_entries()
        self._detail_updating = True
        if not entries:
            for editor in self._detail_editors.values():
                editor.clear()
            self._lbl_detail_info.setText("未选中")
            self._detail_updating = False
            return
        entry = entries[0]
        self._detail_editors["name"].setText(entry.title or "")
        self._detail_editors["tvg-name"].setText(entry.entry_get_attr("tvg-name"))
        self._detail_editors["group-title"].setText(entry.entry_get_attr("group-title"))
        self._detail_editors["tvg-id"].setText(entry.entry_get_attr("tvg-id"))
        self._detail_editors["channelID"].setText(entry.entry_get_attr("channelID"))
        self._detail_editors["tvg-chno"].setText(entry.entry_get_attr("tvg-chno"))
        self._detail_editors["tvg-logo"].setText(entry.entry_get_attr("tvg-logo"))
        self._detail_editors["duration"].setText(entry.duration or "0")
        self._detail_editors["remark"].setText(entry.remark or "")
        self._detail_url_editor.setText(entry.url or "")
        state = entry.test_state or "未测试"
        info = f"已选中 {len(entries)} 条 · 状态：{state}"
        if entry.test_cached:
            info += f"（缓存 · {m3ule_probe_cache_age_text(entry.test_ts)}）"
        if entry.test_ms and entry.test_ms >= 0:
            info += f" · {entry.test_ms}ms"
        if entry.test_ts:
            info += f" · 检测于 {entry.test_ts}"
        self._lbl_detail_info.setText(info)
        self._detail_updating = False

    @Slot()
    def wnd_apply_detail_fields(self) -> None:
        if self._detail_updating:
            return
        entries = self.wnd_selected_entries()
        if not entries:
            return
        entry = entries[0]
        entry.title = self._detail_editors["name"].text()
        for key in ("tvg-name", "group-title", "tvg-id", "channelID", "tvg-chno", "tvg-logo"):
            value = self._detail_editors[key].text().strip()
            if value:
                entry.attrs[key] = value
            elif key in entry.attrs:
                del entry.attrs[key]
        entry.duration = self._detail_editors["duration"].text().strip() or "0"
        entry.remark = self._detail_editors["remark"].text()
        new_url = self._detail_url_editor.text().strip()
        if new_url != (entry.url or ""):
            entry.entry_invalidate_test_if_url_changed(new_url)
        entry.url = new_url
        entry.entry_rebuild_extinf_line()
        self._model.mdl_notify_uid_changed(entry.uid)
        self.wnd_mark_modified()
        self.wnd_update_counts()

    @Slot()
    def wnd_on_model_entry_edited(self, uid: int) -> None:
        self.wnd_mark_modified()
        self.wnd_update_counts()
        self._schedule_save_runtime_settings()

    @Slot()
    def wnd_refresh_filter(self) -> None:
        keyword = self._edit_filter_keyword.text()
        group = self._combo_filter_group.currentData() or ""
        state_text = self._combo_filter_state.currentText()
        state = ""
        if state_text == "未测试":
            state = M3ULE_STATUS_NONE
        elif state_text != "全部":
            state = state_text
        failed_only = self._chk_filter_failed.isChecked()
        self._proxy_edit.prx_set_filters(keyword, group, state, failed_only, False)
        self._proxy_test.prx_set_filters("", "", "", self._chk_test_failed_only.isChecked(), False)
        self._lbl_detail_info.setText(
            f"筛选后 {self._proxy_edit.rowCount()} / {self._model.rowCount()} 条")

    @Slot()
    def wnd_act_clear_filter(self) -> None:
        self._edit_filter_keyword.clear()
        self._combo_filter_group.setCurrentIndex(0)
        self._combo_filter_state.setCurrentIndex(0)
        self._chk_filter_failed.setChecked(False)
        self.wnd_refresh_filter()

    @Slot()
    def wnd_rebuild_group_filter(self) -> None:
        current = self._combo_filter_group.currentData() or ""
        self._combo_filter_group.blockSignals(True)
        self._combo_filter_group.clear()
        self._combo_filter_group.addItem("全部分组", "")
        for name in self._document.doc_group_names():
            self._combo_filter_group.addItem(name, name)
        index = self._combo_filter_group.findData(current)
        self._combo_filter_group.setCurrentIndex(index if index >= 0 else 0)
        self._combo_filter_group.blockSignals(False)
        self.wnd_refresh_filter()

    @Slot(bool)
    def wnd_on_test_failed_only_toggled(self, checked: bool) -> None:
        self._config.cfg_set("ui/test_failed_only", checked)
        self.wnd_refresh_filter()

    @Slot(QModelIndex)
    def wnd_on_edit_view_double_clicked(self, index: QModelIndex) -> None:
        view = self.sender()
        model = view.model() if view is not None else None
        if model is None:
            return
        source_index = model.mapToSource(index) if isinstance(model, QSortFilterProxyModel) else index
        entry = self._model.mdl_entry_at(source_index.row())
        if entry is None:
            return
        column_key = self._model.mdl_column_keys()[source_index.column()]
        if column_key == "url":
            self.wnd_open_url_with_player(entry.url or "")
        else:
            self.wnd_act_edit_entry()

    def wnd_show_table_context_menu(self, position: QPoint) -> None:
        view = self.sender()
        if view is None:
            return
        menu = QMenu(self)
        menu.addAction(self.qact_edit_entry)
        menu.addAction(self.qact_add_link)
        menu.addAction(self.qact_batch_add)
        menu.addAction(self.qact_batch_group)
        menu.addMenu(self.wnd_build_group_quick_menu())
        menu.addAction(self.qact_match_logos)
        menu.addSeparator()
        menu.addAction(self.qact_delete_selected)
        menu.addAction(self.qact_batch_delete)
        menu.addSeparator()
        menu.addAction(self.qact_open_in_player)
        menu.addAction(self.qact_open_in_html5)
        menu.addAction(self.qact_open_in_browser)
        menu.addAction(self.qact_copy_url)
        menu.addSeparator()
        menu.addAction(self.qact_test_selected)
        menu.addAction(self.qact_clear_selected_cache)
        menu.addAction(self.qact_move_up)
        menu.addAction(self.qact_move_down)
        menu.exec(view.viewport().mapToGlobal(position))

    def wnd_show_header_context_menu(self, view: QTableView, position: QPoint) -> None:
        header = view.horizontalHeader()
        menu = QMenu(self)
        columns = self._model.mdl_columns()
        for index, column in enumerate(columns):
            action = QAction(column["title"], menu)
            action.setCheckable(True)
            action.setChecked(not header.isSectionHidden(index))
            action.toggled.connect(
                lambda checked, column_index=index, target=view: self.wnd_set_column_visible(
                    target, column_index, checked))
            menu.addAction(action)
        menu.addSeparator()
        action_choose = menu.addAction("自定义列…")
        action_choose.triggered.connect(lambda _checked=False, target=view: self.wnd_act_choose_columns(target))
        action_reset = menu.addAction("恢复默认列（全部显示）")
        action_reset.triggered.connect(lambda _checked=False, target=view: self.wnd_act_reset_columns(target))
        action_fit = menu.addAction("适应内容宽度")
        action_fit.triggered.connect(lambda: view.resizeColumnsToContents())
        menu.exec(header.mapToGlobal(position))

    # -- 列自定义（显示哪些列 / 顺序，按表分别记忆）-------------------------
    def wnd_table_view_mode(self, view: QTableView) -> str:
        return "test" if view is self._view_test else "edit"

    def wnd_table_view_title(self, view: QTableView) -> str:
        return "链接测试" if view is self._view_test else "文件编辑"

    def wnd_column_layout_key(self, view: QTableView) -> str:
        return M3ULE_COLUMN_LAYOUT_KEYS[self.wnd_table_view_mode(view)]

    def wnd_set_column_visible(self, view: QTableView, column_index: int, visible: bool) -> None:
        view.setColumnHidden(column_index, not visible)
        self.wnd_save_column_layouts()

    def wnd_capture_column_layout(self, view: QTableView) -> dict:
        """把当前「列顺序 + 显示哪些列」读出来（按列 key，新增列不会错位）。"""
        columns = self._model.mdl_columns()
        header = view.horizontalHeader()
        order = []
        for visual in range(header.count()):
            logical = header.logicalIndex(visual)
            if 0 <= logical < len(columns):
                order.append(columns[logical]["key"])
        visible = [key for key in order
                   if not header.isSectionHidden(
                       [column["key"] for column in columns].index(key))]
        return {"order": order, "visible": visible}

    def wnd_apply_column_layout(self, view: QTableView, layout: dict) -> None:
        """套用「列顺序 + 显示哪些列」（缺失的列按源码顺序补上并显示）。"""
        columns = self._model.mdl_columns()
        keys = [column["key"] for column in columns]
        header = view.horizontalHeader()
        order = [key for key in (layout.get("order") or []) if key in keys]
        for key in keys:
            if key not in order:
                order.append(key)
        visible = layout.get("visible")
        visible = [key for key in visible if key in keys] if visible is not None else list(keys)
        if not visible:
            visible = [keys[0]] if keys else []      # 至少留一列，避免整表空白
        header.setUpdatesEnabled(False)
        for position, key in enumerate(order):
            logical = keys.index(key)
            current = header.visualIndex(logical)
            if current != position:
                header.moveSection(current, position)
        for index, key in enumerate(keys):
            view.setColumnHidden(index, key not in visible)
        header.setUpdatesEnabled(True)

    def wnd_save_column_layouts(self) -> None:
        for view in (self._view_edit, self._view_test):
            self._config.cfg_set(self.wnd_column_layout_key(view),
                                 json.dumps(self.wnd_capture_column_layout(view),
                                            ensure_ascii=False))

    def wnd_restore_column_layouts(self) -> None:
        for view in (self._view_edit, self._view_test):
            raw = str(self._config.cfg_get(self.wnd_column_layout_key(view), "") or "")
            if not raw:
                continue
            try:
                layout = json.loads(raw)
            except (ValueError, TypeError):
                continue
            if isinstance(layout, dict):
                self.wnd_apply_column_layout(view, layout)

    def wnd_current_column_layout(self, view: QTableView) -> dict:
        """当前布局；没有存过就用「全部列、源码顺序」。"""
        keys = [column["key"] for column in self._model.mdl_columns()]
        raw = str(self._config.cfg_get(self.wnd_column_layout_key(view), "") or "")
        if raw:
            try:
                layout = json.loads(raw)
            except (ValueError, TypeError):
                layout = None
            if isinstance(layout, dict) and layout.get("order"):
                return layout
        return {"order": list(keys), "visible": list(keys)}

    def wnd_act_choose_columns(self, view: QTableView = None) -> bool:
        """打开「自定义列」对话框（不传 view 时对当前显示的那张表操作）。"""
        target = view if view is not None else self.wnd_active_table_view()
        layout = self.wnd_current_column_layout(target)
        dialog = M3ULiveEditorColumnChooserDialog(
            self._model.mdl_columns(), layout.get("visible"), layout.get("order"),
            self.wnd_table_view_title(target), self)
        if dialog.exec() != QDialog.Accepted:
            return False
        chosen = dialog.dlg_layout()
        self.wnd_apply_column_layout(target, chosen)
        self.wnd_save_column_layouts()
        hidden = [column["title"] for column in self._model.mdl_columns()
                  if column["key"] not in chosen["visible"]]
        self.wnd_append_log(
            f"{self.wnd_table_view_title(target)}列已更新：显示 {len(chosen['visible'])} 列"
            + (f"，隐藏 {'、'.join(hidden)}" if hidden else "（全部显示）"))
        return True

    def wnd_act_reset_columns(self, view: QTableView = None) -> None:
        target = view if view is not None else self.wnd_active_table_view()
        keys = [column["key"] for column in self._model.mdl_columns()]
        self.wnd_apply_column_layout(target, {"order": list(keys), "visible": list(keys)})
        self.wnd_save_column_layouts()
        self.wnd_append_log(f"{self.wnd_table_view_title(target)}列已恢复默认（全部显示）。")

    # ==================================================================
    # 文件操作
    # ==================================================================
    def wnd_confirm_discard_changes(self) -> bool:
        if not self._document.modified:
            return True
        reply = QMessageBox.question(
            self, "未保存的修改",
            "当前文件有未保存的修改，是否先保存？",
            QMessageBox.Save | QMessageBox.Discard | QMessageBox.Cancel, QMessageBox.Save)
        if reply == QMessageBox.Cancel:
            return False
        if reply == QMessageBox.Save:
            return self.wnd_act_save_file()
        return True

    @Slot()
    def wnd_act_new_file(self) -> None:
        if not self.wnd_confirm_discard_changes():
            return
        self._document.doc_clear()
        self._model.mdl_refresh_all()
        self.wnd_reset_edit_sort()
        self.wnd_rebuild_group_filter()
        self.wnd_update_title()
        self.wnd_update_counts()
        self.wnd_append_log("已新建空白 m3u 文件。")

    @Slot()
    def wnd_act_open_file(self) -> None:
        if not self.wnd_confirm_discard_changes():
            return
        last_dir = self._config.cfg_get("io/last_open_dir")
        path, _ = QFileDialog.getOpenFileName(
            self, "打开 m3u / m3u8 文件", last_dir,
            "播放列表 (*.m3u *.m3u8 *.txt);;所有文件 (*.*)")
        if path:
            self.wnd_open_path(path)

    def wnd_open_path(self, path: str) -> None:
        try:
            self.wnd_set_progress(10, 100, f"正在加载 {os.path.basename(path)} …")
            QApplication.processEvents()
            encoding = self._document.doc_load_from_path(
                path, progress=lambda value, text: self.wnd_set_progress(value, 100, text))
            self._model.mdl_refresh_all()
            self.wnd_reset_edit_sort()
            self.wnd_rebuild_group_filter()
            self.wnd_update_title()
            self.wnd_update_counts()
            self._config.cfg_set("io/last_open_dir", os.path.dirname(path))
            self._config.cfg_set("io/last_file", path)
            self.wnd_push_recent_file(path)
            self.wnd_set_progress(100, 100, "加载完成")
            self.wnd_append_log(
                f"已打开：{path}（编码 {encoding}，{len(self._document.entries)} 条频道）")
            if self.wnd_probe_cache_enabled() and self._config.cfg_get("cache/auto_apply"):
                self.wnd_apply_probe_cache(f"打开 {os.path.basename(path)}")
            self.wnd_refresh_cache_stats()
            self._tab_settings.stt_refresh_display_paths()
        except Exception as exc:  # noqa: BLE001
            self.wnd_set_progress(0, 100, "加载失败")
            self.wnd_append_log(f"打开失败：{type(exc).__name__}: {exc}\n{traceback.format_exc()}")
            QMessageBox.critical(self, "打开失败", f"{type(exc).__name__}: {exc}")

    def wnd_auto_open_last_file(self) -> bool:
        """启动时自动恢复上次打开的文件（可在「设置 → 文件与备份」关闭）。

        命令行给了文件参数时不会走到这里；文件不存在只写日志，不弹窗打断启动。
        """
        if not self._config.cfg_get("io/auto_open_last", True):
            return False
        path = str(self._config.cfg_get("io/last_file", "") or "").strip()
        if not path:
            return False
        if not os.path.isfile(path):
            self.wnd_append_log(
                f"上次打开的文件已不存在，未自动打开：{path}"
                "（可在「设置 → 文件与备份」关闭自动打开）")
            return False
        self.wnd_append_log(f"自动恢复上次打开的文件：{path}")
        self.wnd_open_path(path)
        return True

    def wnd_restart_application(self) -> bool:
        """用当前设置重新启动程序（渲染方式等启动参数只有重启才生效）。"""
        if not self.wnd_confirm_discard_changes():
            return False
        self.wnd_save_runtime_settings()
        if getattr(sys, "frozen", False):
            program, arguments = sys.executable, list(sys.argv[1:])
        else:
            program = sys.executable
            arguments = [os.path.abspath(sys.argv[0])] + list(sys.argv[1:])
        try:
            started = QProcess.startDetached(program, arguments, os.getcwd())
        except Exception as exc:  # noqa: BLE001
            QMessageBox.warning(self, "重启失败", f"{type(exc).__name__}: {exc}")
            return False
        if not started:
            QMessageBox.warning(
                self, "重启失败",
                "无法启动新进程，请手动关闭本程序后重新双击启动。")
            return False
        self.wnd_append_log("正在重启程序以使新的启动参数生效…")
        self.close()
        return True

    # ==================================================================
    # 文件导入 / 保存
    # ==================================================================
    def wnd_act_import_append(self) -> None:
        last_dir = self._config.cfg_get("io/last_open_dir")
        path, _ = QFileDialog.getOpenFileName(
            self, "追加导入 m3u / m3u8 文件", last_dir,
            "播放列表 (*.m3u *.m3u8 *.txt);;所有文件 (*.*)")
        if not path:
            return
        try:
            temp_document = M3ULiveEditorDocument()
            temp_document.doc_load_from_path(path)
        except Exception as exc:  # noqa: BLE001
            QMessageBox.warning(self, "导入失败", f"{type(exc).__name__}: {exc}")
            return
        entries = temp_document.entries
        if not entries:
            QMessageBox.information(self, "提示", "该文件没有可导入的频道条目。")
            return
        if not self._document.header_lines and temp_document.header_lines:
            self._document.header_lines = list(temp_document.header_lines)
        self._document.doc_insert_entries(entries)
        self._model.mdl_notify_structural_change()
        self.wnd_reset_edit_sort()
        self.wnd_rebuild_group_filter()
        self.wnd_mark_modified()
        self.wnd_update_counts()
        self.wnd_append_log(f"已从 {os.path.basename(path)} 追加导入 {len(entries)} 条频道。")
        if self.wnd_probe_cache_enabled() and self._config.cfg_get("cache/auto_apply"):
            self.wnd_apply_probe_cache(f"追加导入 {os.path.basename(path)}",
                                       uids=[entry.uid for entry in entries])

    @Slot()
    def wnd_act_save_file(self) -> bool:
        if not self._document.path:
            return self.wnd_act_save_file_as()
        return self.wnd_save_to_path(self._document.path)

    @Slot()
    def wnd_act_save_file_as(self) -> bool:
        last_dir = self._config.cfg_get("io/last_save_dir") or self._config.cfg_get("io/last_open_dir")
        default_name = os.path.basename(self._document.path) if self._document.path else "直播源.m3u"
        path, _ = QFileDialog.getSaveFileName(
            self, "另存为", os.path.join(last_dir, default_name),
            "播放列表 (*.m3u *.m3u8);;所有文件 (*.*)")
        if not path:
            return False
        return self.wnd_save_to_path(path)

    def wnd_save_to_path(self, path: str) -> bool:
        try:
            if (self._config.cfg_get("io/auto_backup_on_save")
                    and os.path.isfile(path)):
                self.wnd_backup_file(path)
            self.wnd_set_progress(10, 100, "正在保存…")
            QApplication.processEvents()
            self._document.doc_save_to_path(
                path, progress=lambda value, text: self.wnd_set_progress(value, 100, text))
            self._model.mdl_refresh_all()
            self.wnd_update_title()
            self._config.cfg_set("io/last_save_dir", os.path.dirname(path))
            self.wnd_push_recent_file(path)
            self.wnd_set_progress(100, 100, "保存完成")
            self.wnd_append_log(f"已保存：{path}")
            self._tab_settings.stt_refresh_display_paths()
            return True
        except Exception as exc:  # noqa: BLE001
            self.wnd_set_progress(0, 100, "保存失败")
            self.wnd_append_log(f"保存失败：{type(exc).__name__}: {exc}\n{traceback.format_exc()}")
            QMessageBox.critical(self, "保存失败", f"{type(exc).__name__}: {exc}")
            return False

    def wnd_backup_file(self, path: str) -> str:
        try:
            backup_dir = m3ule_get_backup_dir()
            stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            name = os.path.splitext(os.path.basename(path))[0]
            target = os.path.join(backup_dir, f"{name}_{stamp}{os.path.splitext(path)[1]}")
            shutil.copy2(path, target)
            self.wnd_trim_backups(name)
            return target
        except Exception as exc:  # noqa: BLE001
            self.wnd_append_log(f"备份失败（不影响保存）：{exc}")
            return ""

    def wnd_trim_backups(self, name_prefix: str) -> None:
        keep = max(1, m3ule_safe_int(self._config.cfg_get("io/backup_keep"), 30))
        backup_dir = m3ule_get_backup_dir()
        try:
            files = [os.path.join(backup_dir, item) for item in os.listdir(backup_dir)
                     if item.startswith(name_prefix + "_")]
            files.sort(key=lambda item: os.path.getmtime(item), reverse=True)
            for stale in files[keep:]:
                try:
                    os.remove(stale)
                except OSError:
                    pass
        except OSError:
            pass

    @Slot()
    def wnd_act_backup_now(self) -> None:
        if not self._document.path or not os.path.isfile(self._document.path):
            QMessageBox.information(self, "提示", "当前文件尚未保存到磁盘，无法备份。")
            return
        target = self.wnd_backup_file(self._document.path)
        if target:
            self.wnd_append_log(f"已备份到：{target}")
            QMessageBox.information(self, "完成", f"已备份到：\n{target}")

    @Slot()
    def wnd_act_export_csv(self) -> None:
        if not self._document.entries:
            QMessageBox.information(self, "提示", "当前没有可导出的频道。")
            return
        last_dir = self._config.cfg_get("io/last_save_dir")
        path, _ = QFileDialog.getSaveFileName(
            self, "导出 CSV", os.path.join(last_dir, "频道列表.csv"), "CSV 文件 (*.csv)")
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8-sig", newline="") as handle:
                writer = csv.writer(handle)
                writer.writerow(["序号", "频道名称", "tvg名称", "分组", "tvg-id", "channelID",
                                 "频道号", "时长", "状态", "对比上次", "耗时(ms)", "检测时间",
                                 "码率(kbps)", "延迟(s)", "流ID", "详情",
                                 "备注", "链接"])
                for position, entry in enumerate(self._document.entries, start=1):
                    writer.writerow([
                        position, entry.title, entry.entry_get_attr("tvg-name"),
                        entry.entry_get_attr("group-title"), entry.entry_get_attr("tvg-id"),
                        entry.entry_get_attr("channelID"), entry.entry_get_attr("tvg-chno"),
                        entry.duration, entry.test_state, entry.entry_delta_label(),
                        entry.test_ms, entry.test_ts,
                        entry.test_kbps if entry.test_kbps > 0 else "",
                        entry.test_delay if entry.test_delay >= 0 else "",
                        entry.test_stream_id, entry.test_detail,
                        entry.remark, entry.url or ""])
        except OSError as exc:
            QMessageBox.warning(self, "导出失败", str(exc))
            return
        self._config.cfg_set("io/last_save_dir", os.path.dirname(path))
        self.wnd_append_log(f"已导出 CSV：{path}")
        QMessageBox.information(self, "完成", f"已导出 {len(self._document.entries)} 条到：\n{path}")

    @Slot()
    def wnd_act_export_m3u(self) -> None:
        if not self._document.entries:
            QMessageBox.information(self, "提示", "当前没有可导出的频道。")
            return
        last_dir = self._config.cfg_get("io/last_save_dir")
        path, _ = QFileDialog.getSaveFileName(
            self, "导出 M3U", os.path.join(last_dir, "导出.m3u"), "播放列表 (*.m3u *.m3u8)")
        if not path:
            return
        try:
            text = self._document.doc_serialize_text()
            with open(path, "wb") as handle:
                handle.write(self._document.doc_encode_text(text))
        except OSError as exc:
            QMessageBox.warning(self, "导出失败", str(exc))
            return
        self._config.cfg_set("io/last_save_dir", os.path.dirname(path))
        self.wnd_append_log(f"已导出 M3U：{path}")

    @Slot()
    def wnd_act_export_test_results(self) -> None:
        rows = [entry for entry in self._document.entries if entry.test_state]
        if not rows:
            QMessageBox.information(self, "提示", "还没有测试结果可导出。")
            return
        last_dir = self._config.cfg_get("io/last_save_dir")
        path, _ = QFileDialog.getSaveFileName(
            self, "导出测试结果", os.path.join(last_dir, "测试结果.csv"), "CSV 文件 (*.csv)")
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8-sig", newline="") as handle:
                writer = csv.writer(handle)
                writer.writerow(["频道名称", "状态", "HTTP", "耗时(ms)", "分片数",
                                 "码率(kbps)", "延迟(s)", "流ID", "详情",
                                 "检测时间", "来源", "链接"])
                for entry in rows:
                    writer.writerow([entry.entry_effective_name(), entry.test_state, entry.test_http,
                                     entry.test_ms, entry.test_seg,
                                     entry.test_kbps if entry.test_kbps > 0 else "",
                                     entry.test_delay if entry.test_delay >= 0 else "",
                                     entry.test_stream_id, entry.test_detail,
                                     entry.test_ts,
                                     "检测缓存" if entry.test_cached else "本次运行",
                                     entry.url or ""])
        except OSError as exc:
            QMessageBox.warning(self, "导出失败", str(exc))
            return
        self.wnd_append_log(f"已导出测试结果：{path}（{len(rows)} 条）")

    # ==================================================================
    # 最近打开
    # ==================================================================
    def wnd_push_recent_file(self, path: str) -> None:
        path = os.path.abspath(path)
        self._recent_files = [item for item in self._recent_files if item != path]
        self._recent_files.insert(0, path)
        self._recent_files = self._recent_files[:15]
        self._config.cfg_set(self.M3ULE_RECENT_KEY, json.dumps(self._recent_files, ensure_ascii=False))
        self.wnd_rebuild_recent_menu()

    def wnd_rebuild_recent_menu(self) -> None:
        if not hasattr(self, "_recent_menu"):
            return
        self._recent_menu.clear()
        if not self._recent_files:
            action = self._recent_menu.addAction("（暂无记录）")
            action.setEnabled(False)
            return
        for path in self._recent_files:
            action = QAction(os.path.basename(path), self)
            action.setToolTip(path)
            action.triggered.connect(lambda _checked=False, target=path: self.wnd_open_recent(target))
            self._recent_menu.addAction(action)
        self._recent_menu.addSeparator()
        clear_action = self._recent_menu.addAction("清空记录")
        clear_action.triggered.connect(self.wnd_act_clear_recent)

    def wnd_open_recent(self, path: str) -> None:
        if not os.path.isfile(path):
            QMessageBox.warning(self, "提示", f"文件不存在：\n{path}")
            return
        if not self.wnd_confirm_discard_changes():
            return
        self.wnd_open_path(path)

    @Slot()
    def wnd_act_clear_recent(self) -> None:
        self._recent_files = []
        self._config.cfg_set(self.M3ULE_RECENT_KEY, "[]")
        self.wnd_rebuild_recent_menu()

    # ==================================================================
    # 编辑操作
    # ==================================================================
    @Slot()
    def wnd_act_add_link(self) -> None:
        dialog = M3ULiveEditorLinkEditDialog("添加链接", entry=None, parent=self)
        if dialog.exec() != QDialog.Accepted:
            return
        entry = dialog.dlg_build_entry()
        if not (entry.url or "").strip():
            QMessageBox.warning(self, "提示", "链接不能为空。")
            return
        if not entry.entry_get_attr("group-title"):
            group = self._combo_filter_group.currentData()
            if group:
                entry.entry_set_attr("group-title", group)
        self._document.doc_insert_entries([entry])
        self._model.mdl_notify_structural_change()
        self.wnd_rebuild_group_filter()
        self.wnd_mark_modified()
        self.wnd_update_counts()
        self.wnd_append_log(f"已添加频道：{entry.entry_effective_name() or entry.url}")
        if self.wnd_probe_cache_enabled() and self._config.cfg_get("cache/auto_apply"):
            self.wnd_apply_probe_cache("新增链接", uids=[entry.uid])

    @Slot()
    def wnd_act_batch_add(self) -> None:
        existing = {(entry.url or "").strip() for entry in self._document.entries}
        dialog = M3ULiveEditorBatchAddDialog(
            existing_urls=existing, group_names=self._document.doc_group_names(), parent=self)
        if dialog.exec() != QDialog.Accepted:
            return
        entries = dialog.dlg_result_entries()
        if not entries:
            return
        start_row = self._model.rowCount()
        self._document.doc_insert_entries(entries)
        self._model.mdl_notify_structural_change()
        self.wnd_rebuild_group_filter()
        self.wnd_mark_modified()
        self.wnd_update_counts()
        self.wnd_append_log(f"已批量添加 {len(entries)} 条频道。")
        if self.wnd_probe_cache_enabled() and self._config.cfg_get("cache/auto_apply"):
            self.wnd_apply_probe_cache("批量添加",
                                       uids=[entry.uid for entry in entries])
        if dialog.dlg_should_autotest():
            self.wnd_start_test_for_uids([entry.uid for entry in entries])

    @Slot()
    def wnd_act_edit_entry(self) -> None:
        entries = self.wnd_selected_entries()
        if not entries:
            QMessageBox.information(self, "提示", "请先选择一条频道记录。")
            return
        entry = entries[0]
        dialog = M3ULiveEditorLinkEditDialog("编辑链接", entry=entry, parent=self)
        if dialog.exec() != QDialog.Accepted:
            return
        fields = dialog.dlg_collect_fields()
        entry.title = fields.get("name", "")
        entry.duration = fields.get("duration", "0") or "0"
        entry.url = fields.get("url", "")
        entry.remark = fields.get("remark", "")
        for key in ("tvg-name", "group-title", "tvg-id", "channelID", "tvg-chno", "tvg-logo"):
            value = fields.get(key, "").strip()
            if value:
                entry.attrs[key] = value
            elif key in entry.attrs:
                del entry.attrs[key]
        entry.entry_rebuild_extinf_line()
        self._model.mdl_notify_uid_changed(entry.uid)
        self.wnd_rebuild_group_filter()
        self.wnd_mark_modified()
        self.wnd_update_counts()
        self.wnd_append_log(f"已修改频道：{entry.entry_effective_name()}")

    @Slot()
    def wnd_act_delete_selected(self) -> None:
        uids = self.wnd_selected_uids()
        if not uids:
            QMessageBox.information(self, "提示", "请先选择要删除的频道。")
            return
        reply = QMessageBox.question(
            self, "确认删除", f"确定删除选中的 {len(uids)} 条频道吗？",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if reply != QMessageBox.Yes:
            return
        removed = self._document.doc_remove_uids(uids)
        self._model.mdl_notify_structural_change()
        self.wnd_rebuild_group_filter()
        self.wnd_mark_modified()
        self.wnd_update_counts()
        self.wnd_append_log(f"已删除 {removed} 条频道。")

    @Slot()
    def wnd_act_delete_all(self) -> None:
        if not self._document.entries:
            return
        reply = QMessageBox.question(
            self, "确认", f"确定删除全部 {len(self._document.entries)} 条频道吗？",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if reply != QMessageBox.Yes:
            return
        count = len(self._document.entries)
        self._document.entries = []
        self._document.modified = True
        self._model.mdl_notify_structural_change()
        self.wnd_rebuild_group_filter()
        self.wnd_update_counts()
        self.wnd_append_log(f"已删除全部 {count} 条频道。")

    @Slot()
    def wnd_act_batch_delete(self) -> None:
        if not self._document.entries:
            QMessageBox.information(self, "提示", "当前没有可删除的频道。")
            return
        dialog = M3ULiveEditorBatchDeleteDialog(
            self._document, group_names=self._document.doc_group_names(), parent=self)
        if dialog.exec() != QDialog.Accepted:
            return
        uids = dialog.dlg_result_uids()
        removed = self._document.doc_remove_uids(uids)
        self._model.mdl_notify_structural_change()
        self.wnd_rebuild_group_filter()
        self.wnd_mark_modified()
        self.wnd_update_counts()
        self.wnd_append_log(f"批量删除完成，共删除 {removed} 条频道。")

    @Slot()
    def wnd_act_remove_duplicates(self) -> None:
        if not self._document.entries:
            return
        removed = self._document.doc_deduplicate()
        if not removed:
            QMessageBox.information(self, "提示", "没有发现重复链接。")
            return
        self._model.mdl_notify_structural_change()
        self.wnd_rebuild_group_filter()
        self.wnd_mark_modified()
        self.wnd_update_counts()
        self.wnd_append_log(f"已删除 {removed} 条重复链接。")

    @Slot()
    def wnd_act_batch_replace(self) -> None:
        if not self._document.entries:
            QMessageBox.information(self, "提示", "当前没有可操作的频道。")
            return
        dialog = M3ULiveEditorBatchReplaceDialog(self)
        dialog.dlg_set_context(self._document, self.wnd_selected_uids())
        if dialog.exec() != QDialog.Accepted:
            return
        changed = dialog.dlg_apply_replacements(self._document, self.wnd_selected_uids())
        if not changed:
            QMessageBox.information(self, "提示", "没有发生任何替换。")
            return
        self._model.mdl_refresh_all()
        self.wnd_rebuild_group_filter()
        self.wnd_mark_modified()
        self.wnd_update_counts()
        self.wnd_append_log(f"批量替换完成，共修改 {changed} 条记录。")
        if self.wnd_probe_cache_enabled() and self._config.cfg_get("cache/auto_apply"):
            self.wnd_apply_probe_cache("批量替换后")

    # -- 批量修改分组（多选 / 整批）-----------------------------------------
    def wnd_after_group_batch(self, changed: int, target: str) -> None:
        """改完分组后的统一收尾：刷新表格与分组下拉、标记改动、写日志。"""
        self._model.mdl_refresh_all()
        self.wnd_rebuild_group_filter()
        self.wnd_mark_modified()
        self.wnd_update_counts()
        label = target if target else "（清除分组）"
        self.wnd_append_log(f"批量修改分组：{changed} 条已改成「{label}」。")

    def wnd_assign_group_to_selection(self, target: str) -> int:
        """把选中的条目直接归入 target 分组（空字符串＝清除分组）。"""
        entries = self.wnd_selected_entries()
        if not entries:
            self.wnd_append_log("批量修改分组：没有选中任何频道，未做改动。")
            return 0
        changed = m3ule_group_batch_apply(entries, target)
        if not changed:
            label = target if target else "（清除分组）"
            self.wnd_append_log(f"批量修改分组：选中条目的分组已经是「{label}」，未做改动。")
            return 0
        self.wnd_after_group_batch(changed, target)
        return changed

    def wnd_build_group_quick_menu(self) -> QMenu:
        """右键菜单里的「快速加入已有分组」子菜单（作用于选中条目）。"""
        menu = QMenu("加入已有分组（选中条目）", self)
        entries = self.wnd_selected_entries()
        names = self._document.doc_group_names()
        if not entries:
            item = menu.addAction("（先选中频道，可按住 Ctrl / Shift 多选）")
            item.setEnabled(False)
            return menu
        if not names:
            item = menu.addAction("（当前文件还没有分组，请用「批量修改分组…」新建）")
            item.setEnabled(False)
        else:
            for name in names[:M3ULE_GROUP_QUICK_MENU_LIMIT]:
                action = menu.addAction(name)
                action.triggered.connect(
                    lambda _checked=False, group=name: self.wnd_assign_group_to_selection(group))
            if len(names) > M3ULE_GROUP_QUICK_MENU_LIMIT:
                item = menu.addAction(
                    f"…其余 {len(names) - M3ULE_GROUP_QUICK_MENU_LIMIT} 个分组，请用「批量修改分组…」")
                item.setEnabled(False)
        menu.addSeparator()
        action_clear = menu.addAction("清除分组（删除 group-title）")
        action_clear.triggered.connect(lambda: self.wnd_assign_group_to_selection(""))
        return menu

    @Slot()
    def wnd_act_batch_group(self) -> None:
        if not self._document.entries:
            QMessageBox.information(self, "提示", "当前没有可修改的频道。")
            return
        selected = self.wnd_selected_uids()
        visible = [entry.uid for entry in self.wnd_visible_entries()]
        dialog = M3ULiveEditorBatchGroupDialog(
            self._document, selected_uids=selected, visible_uids=visible, parent=self)
        if dialog.exec() != QDialog.Accepted:
            return
        changed = dialog.dlg_apply_group()
        self.wnd_after_group_batch(changed, dialog.dlg_target_group())

    # -- 台标自动匹配（按频道名补 tvg-logo）-----------------------------------
    def wnd_logo_match_dialog(self, only_selected=None) -> M3ULiveEditorLogoMatchDialog:
        """建一个「台标自动匹配」对话框（来源与选项都记在设置里）。

        有选中条目时默认只处理选中的那些（想改动整份文件可在对话框里切回「当前文件全部」）。
        """
        selected = self.wnd_selected_uids()
        if only_selected is None:
            only_selected = bool(selected)
        dialog = M3ULiveEditorLogoMatchDialog(
            self._document, self._history, self._config,
            selected_uids=selected, only_selected=only_selected, parent=self)
        dialog.dlg_offer_bundled_library()
        return dialog

    @Slot()
    def wnd_act_match_logos(self) -> None:
        """台标自动匹配（菜单 / 右键入口）：有选中条目时默认只处理选中的那些。"""
        self.wnd_run_logo_match(bool(self.wnd_selected_uids()))

    def wnd_run_logo_match(self, only_selected: bool = False) -> int:
        """打开「台标自动匹配」对话框；返回真正写入的条数（0 表示没改动）。"""
        if not self._document.entries:
            QMessageBox.information(self, "提示", "当前没有可匹配的频道。")
            return 0
        dialog = self.wnd_logo_match_dialog(only_selected)
        if dialog.exec() != QDialog.Accepted:
            return 0
        changed = dialog.dlg_apply_to_document()
        if not changed:
            QMessageBox.information(
                self, "提示", "没有写入任何台标（勾选项的台标可能都和现有的一样）。")
            return 0
        self._model.mdl_refresh_all()
        self.wnd_mark_modified()
        self.wnd_update_counts()
        self.wnd_append_log(
            f"台标自动匹配：{changed} 条已补上台标（参考索引 {dialog.dlg_index_size()} 个名字）。")
        self._schedule_save_runtime_settings()
        return changed

    def wnd_act_move_entry(self, offset: int) -> None:
        entries = self.wnd_selected_entries()
        if not entries:
            return
        entry = entries[0]
        index = self._document.doc_index_of_uid(entry.uid)
        if index < 0:
            return
        if self._document.doc_move_entry(index, index + offset):
            self._model.mdl_notify_structural_change()
            self.wnd_mark_modified()
            self._view_edit.selectRow(self._model.mdl_row_of_uid(entry.uid))

    @Slot()
    def wnd_act_find_focus(self) -> None:
        self._tabs.setCurrentWidget(self._tab_edit)
        self._edit_filter_keyword.setFocus()
        self._edit_filter_keyword.selectAll()

    # ==================================================================
    # 检测结果缓存（跨启动持久化，避免每次打开都重新检测）
    # ==================================================================
    def wnd_probe_cache_enabled(self) -> bool:
        return bool(self._config.cfg_get("cache/enabled"))

    def wnd_probe_cache_ttl(self) -> int:
        return max(0, m3ule_safe_int(self._config.cfg_get("cache/ttl_hours"), 72))

    def wnd_should_skip_cached_tests(self) -> bool:
        """测试时是否跳过缓存有效期内已检测过的链接。"""
        if not self.wnd_probe_cache_enabled():
            return False
        widget = getattr(self, "_chk_test_skip_cached", None)
        if widget is not None:
            return bool(widget.isChecked())
        return bool(self._config.cfg_get("cache/skip_fresh"))

    def wnd_cache_total(self, force: bool = False) -> int:
        """缓存总条数（带内存缓存，避免频繁查库）。"""
        if force or self._cache_total_cache < 0:
            self._cache_total_cache = (self._history.dbh_count_probe_cache()
                                       if self._history.available else 0)
        return self._cache_total_cache

    def wnd_refresh_cache_stats(self, force: bool = False) -> None:
        """刷新“检测缓存”统计文案（测试页 + 设置页 + 状态栏）。"""
        count = self.wnd_cache_total(force)
        ttl = self.wnd_probe_cache_ttl()
        ttl_text = "永久有效" if ttl <= 0 else f"{ttl} 小时内有效"
        filled = sum(1 for entry in self._document.entries if entry.test_cached)
        text = f"检测缓存：已保存 {count} 条 · {ttl_text} · 当前文件回填 {filled} 条"
        label = getattr(self, "_lbl_test_cache_stats", None)
        if label is not None:
            label.setText(text)
        tab = getattr(self, "_tab_settings", None)
        settings_label = getattr(tab, "_lbl_cache_stats", None) if tab is not None else None
        if settings_label is not None:
            settings_label.setText(text)

    def wnd_store_probe_cache(self, payloads) -> int:
        """把刚测出的结果写入持久缓存，下次打开或再次测试时可直接复用。"""
        if not self.wnd_probe_cache_enabled():
            return 0
        if not self._config.cfg_get("cache/auto_store"):
            return 0
        if not self._history.available:
            return 0
        rows = []
        for item in payloads or []:
            if not isinstance(item, dict):
                continue
            if str(item.get("state") or "") in ("", M3ULE_STATUS_NONE, M3ULE_STATUS_CANCEL):
                continue
            rows.append(item)
        if not rows:
            return 0
        source = os.path.basename(self._document.path or "")
        written = self._history.dbh_upsert_probe_cache(rows, source_file=source)
        if written:
            self.wnd_refresh_cache_stats(force=True)
        elif self._history.dbh_last_error():
            self.wnd_append_log(
                f"检测缓存写入失败：{self._history.dbh_last_error()}")
        return written

    def wnd_apply_probe_cache(self, reason: str = "", uids=None, silent: bool = False) -> int:
        """把持久缓存里的检测结果回填到当前文件（打开文件 / 追加导入 / 手动应用）。"""
        if not self.wnd_probe_cache_enabled() or not self._history.available:
            return 0
        entries = self._document.entries
        if uids is not None:
            wanted = set(uids)
            entries = [entry for entry in entries if entry.uid in wanted]
        keyed: dict = {}
        for entry in entries:
            key = m3ule_probe_cache_key(entry.url or "")
            if key:
                keyed.setdefault(key, []).append(entry)
        if not keyed:
            return 0
        records = self._history.dbh_get_probe_cache(list(keyed.keys()), touch=True)
        ttl = self.wnd_probe_cache_ttl()
        applied = 0
        expired = 0
        for key, group in keyed.items():
            record = records.get(key)
            if not record:
                continue
            payload = record.get("payload") or {}
            if not payload.get("state"):
                continue
            checked_at = record.get("checked_at", "")
            if not m3ule_probe_cache_is_fresh(checked_at, ttl):
                expired += 1
            for entry in group:
                entry.entry_set_cached_result(payload, checked_at)
                applied += 1
        if applied:
            self._model.mdl_refresh_all()
            self.wnd_update_counts()
            self.wnd_refresh_cache_stats()
        if applied and not silent:
            note = f"（其中 {expired} 条已超出有效期，重测时会重新检测）" if expired else ""
            self.wnd_append_log(
                f"已从检测缓存恢复 {applied} 条检测结果{note}：{reason or '手动应用'}")
        return applied

    def wnd_clear_entries_probe_cache(self, entries) -> int:
        """删除指定条目对应链接的缓存记录，返回数据库删除条数。"""
        keys = [m3ule_probe_cache_key(entry.url or "") for entry in (entries or [])]
        keys = [key for key in keys if key]
        if not keys or not self._history.available:
            return 0
        removed = self._history.dbh_delete_probe_cache(keys)
        self.wnd_refresh_cache_stats(force=True)
        return removed

    @Slot()
    def wnd_act_apply_probe_cache(self) -> None:
        if not self._history.available:
            QMessageBox.information(self, "提示", f"检测缓存不可用：{self._history.error}")
            return
        if not self._document.entries:
            QMessageBox.information(self, "提示", "当前没有可套用缓存的频道。")
            return
        applied = self.wnd_apply_probe_cache("手动应用")
        if applied:
            self.wnd_append_log(f"已套用检测缓存：{applied} 条。")
        else:
            QMessageBox.information(self, "提示", "没有找到与当前链接匹配的检测缓存。")

    @Slot()
    def wnd_act_clear_probe_cache(self) -> None:
        if not self._history.available:
            QMessageBox.information(self, "提示", f"检测缓存不可用：{self._history.error}")
            return
        count = self._history.dbh_count_probe_cache()
        if not count:
            QMessageBox.information(self, "提示", "检测缓存已经是空的。")
            return
        reply = QMessageBox.question(
            self, "确认",
            f"确定清空全部检测缓存吗？（已保存 {count} 条检测结果）\n"
            "清空后再次测试需要重新检测所有链接。",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if reply != QMessageBox.Yes:
            return
        self._history.dbh_clear_probe_cache()
        self.wnd_refresh_cache_stats(force=True)
        self.wnd_append_log(f"已清空检测缓存（{count} 条）。")

    @Slot()
    def wnd_act_clear_selected_cache(self) -> None:
        entries = self.wnd_selected_entries()
        if not entries:
            QMessageBox.information(self, "提示", "请先选择要清除检测缓存的频道。")
            return
        removed = self.wnd_clear_entries_probe_cache(entries)
        for entry in entries:
            entry.entry_reset_test_result()
        self._model.mdl_refresh_all()
        self.wnd_update_counts()
        self.wnd_append_log(
            f"已清除所选 {len(entries)} 条链接的检测缓存（数据库删除 {removed} 条）。")

    @Slot()
    def wnd_act_prune_probe_cache(self) -> None:
        ttl = self.wnd_probe_cache_ttl()
        if ttl <= 0:
            QMessageBox.information(
                self, "提示", "当前“检测缓存有效期”为永久有效，没有可清理的过期缓存。")
            return
        removed = self._history.dbh_prune_probe_cache(ttl)
        self.wnd_refresh_cache_stats(force=True)
        self.wnd_append_log(f"已清理过期检测缓存 {removed} 条（有效期 {ttl} 小时）。")
        QMessageBox.information(self, "完成", f"已清理过期检测缓存 {removed} 条。")

    # ==================================================================
    # 测试
    # ==================================================================
    def wnd_collect_test_tasks(self, scope: str) -> list:
        self._last_skipped_cached = 0
        entries = self._document.entries
        ignore_cache = scope == "force"
        if ignore_cache:
            scope = "all"
        if scope == "selected":
            entries = self.wnd_selected_entries()
        elif scope == "failed":
            entries = [entry for entry in entries
                       if entry.test_state in (M3ULE_STATUS_FAIL, M3ULE_STATUS_TIMEOUT, M3ULE_STATUS_ERROR)]
        elif scope == "untested":
            entries = [entry for entry in entries if not entry.test_state]
        elif scope == "stale":
            ttl = self.wnd_probe_cache_ttl()
            entries = [entry for entry in entries
                       if not entry.test_state
                       or (entry.test_cached and not entry.entry_test_result_is_fresh(ttl))]
        elif scope == "scope":
            text = self._combo_test_scope.currentText()
            mapping = {"全部条目": "all", "当前选中": "selected",
                       "仅失败项": "failed", "仅未测试项": "untested",
                       "仅缓存过期项": "stale", "忽略缓存全部重测": "force"}
            return self.wnd_collect_test_tasks(mapping.get(text, "all"))
        if not ignore_cache and self.wnd_should_skip_cached_tests():
            ttl = self.wnd_probe_cache_ttl()
            kept = []
            for entry in entries:
                if entry.entry_test_result_is_fresh(ttl):
                    self._last_skipped_cached += 1
                    continue
                kept.append(entry)
            entries = kept
        tasks = []
        for entry in entries:
            url = (entry.url or "").strip()
            if not url:
                continue
            tasks.append({"uid": entry.uid, "url": url, "label": entry.entry_effective_name()})
        return tasks

    def wnd_act_start_test(self, scope: str = "all") -> None:
        if self._test_worker is not None and self._test_worker.isRunning():
            QMessageBox.information(self, "提示", "已有测试任务正在运行，请先停止。")
            return
        if self.wnd_probe_cache_enabled():
            # 先回填缓存，界面状态与实际结果保持一致；未过期的条目随后会被跳过
            self.wnd_apply_probe_cache("开始测试前套用缓存", silent=True)
        tasks = self.wnd_collect_test_tasks(scope)
        if not tasks:
            skipped = self._last_skipped_cached
            if skipped:
                QMessageBox.information(
                    self, "提示",
                    f"这 {skipped} 条链接都还在检测缓存有效期内，无需重复检测。\n\n"
                    "如需强制重新检测，请取消勾选“跳过有效缓存”，"
                    "或把范围选为“忽略缓存全部重测”。")
            else:
                QMessageBox.information(self, "提示", "没有符合条件的链接需要测试。")
            return
        if self._last_skipped_cached:
            self.wnd_append_log(
                f"已跳过 {self._last_skipped_cached} 条缓存有效期内的链接"
                "（如需强制重测，请取消勾选“跳过有效缓存”）。")
        if len(tasks) > 2000:
            reply = QMessageBox.question(
                self, "确认",
                f"将测试 {len(tasks)} 条链接，可能耗时较长，是否继续？",
                QMessageBox.Yes | QMessageBox.No, QMessageBox.Yes)
            if reply != QMessageBox.Yes:
                return
        self._tabs.setCurrentWidget(self._tab_test)
        self.wnd_start_test_for_uids([task["uid"] for task in tasks], tasks=tasks)

    def wnd_start_test_for_uids(self, uids, tasks=None) -> None:
        if self._test_worker is not None and self._test_worker.isRunning():
            return
        if tasks is None:
            uid_set = set(uids)
            tasks = []
            for entry in self._document.entries:
                if entry.uid in uid_set and (entry.url or "").strip():
                    tasks.append({"uid": entry.uid, "url": entry.url.strip(),
                                  "label": entry.entry_effective_name()})
        if not tasks:
            return
        # 测试前把当前结果存成「上一次」，供「对比上次」列判断这次是多了台还是少了台
        for task in tasks:
            entry = self._document.doc_find_entry_by_uid(task.get("uid", -1))
            if entry is not None:
                entry.entry_snapshot_previous_result()
        self._model.mdl_refresh_all()
        options = {
            "workers": self._spin_test_workers.value(),
            "timeout": self._spin_test_timeout.value(),
            "retries": self._spin_test_retries.value(),
            "deep": self._chk_test_deep.isChecked(),
            "user_agent": self._config.cfg_get_user_agent(),
            "proxy": self._config.cfg_get_proxy(),
            "ignore_ssl": self._chk_test_ssl.isChecked(),
        }
        self._test_total = len(tasks)
        self._test_done = 0
        self._test_cache_written = 0
        self._test_summary_counts = {"ok": 0, "bad": 0}
        self._test_progress.setRange(0, self._test_total)
        self._test_progress.setValue(0)
        self._lbl_test_summary.setText(f"测试中 0/{self._test_total}")
        self._btn_test_stop.setEnabled(True)
        self._tabs.setCurrentWidget(self._tab_test)

        self._test_worker = M3ULiveEditorProbeWorker(tasks, options, parent=self)
        self._test_worker.sig_worker_results.connect(self.wnd_on_test_results)
        self._test_worker.sig_worker_progress.connect(self.wnd_on_test_progress)
        self._test_worker.sig_worker_log.connect(self.wnd_append_log)
        self._test_worker.sig_worker_finished.connect(self.wnd_on_test_finished)
        self._test_worker.start()
        self.wnd_append_log(f"任务已加入 {len(tasks)} 条链接开始测试。")

    @Slot(object)
    def wnd_on_test_results(self, payloads: list) -> None:
        for payload in payloads:
            uid = payload.get("uid", -1)
            entry = self._document.doc_find_entry_by_uid(uid)
            if entry is None:
                continue
            entry.entry_apply_probe_payload(payload)
            self._model.mdl_notify_uid_changed(uid)
            if entry.test_state in (M3ULE_STATUS_OK, M3ULE_STATUS_PARTIAL):
                self._test_summary_counts["ok"] += 1
            else:
                self._test_summary_counts["bad"] += 1
        self._test_cache_written += self.wnd_store_probe_cache(payloads)
        self.wnd_update_counts()

    @Slot(int, int)
    def wnd_on_test_progress(self, done: int, total: int) -> None:
        self._test_progress.setRange(0, max(1, total))
        self._test_progress.setValue(done)
        self.wnd_set_progress(done, max(1, total), f"测试中 {done}/{total}")
        self._lbl_test_summary.setText(
            f"测试中 {done}/{total} · 可用 {self._test_summary_counts.get('ok', 0)} · "
            f"异常 {self._test_summary_counts.get('bad', 0)}")

    @Slot(dict)
    def wnd_on_test_finished(self, summary: dict) -> None:
        self._btn_test_stop.setEnabled(False)
        self._test_progress.setValue(self._test_progress.maximum())
        self.wnd_set_progress(0, 100, "测试完成")
        text = (f"完成：成功 {summary.get('ok', 0)} · 部分可用 {summary.get('partial', 0)} · "
                f"失败 {summary.get('fail', 0)} · 超时 {summary.get('timeout', 0)} · "
                f"错误 {summary.get('error', 0)} · 有节目 {summary.get('has_program', 0)} · "
                f"用时 {summary.get('elapsed_ms', 0) / 1000:.1f}s")
        if summary.get("cancelled"):
            text = "已停止 · " + text
        self._lbl_test_summary.setText(text)
        if self._history.available:
            recorded = self._history.dbh_record_test_results(self._document)
            if recorded:
                self.wnd_append_log(f"测试结果已写入历史数据库（{recorded} 条）。")
            elif self._history.dbh_last_error():
                self.wnd_append_log(
                    f"历史数据库写入失败（不影响界面结果）：{self._history.dbh_last_error()}")
        if self._test_cache_written:
            self.wnd_append_log(
                f"检测结果已保存到缓存 {self._test_cache_written} 条，"
                "下次打开同一文件或再次测试时会直接复用，不再重复检测。")
            self.wnd_refresh_cache_stats()
        self._tab_settings.stt_refresh_db_stats()
        self.wnd_append_log(text)
        delta_text = self.wnd_delta_summary_text()
        if delta_text:
            self._lbl_test_summary.setText(f"{text} · {delta_text}")
            gained = self.wnd_delta_counts().get(M3ULE_DELTA_GAINED, 0)
            lost = self.wnd_delta_counts().get(M3ULE_DELTA_LOST, 0)
            self.wnd_append_log(
                delta_text + ("　（可在「视图 → 文件编辑列 / 链接测试列」里打开「对比上次」列查看明细）"
                              if (gained or lost) else ""))
        self._test_worker = None
        self.wnd_update_counts()

    def wnd_delta_counts(self) -> dict:
        """统计「对比上次」各结论的条数（只统计有上一次记录、本次已测过的条目）。"""
        counts = {label: 0 for label in M3ULE_DELTA_ORDER}
        for entry in self._document.entries:
            label = entry.entry_delta_label()
            if label:
                counts[label] = counts.get(label, 0) + 1
        return counts

    def wnd_delta_summary_text(self) -> str:
        """「对比上次」一句话结论：这次比上次多了还是少了。"""
        counts = self.wnd_delta_counts()
        total = sum(counts.values())
        if not total:
            return ""
        return (f"对比上次：★新增可用 {counts.get(M3ULE_DELTA_GAINED, 0)} · "
                f"★新失效 {counts.get(M3ULE_DELTA_LOST, 0)} · "
                f"仍然可用 {counts.get(M3ULE_DELTA_KEEP_OK, 0)} · "
                f"仍然不可用 {counts.get(M3ULE_DELTA_KEEP_BAD, 0)} · "
                f"首次测试 {counts.get(M3ULE_DELTA_FIRST, 0)} · "
                f"本次未测 {counts.get(M3ULE_DELTA_UNTESTED, 0)}")

    @Slot()
    def wnd_act_stop_test(self) -> None:
        if self._test_worker is not None and self._test_worker.isRunning():
            self._test_worker.worker_request_cancel()
            self._btn_test_stop.setEnabled(False)
            self.wnd_append_log("已请求停止测试。")

    @Slot()
    def wnd_act_clear_test_results(self) -> None:
        for entry in self._document.entries:
            entry.entry_reset_test_result()
        self._model.mdl_refresh_all()
        self._test_summary_counts = {"ok": 0, "bad": 0}
        self._lbl_test_summary.setText("已清空测试结果（检测缓存仍保留，可点“应用检测缓存”再套用）")
        self.wnd_update_counts()
        self.wnd_append_log("已清空全部测试结果与「对比上次」快照（检测缓存未受影响）。")

    @Slot()
    def wnd_act_show_index_map(self) -> None:
        """打开编号映射表对话框（编号 ↔ 频道名 ↔ 可用性）。"""
        dialog = getattr(self, "_index_map_dialog", None)
        if dialog is None:
            dialog = M3ULiveEditorIndexMapDialog(self, parent=self)
            self._index_map_dialog = dialog
        else:
            dialog.dlg_load_from_current()
        dialog.show()
        dialog.raise_()
        dialog.activateWindow()

    def wnd_sync_id_dialog(self):
        """频道同步对话框（惰性创建，内容自带记忆）。"""
        dialog = getattr(self, "_sync_dialog", None)
        if dialog is None:
            dialog = M3ULiveEditorSyncDialog(self, parent=self)
            self._sync_dialog = dialog
        return dialog

    @Slot()
    def wnd_act_sync_index_ids(self) -> None:
        """把「已校对文件里确认的 频道名 → 编号」同步到另一个文件。

        两种方式：只更新编号（其它频道原样保留）或整表替换（用来源重建频道区、
        旧频道清除、同名频道沿用原分组与台标）。
        """
        dialog = self.wnd_sync_id_dialog()
        dialog.show()
        dialog.raise_()
        dialog.activateWindow()

    @Slot()
    def wnd_act_show_test_history(self) -> None:
        if not self._history.available:
            QMessageBox.information(self, "提示", f"历史数据库不可用：{self._history.error}")
            return
        runs = self._history.dbh_recent_scan_runs(20)
        lines = [
            f"测试历史条数：{self._history.dbh_count_rows('test_history')}",
            f"频道映射条数：{self._history.dbh_count_rows('id_remarks')}",
            f"检测缓存条数：{self._history.dbh_count_rows('probe_cache')}",
            "",
            "最近扫描记录：",
        ]
        for run in runs:
            lines.append(f"  {run[0]}  编号 {run[2]}~{run[3]}  共 {run[4]}，可用 {run[5]}  {run[6]}")
        QMessageBox.information(self, "测试历史统计", "\n".join(lines))

    # ==================================================================
    # 打开链接 / 工具
    # ==================================================================
    def wnd_open_url_with_player(self, url: str) -> None:
        if not url:
            QMessageBox.information(self, "提示", "链接为空。")
            return
        player = self._config.cfg_get("player/path").strip()
        try:
            if player and os.path.isfile(player):
                subprocess.Popen([player, url])
                self.wnd_append_log(f"已用播放器打开：{url}")
            else:
                if not QDesktopServices.openUrl(QUrl(url)):
                    raise OSError("系统未能打开该链接")
                self.wnd_append_log(f"已用系统默认程序打开：{url}")
        except Exception as exc:  # noqa: BLE001
            self.wnd_append_log(f"打开失败：{exc}")
            QMessageBox.warning(self, "打开失败", f"{exc}\n\n可在“设置”中指定播放器路径。")

    @Slot()
    def wnd_act_open_in_player(self) -> None:
        entries = self.wnd_selected_entries()
        if not entries:
            QMessageBox.information(self, "提示", "请先选择一条频道。")
            return
        self.wnd_open_url_with_player(entries[0].url or "")

    # ==================================================================
    # 弹窗播放器（内嵌 FFmpeg / VLC 内核，或系统浏览器播放页）
    # ==================================================================
    def wnd_relay_server(self) -> M3ULiveEditorStreamRelayServer:
        """惰性创建本机播放中转服务（系统浏览器播放页用）。"""
        if self._relay is None:
            self._relay = M3ULiveEditorStreamRelayServer(
                user_agent=self._config.cfg_get_user_agent(),
                timeout=max(8.0, float(self._config.cfg_get("probe/timeout") or 8.0)),
                use_local_hlsjs=bool(self._config.cfg_get("player/html5_local_hlsjs")))
        else:
            self._relay.user_agent = self._config.cfg_get_user_agent()
            self._relay.timeout = max(8.0, float(self._config.cfg_get("probe/timeout") or 8.0))
            self._relay.use_local_hlsjs = bool(self._config.cfg_get("player/html5_local_hlsjs"))
        return self._relay

    def wnd_html5_entry_list_and_start(self) -> tuple:
        """返回 (要播放的条目列表, 起始索引)。

        列表＝当前视图的全部频道（已按筛选/排序），起始索引＝选中行在列表中的位置（没选就从第一个开始）。
        这样播放弹窗里的「上一个 / 下一个」可以直接在整份列表上连着切换。
        """
        entries = self.wnd_visible_entries()
        if not entries:
            return [], 0
        start = 0
        selected = self.wnd_selected_entries()
        if selected:
            for index, entry in enumerate(entries):
                if entry.uid == selected[0].uid:
                    start = index
                    break
        return entries, start

    @Slot()
    def wnd_act_open_in_html5(self) -> None:
        """打开播放弹窗：带上**当前视图的全部频道**，从选中行开始，方便用「上一个/下一个」连着看。"""
        entries, start = self.wnd_html5_entry_list_and_start()
        if not entries:
            QMessageBox.information(self, "提示", "当前视图里没有可播放的频道。")
            return
        self.wnd_open_html5_player(entries, start)

    def wnd_open_html5_player(self, entries: list, start_index: int = 0) -> None:
        """打开弹窗播放器（或按设置改用系统浏览器播放页）。"""
        playable = [entry for entry in (entries or []) if (entry.url or "").strip()]
        if not playable:
            QMessageBox.information(self, "提示", "所选条目没有有效链接。")
            return
        mode = self._config.cfg_get("player/html5_mode")
        if mode == "系统浏览器":
            relay = self.wnd_relay_server()
            if not relay.relay_start():
                QMessageBox.warning(
                    self, "提示",
                    "无法启动本机播放中转服务，请改用“用播放器打开”（VLC）。")
                return
            target = playable[max(0, min(start_index, len(playable) - 1))]
            url = relay.relay_player_url(target.url or "", target.entry_effective_name())
            QDesktopServices.openUrl(QUrl(url))
            self.wnd_append_log(
                f"已在系统浏览器打开播放页（{target.entry_effective_name()}）；"
                "需保持本程序运行以维持本机中转。")
            return
        self.wnd_append_log("弹窗播放器已启动（内嵌播放，内核：" +
                            m3ule_player_backend_label(m3ule_player_backend_key(
                                self._config.cfg_get("player/backend"))) + "）。")
        dialog = self._html5_dialog
        if dialog is None:
            dialog = M3ULiveEditorHtml5PlayerDialog(self, playable, start_index, parent=self)
            self._html5_dialog = dialog
        else:
            dialog._entries = playable
            dialog.dlg_fill_entries_combo(playable, start_index)
        # 先显示弹窗再开始播放：内嵌内核需要窗口已经显示出来，
        # 否则画面可能被丢到一个独立的输出窗口里（看起来像「另开了一个播放器」）。
        dialog.show()
        dialog.raise_()
        dialog.activateWindow()
        dialog.dlg_play_index(start_index)

    def wnd_open_url_in_html5(self, url: str, title: str = "", entries: list = None,
                              start_index: int = 0) -> None:
        """按链接直接打开弹窗播放器（供 ID 扫描页等使用）。

        entries 给定时用这份列表（这样弹窗里的「上一个/下一个」可以连续切换），
        start_index 指定从哪一条开始播；不给 entries 时就播这一条链接。
        """
        url = (url or "").strip()
        if not url:
            QMessageBox.information(self, "提示", "链接为空。")
            return
        playable = [entry for entry in (entries or []) if (entry.url or "").strip()]
        if not playable:
            playable = [M3ULiveEditorEntry(url=url, title=title or "")]
            start_index = 0
        else:
            start_index = max(0, min(int(start_index), len(playable) - 1))
        self.wnd_open_html5_player(playable, start_index)

    @Slot()
    def wnd_act_open_in_browser(self) -> None:
        entries = self.wnd_selected_entries()
        if not entries:
            QMessageBox.information(self, "提示", "请先选择一条频道。")
            return
        url = (entries[0].url or "").strip()
        if not url:
            QMessageBox.information(self, "提示", "链接为空。")
            return
        webbrowser.open(url)
        self.wnd_append_log(f"已在浏览器打开：{url}")

    @Slot()
    def wnd_act_copy_url(self) -> None:
        entries = self.wnd_selected_entries()
        if not entries:
            QMessageBox.information(self, "提示", "请先选择频道。")
            return
        if len(entries) == 1:
            QApplication.clipboard().setText(entries[0].url or "")
        else:
            QApplication.clipboard().setText("\n".join(entry.url or "" for entry in entries))
        self.wnd_append_log(f"已复制 {len(entries)} 条链接到剪贴板。")

    @Slot()
    def wnd_act_open_program_dir(self) -> None:
        path = m3ule_get_program_dir()
        try:
            os.startfile(path)  # type: ignore[attr-defined]
        except Exception:
            QDesktopServices.openUrl(QUrl.fromLocalFile(path))

    @Slot()
    def wnd_act_open_data_dir(self) -> None:
        path = m3ule_get_data_dir()
        try:
            os.startfile(path)  # type: ignore[attr-defined]
        except Exception:
            QDesktopServices.openUrl(QUrl.fromLocalFile(path))

    @Slot()
    def wnd_act_open_env_file(self) -> None:
        path = m3ule_get_env_path()
        if not os.path.isfile(path):
            m3ule_save_env_key("M3ULE_DB_PASSWORD", "")
        try:
            os.startfile(path)  # type: ignore[attr-defined]
        except Exception:
            QDesktopServices.openUrl(QUrl.fromLocalFile(path))

    @Slot()
    def wnd_act_save_log(self) -> None:
        last_dir = self._config.cfg_get("io/last_save_dir")
        default = os.path.join(last_dir, f"运行日志_{datetime.now():%Y%m%d_%H%M%S}.txt")
        path, _ = QFileDialog.getSaveFileName(self, "保存日志", default, "文本文件 (*.txt)")
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8") as handle:
                handle.write(self._log_view.toPlainText())
        except OSError as exc:
            QMessageBox.warning(self, "保存失败", str(exc))
            return
        self.wnd_append_log(f"日志已保存：{path}")

    @Slot()
    def wnd_act_show_help(self) -> None:
        M3ULiveEditorHelpDialog(self).exec()

    @Slot()
    def wnd_act_check_icon(self) -> None:
        path = m3ule_get_icon_path()
        if path:
            QMessageBox.information(self, "图标状态", f"已加载图标：\n{path}")
        else:
            QMessageBox.information(
                self, "图标状态",
                "程序目录下未找到 icon.ico，程序将使用系统默认图标。\n"
                "把 icon.ico 放到程序目录即可自动启用。")

    @Slot()
    def wnd_act_show_about(self) -> None:
        box = QMessageBox(self)
        box.setWindowTitle("关于")
        icon_path = m3ule_get_icon_path()
        if icon_path:
            box.setWindowIcon(QIcon(icon_path))
            pixmap = QPixmap(icon_path)
            if not pixmap.isNull():
                box.setIconPixmap(pixmap.scaled(64, 64, Qt.KeepAspectRatio, Qt.SmoothTransformation))
        box.setTextFormat(Qt.RichText)
        box.setText(
            f"<h3>{M3ULE_APP_NAME_CN}</h3>"
            f"<p>版本：<b>v{M3ULE_VERSION}</b><br>构建日期：{M3ULE_BUILD_DATE}<br>"
            f"程序目录：{m3ule_get_program_dir()}</p>"
            f"<p>技术栈：Python 3.10 · PySide6 (Qt6) · requests · SQLite3</p>"
            f"<p>本程序为唯一主程序（最终更新版），所有更新直接修改 "
            f"M3U_Live_Editor.py，并同步更新《软件升级迭代记录.md》与版本号。</p>")
        box.exec()

    # ==================================================================
    # 列宽 / 设置持久化
    # ==================================================================
    def _apply_view_column_widths(self, view: QTableView) -> None:
        stored = self._column_widths()
        header = view.horizontalHeader()
        columns = self._model.mdl_columns()
        for index, column in enumerate(columns):
            width = stored.get(column["key"])
            if width:
                view.setColumnWidth(index, int(width))
        header.setSectionResizeMode(len(columns) - 1, QHeaderView.Stretch)

    def _column_widths(self) -> dict:
        raw = self._config.cfg_get(self.M3ULE_COLUMN_WIDTH_KEY, "")
        if not raw:
            return {}
        try:
            return json.loads(raw)
        except (ValueError, TypeError):
            return {}

    def wnd_save_column_widths(self) -> None:
        stored = {}
        for index, column in enumerate(self._model.mdl_columns()):
            stored[column["key"]] = self._view_edit.columnWidth(index)
        self._config.cfg_set(self.M3ULE_COLUMN_WIDTH_KEY,
                             json.dumps(stored, ensure_ascii=False))

    def _schedule_save_runtime_settings(self) -> None:
        self._save_timer.start()

    @Slot()
    def wnd_save_runtime_settings(self) -> None:
        self._config.cfg_save_geometry(self.M3ULE_GEOMETRY_KEY, self.saveGeometry())
        self._config.cfg_save_state(self.M3ULE_WINDOW_STATE_KEY, self.saveState())
        self._config.cfg_save_state(self.M3ULE_MAIN_SPLITTER_KEY, self._main_splitter.saveState())
        self._config.cfg_save_state(self.M3ULE_EDIT_SPLITTER_KEY, self._edit_splitter.saveState())
        self._config.cfg_set("ui/current_tab", self._tabs.currentIndex())
        if hasattr(self._tab_diff, "_modes"):
            self._config.cfg_set("diff/mode", self._tab_diff._modes.currentIndex())
        signal_combo = getattr(self._tab_diff, "_combo_pair_signal", None)
        if signal_combo is not None:
            self._config.cfg_set("diff/pair_signal_filter", signal_combo.currentIndex())
        history_check = getattr(self._tab_diff, "_chk_pair_history_old", None)
        if history_check is not None:
            self._config.cfg_set("diff/pair_history_old", history_check.isChecked())
        current_path = self.wnd_current_path()
        if current_path and os.path.isfile(current_path):
            self._config.cfg_set("io/last_file", current_path)
        self.wnd_save_column_widths()
        self.wnd_save_column_layouts()
        self._config.cfg_set("scan/template", self._tab_scan._edit_template.text())
        self._tab_scan.tab_scan_persist_settings()
        self._tab_diff.tab_diff_pair_persist_sources()
        self.wnd_save_table_sort_state()

    def wnd_save_table_sort_state(self) -> None:
        header = self._view_edit.horizontalHeader()
        self._config.cfg_set("ui/sort_column", header.sortIndicatorSection())
        self._config.cfg_set("ui/sort_order",
                             int(header.sortIndicatorOrder().value) if hasattr(header.sortIndicatorOrder(), "value")
                             else int(header.sortIndicatorOrder()))

    def wnd_migrate_player_settings(self) -> str:
        """把旧版本的播放内核设置迁移到现在的两个内核（v1.8.4 起只有 FFmpeg / VLC）。

        旧值（内嵌 HTML5 / mpv / 自动）统一落到默认内核并**写回设置**，同时清掉已移除内核
        遗留的设置键 —— 否则设置文件里会存着一个不存在的内核，用户看到下拉框与设置不一致。
        返回迁移后的内核键（供日志使用）。
        """
        configured = self._config.cfg_get("player/backend")
        key = m3ule_player_backend_key(configured)
        label = m3ule_player_backend_label(key)
        if str(configured or "").strip() != label:
            self._config.cfg_set("player/backend", label)
            self.wnd_append_log(
                f"播放内核已迁移：{str(configured or '(空)').strip() or '(空)'} → {label}"
                "（v1.8.4 起只提供 FFmpeg 与 VLC 两个内核）。")
        settings = QSettings(m3ule_get_settings_path(), QSettings.IniFormat)
        removed = []
        for obsolete in M3ULE_PLAYER_OBSOLETE_SETTINGS:
            if settings.contains(obsolete):
                settings.remove(obsolete)
                removed.append(obsolete)
        if removed:
            settings.sync()
            self.wnd_append_log("已清理旧内核遗留的设置项：" + "、".join(removed))
        return key

    def wnd_restore_settings(self) -> None:
        self.wnd_migrate_player_settings()
        geometry = self._config.cfg_load_geometry(self.M3ULE_GEOMETRY_KEY)
        if not geometry.isEmpty():
            self.restoreGeometry(geometry)
        else:
            screen = QGuiApplication.primaryScreen()
            if screen is not None:
                available = screen.availableGeometry()
                self.resize(min(1440, int(available.width() * 0.9)),
                            min(860, int(available.height() * 0.9)))
        state = self._config.cfg_load_state(self.M3ULE_WINDOW_STATE_KEY)
        if not state.isEmpty():
            self.restoreState(state)
        main_splitter_state = self._config.cfg_load_state(self.M3ULE_MAIN_SPLITTER_KEY)
        if not main_splitter_state.isEmpty():
            self._main_splitter.restoreState(main_splitter_state)
        edit_splitter_state = self._config.cfg_load_state(self.M3ULE_EDIT_SPLITTER_KEY)
        if not edit_splitter_state.isEmpty():
            self._edit_splitter.restoreState(edit_splitter_state)

        self._chk_filter_failed.setChecked(self._config.cfg_get("ui/filter_failed_only", False))
        self._chk_test_failed_only.setChecked(self._config.cfg_get("ui/test_failed_only"))
        self._combo_test_scope.setCurrentText(self._config.cfg_get("ui/test_scope", "全部条目"))
        self._spin_test_workers.setValue(self._config.cfg_get("probe/workers"))
        self._spin_test_timeout.setValue(self._config.cfg_get("probe/timeout"))
        self._spin_test_retries.setValue(self._config.cfg_get("probe/retries"))
        self._chk_test_deep.setChecked(self._config.cfg_get("probe/deep"))
        self._chk_test_ssl.setChecked(self._config.cfg_get("probe/ignore_ssl"))

        raw_recent = self._config.cfg_get(self.M3ULE_RECENT_KEY, "")
        if raw_recent:
            try:
                parsed = json.loads(raw_recent)
                if isinstance(parsed, list):
                    self._recent_files = [str(item) for item in parsed]
            except (ValueError, TypeError):
                self._recent_files = []
        self.wnd_rebuild_recent_menu()

        tab_index = m3ule_safe_int(self._config.cfg_get("ui/current_tab", 0), 0)
        if 0 <= tab_index < self._tabs.count():
            self._tabs.setCurrentIndex(tab_index)

        diff_mode = m3ule_safe_int(self._config.cfg_get("diff/mode", 0), 0)
        if hasattr(self._tab_diff, "_modes") and 0 <= diff_mode < self._tab_diff._modes.count():
            self._tab_diff._modes.setCurrentIndex(diff_mode)
        signal_index = m3ule_safe_int(self._config.cfg_get("diff/pair_signal_filter", 0), 0)
        combo = getattr(self._tab_diff, "_combo_pair_signal", None)
        if combo is not None and 0 <= signal_index < combo.count():
            combo.blockSignals(True)
            combo.setCurrentIndex(signal_index)
            combo.blockSignals(False)
            # 与 tab_diff_pair_signal_changed 保持一致：按信号过滤时不受「只看有变化」遮挡
            if signal_index != 0:
                only_changed = getattr(self._tab_diff, "_chk_pair_only_changed", None)
                if only_changed is not None:
                    only_changed.blockSignals(True)
                    only_changed.setChecked(False)
                    only_changed.blockSignals(False)

        history_check = getattr(self._tab_diff, "_chk_pair_history_old", None)
        if history_check is not None:
            history_check.blockSignals(True)
            history_check.setChecked(self._config.cfg_get("diff/pair_history_old", True))
            history_check.blockSignals(False)

        restored_sides = self._tab_diff.tab_diff_pair_restore_sources()
        if restored_sides:
            self.wnd_append_log(
                f"对比分析：已恢复上次的对比来源（{restored_sides} 侧），"
                "点「开始双列对比」即可刷新结果。")

        column_widths = self._column_widths()
        for index, column in enumerate(self._model.mdl_columns()):
            width = column_widths.get(column["key"], column["width"])
            self._view_edit.setColumnWidth(index, int(width))
            self._view_test.setColumnWidth(index, int(width))
        self.wnd_restore_column_layouts()

        sort_column = m3ule_safe_int(self._config.cfg_get("ui/sort_column", -1), -1)
        if 0 <= sort_column < self._model.columnCount():
            order = Qt.AscendingOrder if m3ule_safe_int(
                self._config.cfg_get("ui/sort_order", 0), 0) == 0 else Qt.DescendingOrder
            self._view_edit.sortByColumn(sort_column, order)
            self._view_test.sortByColumn(sort_column, order)
        else:
            self.wnd_reset_edit_sort()

    def wnd_reset_edit_sort(self) -> None:
        """恢复为文件自然顺序（按序号升序）。"""
        self._view_edit.sortByColumn(0, Qt.AscendingOrder)
        self._view_test.sortByColumn(0, Qt.AscendingOrder)

    # ==================================================================
    # 拖放 / 关闭
    # ==================================================================
    def dragEnterEvent(self, event) -> None:
        if event.mimeData().hasUrls():
            for url in event.mimeData().urls():
                path = url.toLocalFile()
                if path.lower().endswith((".m3u", ".m3u8", ".txt")):
                    event.acceptProposedAction()
                    return
        event.ignore()

    def dropEvent(self, event) -> None:
        for url in event.mimeData().urls():
            path = url.toLocalFile()
            if path.lower().endswith((".m3u", ".m3u8", ".txt")) and os.path.isfile(path):
                if self.wnd_confirm_discard_changes():
                    self.wnd_open_path(path)
                event.acceptProposedAction()
                return
        event.ignore()

    def closeEvent(self, event) -> None:
        if not self.wnd_confirm_discard_changes():
            event.ignore()
            return
        if self._test_worker is not None and self._test_worker.isRunning():
            self._test_worker.worker_request_cancel()
            self._test_worker.wait(3000)
        if self._html5_dialog is not None:
            try:
                self._html5_dialog.close()
            except Exception:
                pass
            self._html5_dialog = None
        if self._relay is not None:
            try:
                self._relay.relay_stop()
            except Exception:
                pass
            self._relay = None
        try:
            self.wnd_save_runtime_settings()
            self._config.cfg_set("ui/test_scope", self._combo_test_scope.currentText())
            self._config.cfg_set("ui/filter_failed_only", self._chk_filter_failed.isChecked())
        except Exception:
            pass
        try:
            self._history.dbh_close()
        except Exception:
            pass
        event.accept()


M3ULE_DARK_STYLESHEET = """
QWidget { background-color: #202124; color: #e8eaed; }
QTableView, QTableWidget, QPlainTextEdit, QTextEdit, QLineEdit, QComboBox, QSpinBox, QDoubleSpinBox {
    background-color: #292a2d; color: #e8eaed; selection-background-color: #3f5f9e; }
QHeaderView::section { background-color: #303134; color: #e8eaed; border: 0px; padding: 3px; }
QGroupBox { border: 1px solid #3c4043; border-radius: 4px; margin-top: 8px; padding-top: 6px; }
QGroupBox::title { subcontrol-origin: margin; left: 8px; padding: 0 4px; color: #9aa0a6; }
QTabBar::tab { background: #292a2d; color: #9aa0a6; padding: 6px 12px; }
QTabBar::tab:selected { background: #3c4043; color: #ffffff; }
QToolBar, QStatusBar, QMenuBar { background-color: #292a2d; }
QPushButton { background-color: #3c4043; border: 1px solid #5f6368; border-radius: 3px; padding: 4px 10px; }
QPushButton:hover { background-color: #4a4d51; }
QProgressBar { border: 1px solid #5f6368; border-radius: 3px; text-align: center; }
QProgressBar::chunk { background-color: #1a73e8; }
"""


# ----------------------------------------------------------------------------
# 程序入口
# ----------------------------------------------------------------------------

def m3ule_install_exception_hook() -> None:
    """把未捕获异常写入日志文件，便于排查。"""

    def handler(exc_type, exc_value, exc_tb):
        text = "".join(traceback.format_exception(exc_type, exc_value, exc_tb))
        try:
            log_path = os.path.join(
                m3ule_get_log_dir(), f"crash_{datetime.now():%Y%m%d_%H%M%S}.log")
            with open(log_path, "w", encoding="utf-8") as handle:
                handle.write(text)
        except Exception:
            pass
        sys.__excepthook__(exc_type, exc_value, exc_tb)

    sys.excepthook = handler


def m3ule_create_application(argv) -> QApplication:
    # 先关掉系统加载器的硬错误弹框：否则依赖不满足的库（例如 libmpv 遇到旧版 vulkan-1.dll）
    # 会先弹出一个卡住界面的「无法找到入口」框，而不是让程序自己报告并换内核。
    m3ule_set_loader_error_mode()
    application = QApplication(argv)
    application.setApplicationName(M3ULE_APP_NAME_EN)
    application.setApplicationDisplayName(M3ULE_APP_NAME_CN)
    application.setOrganizationName(M3ULE_APP_ORG)
    application.setApplicationVersion(M3ULE_VERSION)
    icon_path = m3ule_get_icon_path()
    if icon_path:
        application.setWindowIcon(QIcon(icon_path))
    return application


def m3ule_settings_read_bool(settings, key: str, default: bool = False) -> bool:
    """从 QSettings 读布尔值（INI 里存的是 "true"/"false" 字符串）。"""
    try:
        value = settings.value(key, default)
    except Exception:  # noqa: BLE001
        return default
    if isinstance(value, bool):
        return value
    text = str(value or "").strip().lower()
    if text in ("1", "true", "yes", "on"):
        return True
    if text in ("0", "false", "no", "off", ""):
        return False
    return default


def m3ule_remote_session_detected() -> bool:
    """远程桌面会话（保留：用于播放诊断提示与 UI 说明）。"""
    name = str(os.environ.get("SESSIONNAME", "") or "").strip().upper()
    if name.startswith("RDP"):
        return True
    return bool(os.environ.get("M3ULE_FORCE_SOFTWARE_RENDER"))


def m3ule_settings_read_text(key: str, default: str = "") -> str:
    """从 settings.ini 读字符串（供配置管理器之外、甚至 QApplication 之前使用）。"""
    try:
        settings = QSettings(m3ule_get_settings_path(), QSettings.IniFormat)
        value = settings.value(key, default)
        return default if value is None else str(value)
    except Exception:  # noqa: BLE001
        return default


def m3ule_shorten_url_text(url: str, limit: int = 68) -> str:
    """把过长的链接截断显示（完整地址放在控件提示里），避免把窗口顶宽。"""
    text = str(url or "")
    if len(text) <= limit:
        return text
    return text[:limit] + "…"


def m3ule_player_backend_key(text) -> str:
    """把「播放内核」设置的文本（键或中文标签）归一化成键。

    只提供 FFmpeg 与 VLC 两个内核；旧版本的取值（HTML5 / mpv / 自动）统一迁移到默认内核，
    这样升级后不会因为设置里存着已移除的内核而「什么都播不了」。
    """
    raw = str(text or "").strip()
    if not raw:
        return M3ULE_PLAYER_BACKEND_DEFAULT
    if raw in M3ULE_PLAYER_BACKEND_LABELS:
        return raw
    if raw in M3ULE_PLAYER_BACKEND_LEGACY:
        return M3ULE_PLAYER_BACKEND_LEGACY[raw]
    for key, label in M3ULE_PLAYER_BACKEND_LABELS.items():
        if raw == label or raw.startswith(label[:4]):
            return key
    lowered = raw.casefold()
    if "vlc" in lowered:
        return "vlc"
    if "mpv" in lowered or "html5" in lowered or "webengine" in lowered:
        return M3ULE_PLAYER_BACKEND_DEFAULT
    return M3ULE_PLAYER_BACKEND_DEFAULT


def m3ule_player_backend_label(key: str) -> str:
    return M3ULE_PLAYER_BACKEND_LABELS.get(m3ule_player_backend_key(key),
                                           M3ULE_PLAYER_BACKEND_LABELS[M3ULE_PLAYER_BACKEND_DEFAULT])


def m3ule_library_loadable(path: str, refresh: bool = False) -> tuple:
    """尝试把库载入当前进程，返回 (是否成功, 说明)；结果按文件指纹缓存。

    加载前先关掉 Windows 加载器的硬错误弹框：否则第一次加载失败会弹出一个卡住界面的
    「无法找到入口」模态框，由程序自己写日志、给出可读原因更合适。
    """
    import ctypes
    target = os.path.abspath(str(path or ""))
    key = (os.path.basename(target).lower(), target)
    if not refresh and key in M3ULE_LIBRARY_LOAD_CACHE:
        return M3ULE_LIBRARY_LOAD_CACHE[key]
    if not os.path.isfile(target):
        result = (False, f"文件不存在：{target}")
        M3ULE_LIBRARY_LOAD_CACHE[key] = result
        return result
    m3ule_set_loader_error_mode()
    try:
        handle = ctypes.CDLL(target)
    except Exception as exc:  # noqa: BLE001
        code = getattr(exc, "winerror", None)
        if code == 126:
            reason = "找不到依赖模块（WinError 126）"
        elif code == 127:
            reason = "依赖接口缺失（WinError 127，典型是依赖 DLL 版本过旧）"
        elif code == 193:
            reason = "不是有效的 Win32 程序（WinError 193，通常是位数不一致）"
        else:
            reason = f"{type(exc).__name__}: {exc}"
        result = (False, f"无法加载：{reason}")
    else:
        M3ULE_PRELOADED_MODULES.setdefault(os.path.basename(target).lower(), handle)
        result = (True, "可以加载")
    M3ULE_LIBRARY_LOAD_CACHE[key] = result
    return result


def m3ule_set_loader_error_mode() -> int:
    """关闭 Windows 加载器的硬错误弹框，返回设置前的模式（非 Windows 返回 0）。

    双击 bat / 无控制台启动时，依赖解析失败会被系统用**模态框**报告
    （典型文案：「无法定位程序输入点 xxx 于动态链接库 yyy 上」），界面被卡住，
    而且看不出是程序在加载哪个库。关掉之后，失败会以错误码返回，
    由程序自己写日志、自动修复依赖或换内核，并给出可读原因。
    """
    if os.name != "nt":
        return 0
    try:
        import ctypes
        return int(ctypes.WinDLL("kernel32").SetErrorMode(M3ULE_LOADER_ERROR_MODE_FLAGS))
    except Exception:  # noqa: BLE001
        return 0


def m3ule_player_backend_library_key(key: str) -> str:
    """内核对应的「库文件路径」设置键（FFmpeg 内核由 PySide6 自带，返回空串）。"""
    key = m3ule_player_backend_key(key)
    if key == "vlc":
        return "player/libvlc_path"
    return ""


def m3ule_player_backend_library_names(key: str) -> tuple:
    return M3ULE_LIBVLC_NAMES


def m3ule_player_backend_set_library(key: str, path: str) -> bool:
    """记录 / 清除某个内核的库文件路径（空串表示清除），返回设置后的可用性。

    写入的是程序设置（`player/libvlc_path`），这样用户不必去改环境变量就能让 VLC 内核可用。
    """
    setting_key = m3ule_player_backend_library_key(key)
    if not setting_key:
        return False
    text = str(path or "").strip()
    if text and not os.path.isfile(text):
        return False
    settings = QSettings(m3ule_get_settings_path(), QSettings.IniFormat)
    settings.setValue(setting_key, text)
    settings.sync()
    return m3ule_player_backend_status(key)[0]


def m3ule_player_backend_library_hint(key: str) -> str:
    """给用户看的「怎么让它可用」提示（未安装时显示在对话框与设置页）。"""
    key = m3ule_player_backend_key(key)
    if key == "qtmm":
        return ("FFmpeg 内核由 PySide6 自带（Qt 多媒体 + FFmpeg 后端），无需额外安装。\n"
                "源码运行：pip install PySide6。\n"
                "编译版显示不可用或「没有报错但不出画」时，多半是打包时漏了 Qt 的 multimedia 插件"
                "（ffmpegmediaplugin.dll）——见《软件升级迭代记录.md》里的编译说明。")
    if key == "vlc":
        return ("VLC 内核需要两样东西：①本机已安装的 VLC（提供 libvlc.dll）；"
                "②Python 绑定 python-vlc（命令行执行 pip install python-vlc，它只是绑定，不含 VLC 本体）。\n"
                "VLC 装好即可用（程序会查各磁盘的 Program Files\\VideoLAN\\VLC 与注册表 InstallDir）；\n"
                "便携版 / 自定义目录时：把 libvlc.dll 所在目录指给程序（「浏览…」选 libvlc.dll，"
                f"或用环境变量 {M3ULE_LIBVLC_DIR_ENV} 指定安装目录），"
                "也可把整个 VLC 目录复制到程序目录下的 vlc\\ 子目录。\n"
                "都没有时可用 winget install VideoLAN.VLC 安装，或到 https://www.videolan.org/vlc/ 下载。")
    return "未知播放内核。"


def m3ule_find_library(names, env_value: str = "", extra_dirs=()) -> str:
    """按顺序查找本地库文件（env 指定 → 程序目录子目录 → 程序目录 → PATH → 常见安装目录）。"""
    if env_value:
        candidate = os.path.abspath(os.path.expanduser(env_value))
        if os.path.isfile(candidate):
            return candidate
    program_dir = m3ule_get_program_dir()
    search_dirs = [os.path.join(program_dir, "vlc"),
                   os.path.join(program_dir, "libvlc"), program_dir]
    search_dirs.extend(extra_dirs)
    for directory in search_dirs:
        for name in names:
            candidate = os.path.join(directory, name)
            if os.path.isfile(candidate):
                return candidate
    for name in names:
        found = shutil.which(name)
        if found:
            return found
    return ""


def m3ule_program_files_dirs() -> list:
    """本机所有磁盘上的 Program Files / Program Files (x86) 目录（含装在非 C: 盘的软件）。"""
    dirs = []
    for variable in ("ProgramFiles", "ProgramFiles(x86)"):
        value = os.environ.get(variable, "")
        if value and os.path.isdir(value):
            dirs.append(value)
    for letter in "CDEFGHIJ":
        for name in ("Program Files", "Program Files (x86)"):
            candidate = f"{letter}:\\{name}"
            if candidate not in dirs and os.path.isdir(candidate):
                dirs.append(candidate)
    return dirs


def m3ule_registry_install_dirs(subkey: str) -> list:
    """从注册表读取某软件的安装目录（VLC 等会写 `InstallDir`），读不到返回空列表。"""
    if os.name != "nt":
        return []
    try:
        import winreg  # type: ignore
    except Exception:  # noqa: BLE001
        return []
    found = []
    for root in (winreg.HKEY_LOCAL_MACHINE, winreg.HKEY_CURRENT_USER):
        for prefix in ("SOFTWARE", "SOFTWARE\\WOW6432Node"):
            try:
                with winreg.OpenKey(root, f"{prefix}\\{subkey}") as handle:
                    value, _kind = winreg.QueryValueEx(handle, "InstallDir")
            except OSError:
                continue
            text = str(value or "").strip()
            if text and os.path.isdir(text) and text not in found:
                found.append(text)
    return found


def m3ule_common_install_dirs(subpath: str) -> list:
    """某软件的常见安装目录：所有磁盘的 `Program Files\\<subpath>` + 注册表里的 InstallDir。

    `subpath` 用反斜杠分隔（例如 `VideoLAN\\VLC`）；不存在的目录会被过滤掉。
    """
    candidates = []
    for base in m3ule_program_files_dirs():
        candidates.append(os.path.join(base, *subpath.split("\\")))
    candidates.extend(m3ule_registry_install_dirs(subpath))
    ordered = []
    for item in candidates:
        if os.path.isdir(item) and item not in ordered:
            ordered.append(item)
    return ordered


def m3ule_which_dir(executable: str) -> str:
    """某个可执行文件（如 vlc.exe / mpv.exe）所在目录；PATH 里没有则返回空串。"""
    found = shutil.which(str(executable or ""))
    return os.path.dirname(found) if found else ""


def m3ule_vlc_install_dirs() -> list:
    """VLC 安装目录候选：所有磁盘的 Program Files、注册表 InstallDir、PATH 里 vlc.exe 的目录。"""
    dirs = m3ule_common_install_dirs(r"VideoLAN\VLC")
    for item in (m3ule_which_dir("vlc.exe"), os.path.join(
            os.environ.get("LOCALAPPDATA", ""), "Programs", "VideoLAN", "VLC")):
        if item and os.path.isdir(item) and item not in dirs:
            dirs.append(item)
    return dirs


def m3ule_find_libvlc() -> str:
    """定位 libvlc（设置/环境变量 → 程序目录 → PATH → 各磁盘 Program Files\\VideoLAN\\VLC → 注册表）。

    以前只查 `C:\\Program Files\\VideoLAN\\VLC`，装在 D: 等其它盘（或自定义目录）的 VLC 会被漏掉，
    于是「明明装了 VLC + python-vlc，却提示未找到 libvlc.dll」。现在按所有磁盘 + 注册表 InstallDir 找。
    """
    env_file = m3ule_settings_read_text("player/libvlc_path")
    if not env_file:
        env_file = os.environ.get(M3ULE_LIBVLC_PATH_ENV, "")
    if not env_file:
        env_dir = os.environ.get(M3ULE_LIBVLC_DIR_ENV, "")
        if env_dir:
            candidate = os.path.join(env_dir, M3ULE_LIBVLC_NAMES[0])
            if os.path.isfile(candidate):
                env_file = candidate
    return m3ule_find_library(M3ULE_LIBVLC_NAMES, env_file, m3ule_vlc_install_dirs())


def m3ule_vlc_plugins_dir(lib_path: str) -> str:
    """libvlc 旁边的 `plugins` 目录（VLC 的解码/分离器插件都在这里）；没有则返回空串。"""
    directory = os.path.dirname(os.path.abspath(str(lib_path or "")))
    if not directory:
        return ""
    plugins = os.path.join(directory, "plugins")
    return plugins if os.path.isdir(plugins) else ""


def m3ule_player_backend_search_hint(key: str) -> str:
    """「都找过哪些地方」的说明（用于未找到库文件时告诉用户程序已经尽力了）。"""
    key = m3ule_player_backend_key(key)
    if key == "vlc":
        dirs = m3ule_vlc_install_dirs()
        return ("已查找：程序目录 vlc\\ / libvlc\\、PATH、各磁盘的 Program Files\\VideoLAN\\VLC、"
                "注册表 InstallDir"
                + ("（注册表指向 " + dirs[0] + "）" if dirs else ""))
    return ""


def m3ule_player_backend_status(key: str) -> tuple:
    """返回 (是否可用, 说明)。两个内核都直连拉流（不需要本机中转）。"""
    key = m3ule_player_backend_key(key)
    if key == "qtmm":
        if M3ULE_QTMM_AVAILABLE:
            return True, "PySide6 QtMultimedia + FFmpeg 后端可用"
        return False, (f"QtMultimedia 不可用（{M3ULE_QTMM_ERROR}）"
                       "——源码运行时执行 pip install PySide6；编译版请确认打包时带上了 "
                       "Qt 的 multimedia 插件（见《软件升级迭代记录.md》的编译说明）")
    if key == "vlc":
        if importlib.util.find_spec("vlc") is None:
            return False, ("未安装 python-vlc（在命令行执行 pip install python-vlc）"
                           "—— 注意它是 Python 绑定，还需要本机的 VLC（libvlc.dll）")
        path = m3ule_find_libvlc()
        if path:
            loadable, note = m3ule_library_loadable(path)
            if not loadable:
                return False, f"libvlc 无法加载：{path}｜{note}"
            if not m3ule_vlc_plugins_dir(path):
                return True, f"libvlc：{path}（未找到 plugins 目录，VLC 安装可能不完整）"
            return True, f"libvlc：{path}"
        return False, ("python-vlc 已安装，但未找到 libvlc.dll（也就是 VLC 本体没装或装在别处）。"
                       "装好 VLC 即可，或点「指定库文件…」指到 libvlc.dll。"
                       + m3ule_player_backend_search_hint("vlc"))
    return False, "未知播放内核"


def m3ule_player_backend_report() -> list:
    """本机各播放内核的可用性报告：[(key, label, 可用, 说明)]。"""
    return [(key, label, *m3ule_player_backend_status(key))
            for key, label in M3ULE_PLAYER_BACKEND_LABELS.items()]


def m3ule_player_backend_chain(configured, available=None) -> list:
    """内核尝试顺序：指定的内核优先，其后按默认优先级补齐（只有一个内核可用时就只用它）。

    available 为 None 时使用真实可用性；也可传入 {key: bool} 供测试注入。
    """
    key = m3ule_player_backend_key(configured)

    def _usable(candidate: str) -> bool:
        if available is None:
            return m3ule_player_backend_status(candidate)[0]
        return bool(available.get(candidate, False))

    ordered = [key] if _usable(key) else []
    ordered += [item for item in M3ULE_PLAYER_BACKEND_CHAIN
                if item != key and _usable(item)]
    return ordered or [key]


def m3ule_player_backend_needs_relay(key: str) -> bool:
    """两个内核都直连拉流（本机中转只用于「系统浏览器播放页」）。"""
    return False


def m3ule_player_backend_report_text() -> str:
    lines = ["本机可用播放内核（只有两个）：", ""]
    for _key, label, ok, reason in m3ule_player_backend_report():
        lines.append(f"{'✔' if ok else '✘'} {label}：{'可用' if ok else '不可用'}")
        lines.append(f"    {reason}")
    lines.extend([
        "",
        f"默认内核：{M3ULE_PLAYER_BACKEND_LABELS[M3ULE_PLAYER_BACKEND_DEFAULT]}"
        "（旧版本里的 HTML5 / mpv / 自动 设置会自动迁移到它）",
        "说明：",
        "· 两个内核都基于 FFmpeg 直接拉流，互不依赖：当前内核打不开画面时自动换另一个；",
        "· FFmpeg 内核由 PySide6 自带，不需要额外安装；编译版请确认打包时带上了 Qt 的 "
        "multimedia 插件（缺少 ffmpegmediaplugin.dll 时会安静地不出画，见编译说明）；",
        "· VLC 内核需要本机已安装 VLC（提供 libvlc.dll）并 pip install python-vlc，",
        "  可在设置页或播放弹窗里用「指定库文件…」直接指到 libvlc.dll；",
        "· 两个都不行时用「在系统浏览器打开」（Chrome/Edge 解码支持最完整）或"
        "「用播放器打开」（系统里已装的 VLC / mpv）。",
    ])
    return "\n".join(lines)


def m3ule_player_selftest_restore_backend(config, saved_backend: str) -> bool:
    """自检结束后把用户的播放内核设置改回自检之前的值（自检不应该改用户设置）。"""
    if config is None or saved_backend == "":
        return False
    if config.cfg_get("player/backend") == saved_backend:
        return False
    config.cfg_set("player/backend", saved_backend)
    return True


def m3ule_run_player_selftest(stream_url: str, wait_seconds: float = 30.0,
                              backend: str = "", report_path: str = "") -> int:
    """无人值守自检：用指定的播放内核真正拉流解码，验证「能出画」。

    与旧的内嵌浏览器自检不同，这里直接看内核解出了多少帧 —— 因此源码运行与
    **编译后的 exe** 都能用它确认 FFmpeg（Qt 多媒体）链路是否完好：
    编译时漏掉 Qt 的 multimedia 插件正是「exe 里 ffmpeg 播放不了」的原因，
    那种情况下本自检会明确报「未出画」。

    结论会写入报告文件（编译版没有控制台，看文件最方便）：
    `--selftest-report=路径` 指定，默认写到程序目录的 `selftest-player.txt`。

    自检过程中会真正切换内核（`dlg_request_backend` 会把选择写进设置），
    所以结束时会把 `player/backend` 恢复成自检开始前的值 —— 跑自检不会改用户的播放内核设置。

    退出码：0 = 出画；1 = 超时或环境不支持（含全部内核都不可用）。
    """
    report: list = []

    def say(text: str = "") -> None:
        print(text)
        report.append(text)

    application = m3ule_create_application(sys.argv[:1])
    window = M3ULiveEditorMainWindow()
    window.show()
    config = window.wnd_config_manager()
    saved_backend = config.cfg_get("player/backend")
    wanted = m3ule_player_backend_key(backend) if backend else ""
    chain = [wanted] if wanted else m3ule_player_backend_chain(
        config.cfg_get("player/backend"))
    say(f"[selftest] 播放地址：{stream_url}")
    say(f"[selftest] 尝试内核：{'、'.join(m3ule_player_backend_label(k) for k in chain)}")
    for _key, label, ok, reason in m3ule_player_backend_report():
        say(f"[selftest]   {'✔' if ok else '✘'} {label}：{reason}")
    entry = M3ULiveEditorEntry(url=stream_url, title="selftest")
    dialog = M3ULiveEditorHtml5PlayerDialog(window, [entry], 0, parent=window)
    dialog.show()
    result = 1
    for key in chain:
        if not dialog.dlg_request_backend(key, notify=False):
            say(f"[selftest] {m3ule_player_backend_label(key)} 不可用，跳过")
            continue
        backend_key = dialog.dlg_current_backend()
        if backend_key != key:
            say(f"[selftest] {m3ule_player_backend_label(key)} 启动失败，"
                f"已自动换用 {m3ule_player_backend_label(backend_key)}")
        active_label = m3ule_player_backend_label(backend_key)
        frames = 0
        deadline = time.time() + max(8.0, wait_seconds)
        while time.time() < deadline:
            application.processEvents()
            time.sleep(0.05)
            frames, position = dialog.dlg_backend_progress()
            if frames:
                say(f"[selftest] {active_label} 出画：已解码 {frames} 帧，位置 {position} ms")
                say(f"[selftest] 结果: 成功（{active_label} 能正常播放）")
                result = 0
                break
        if result == 0:
            break
        say(f"[selftest] {active_label} 未出画：{dialog.dlg_backend_status_text()}")
    if result != 0:
        say("[selftest] 结果: 失败（没有任何内核出画）")
        for line in dialog.dlg_build_diagnostics_lines():
            say("[selftest]   " + line)
        say("[selftest] 提示：编译版出现本结果时，请确认打包参数里有 "
            "--include-qt-plugins=multimedia（缺少 multimedia 插件时 Qt 多媒体没有媒体后端，"
            "表现为「无报错但不出画」）。")
    dialog.close()
    window.close()
    if m3ule_player_selftest_restore_backend(config, saved_backend):
        # 自检用 dlg_request_backend() 真正切换过内核，那个入口会把选择写进设置；
        # 这里改回去，免得「测一次」就把用户的播放内核设置换了。
        say(f"[selftest] 已把播放内核设置恢复为：{m3ule_player_backend_label(saved_backend)}")
    if not report_path:
        report_path = os.path.join(m3ule_get_program_dir(), "selftest-player.txt")
    try:
        with open(report_path, "w", encoding="utf-8", newline="") as handle:
            handle.write("\n".join(report) + "\n")
        print(f"[selftest] 报告已写入：{report_path}")
    except OSError as exc:  # noqa: BLE001
        print(f"[selftest] 报告写入失败：{exc}")
    return result


def main() -> int:
    m3ule_load_env_file()
    m3ule_install_exception_hook()
    selftest_backend = ""
    selftest_report = ""
    for argument in sys.argv[1:]:
        if argument.startswith("--selftest-player-backend="):
            selftest_backend = argument.split("=", 1)[1].strip()
        elif argument.startswith("--selftest-report="):
            selftest_report = argument.split("=", 1)[1].strip()
    for argument in sys.argv[1:]:
        if argument.startswith("--selftest-player="):
            return m3ule_run_player_selftest(argument.split("=", 1)[1].strip(),
                                            backend=selftest_backend,
                                            report_path=selftest_report)
        if argument.startswith("--selftest-html5="):
            # 兼容旧参数名（内嵌播放器已只剩 FFmpeg / VLC 两个内核）
            return m3ule_run_player_selftest(argument.split("=", 1)[1].strip(),
                                            backend=selftest_backend,
                                            report_path=selftest_report)
    application = m3ule_create_application(sys.argv)
    window = M3ULiveEditorMainWindow()
    if not window.wnd_icon_available():
        window.wnd_append_log("未找到 icon.ico，已跳过窗口图标设置。")
    window.show()
    window.wnd_append_log(
        "弹窗播放：" + str(window.wnd_config_manager().cfg_get("player/html5_mode"))
        + "（内核：" + m3ule_player_backend_label(m3ule_player_backend_key(
            window.wnd_config_manager().cfg_get("player/backend"))) + "）")
    for argument in sys.argv[1:]:
        # 供自动化冒烟使用：启动主界面并在指定秒数后自动退出
        if argument.startswith("--selftest-ui="):
            seconds = m3ule_safe_float(argument.split("=", 1)[1], 0.0)
            QTimer.singleShot(int(max(1.0, seconds) * 1000), application.quit)
    opened_by_argument = False
    for argument in sys.argv[1:]:
        if os.path.isfile(argument):
            window.wnd_open_path(argument)
            opened_by_argument = True
            break
    if not opened_by_argument:
        # 记住上次打开的文件：没有命令行参数时自动恢复，省去每次重新选文件
        window.wnd_auto_open_last_file()
    return application.exec()


if __name__ == "__main__":
    sys.exit(main())


