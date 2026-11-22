# -*- mode: python ; coding: utf-8 -*-
# M3U 直播源编辑管理系统 - PyInstaller 打包配置
# 用法：pyinstaller M3U_Live_Editor.spec
# 注意：主程序为唯一编译源 M3U_Live_Editor.py
#
# ★ v1.8.4 起播放内核只有 FFmpeg（Qt 多媒体）与 VLC：Qt6 的媒体后端在
#   `PySide6/plugins/multimedia/` 里（ffmpegmediaplugin.dll），
#   PyInstaller 的默认 Qt 收集**不保证**带上它；漏掉时表现为「编译后 ffmpeg 播放不了」
#   （无报错、不出画）。因此这里显式收集该插件目录与 FFmpeg 运行库。

import glob
import os.path

import PySide6

block_cipher = None

_pyside6_dir = os.path.dirname(os.path.abspath(PySide6.__file__))
_multimedia_plugin_dir = os.path.join(_pyside6_dir, "plugins", "multimedia")
_qt_plugins = []
if os.path.isdir(_multimedia_plugin_dir):
    _qt_plugins.append((_multimedia_plugin_dir, "PySide6/plugins/multimedia"))
# Qt6 的 FFmpeg 后端运行库（avcodec / avformat / avutil / swresample / swscale）
_ffmpeg_dlls = [
    (path, ".") for pattern in ("av*.dll", "sw*.dll")
    for path in glob.glob(os.path.join(_pyside6_dir, pattern))
]

a = Analysis(
    ['M3U_Live_Editor.py'],
    pathex=[],
    binaries=_ffmpeg_dlls,
    datas=[('icon.ico', '.'),
           ('assets/hls.min.js', 'assets'),
           ('data/*.csv', 'data')] + _qt_plugins,  # v1.8.3：随程序的台标库
    hiddenimports=[
        'requests',
        'urllib3',
        'certifi',
        'charset_normalizer',
        'idna',
    ],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    win_no_prefer_redirects=False,
    win_private_assemblies=False,
    cipher=block_cipher,
    noarchive=False,
)
pyz = PYZ(a.pure, a.zipped_data, cipher=block_cipher)

exe = EXE(
    pyz,
    a.scripts,
    [],
    exclude_binaries=True,
    name='M3U_Live_Editor',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    console=False,
    disable_windowed_traceback=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
    icon='icon.ico',
)
coll = COLLECT(
    exe,
    a.binaries,
    a.zipfiles,
    a.datas,
    strip=False,
    upx=True,
    upx_exclude=[],
    name='M3U_Live_Editor',
)
