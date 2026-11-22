# M3U_Live_Editor v1.8.4

> **一句话**：M3U_Live_Editor —— 台标自动匹配。
>
> **适合谁**：想直接用现成工具、不想自己写代码的 Windows 用户。
>
> **解决什么问题**：把「台标自动匹配」这件事做成开箱即用的程序 —— 下载解压、装上依赖、双击就能跑。

---

## 目录

- [1. 这是什么](#1-这是什么)
- [2. 零基础入门（5 分钟跑起来）](#2-零基础入门5-分钟跑起来)
- [3. 功能与界面](#3-功能与界面)
- [4. 命令行参数](#4-命令行参数)
- [5. 配置文件与数据](#5-配置文件与数据)
- [6. 工作原理（技术参考）](#6-工作原理技术参考)
- [7. 排错手册](#7-排错手册)
- [8. 常见问题 FAQ](#8-常见问题-faq)
- [9. 目录结构](#9-目录结构)
- [10. 开发与构建](#10-开发与构建)
- [11. 已知限制与安全说明](#11-已知限制与安全说明)
- [12. 许可](#12-许可)

## 1. 这是什么

| 项目 | 说明 |
| --- | --- |
| 程序名 | `M3U_Live_Editor` |
| 当前版本 | v1.8.4 |
| 主程序 | `M3U_Live_Editor.py` |
| 界面技术 | PySide6（Qt6 官方 Python 绑定） |
| 语言 / 运行平台 | Python 3.10 / Windows |
| 源码规模 | 根目录及子模块共 12 个 .py 文件 |
| 仓库 | https://github.com/duma520/M3U_Live_Editor |

## 2. 零基础入门（5 分钟跑起来）

### 第 1 步：装 Python

1. 打开 <https://www.python.org/downloads/windows/>，下载 Python 3.10 或更新版本。
2. 安装时**务必勾选** `Add python.exe to PATH`（安装向导第一页最下方）。
3. 装完按 `Win + R` 输入 `cmd`，敲 `python --version`，能看到版本号就成功了。

### 第 2 步：拿到源码

- **下载压缩包**：在本仓库 Releases 页下载 `M3U_Live_Editor-*.zip`，解压到任意目录。
- **git 克隆**：`git clone https://github.com/duma520/M3U_Live_Editor.git`

### 第 3 步：装依赖

在源码目录打开命令行，执行：

```
pip install PySide6 requests urllib3 vlc
```

> 清单是从源码的实际 import 汇总出来的；若某个包名不准确，以 pip 报错提示的正确包名为准。

### 第 4 步：启动

```bat
python M3U_Live_Editor.py
```

目录里还带了 `1.bat`，双击等同于上面的命令（前提是 Python 在 PATH 里）。

## 3. 功能与界面

> 本节只列源码里能确认的事实；具体按钮与交互以运行后的界面为准。

| 维度 | 实际情况 |
| --- | --- |
| 界面框架 | PySide6（Qt6 官方 Python 绑定） |
| 是否有 main 入口 | 是，可直接 python 主程序.py 运行 |
| 第三方依赖数 | 4 个 |

### 版本变更（来自项目自带迭代记录）

| 版本 | 说明 |
| --- | --- |
| 12201 | 主窗口：`wnd_build_*`（界面，`wnd_build_test_tab`(12569) 含「跳过有效缓存」与缓存按钮行）、`wnd_act_*`（动作处理）、`wnd_relay_server` / `wnd_act_open_in_html5` / `wnd_open_html5_player`、测试流程 `wnd_act_start_test`(14133) / `wnd_collect_test_tasks`(14092) / `wnd_on_test_results` / `wnd_on_test_finished`、持久化 `wnd_save_runtime_settings`(14624) / `wnd_restore_settings`(14681)；**记忆上次文件：`wnd_open_path`(13316) / `wnd_auto_open_last_file`(13342) / 重启程序（v1.5.1）：`wnd_restart_application`(13361)**；**列自定义：`wnd_show_header_context_menu` / `wnd_table_view_mode` / `wnd_table_view_title` / `wnd_set_column_visible` / `wnd_capture_column_layout` / `wnd_apply_column_layout` / `wnd_save_column_layouts` / `wnd_restore_column_layouts` / `wnd_current_column_layout` / `wnd_act_choose_columns` / `wnd_act_reset_columns`**；**差异统计：`wnd_delta_counts` / `wnd_delta_summary_text`**；**缓存 API：`wnd_probe_cache_enabled`(13914) / `wnd_probe_cache_ttl`(13917) / `wnd_should_skip_cached_tests`(13920) / `wnd_cache_total`(13929) / `wnd_refresh_cache_stats`(13936) / `wnd_store_probe_cache`(13951) / `wnd_apply_probe_cache`(13977) / `wnd_clear_entries_probe_cache`(14019) / `wnd_act_apply_probe_cache`(14030) / `wnd_act_clear_probe_cache`(14044) / `wnd_act_clear_selected_cache`(14064) / `wnd_act_prune_probe_cache`(14078)**** |
| 7171 | **★ v1.7.3 自动换行布局（播放弹窗工具栏用）**：`addItem` / `itemAt` / `takeAt` / `sizeHint` / `minimumSize` / `heightForWidth` / `setGeometry` 之外，自有算法 `m3ule_item_size`（把 sizeHint 夹在最小/最大宽度之间）/ `m3ule_flow_layout` / `m3ule_row_count`（给定宽度排几行，供界面自检与冒烟测试） |
| 12201 | `wnd_visible_entries`（当前视图的全部条目，尊重筛选与排序）/ `wnd_html5_entry_list_and_start`（播放列表＋起始索引，供「上一个 / 下一个」整表切换）；`wnd_open_url_in_html5(url, title, entries=…, start_index=…)` 新增可选列表参数（不传则沿用只播一条的旧行为） |
| 12201 | `wnd_sync_id_dialog`（惰性创建频道同步对话框）/ `wnd_act_sync_index_ids`（菜单「工具 → **频道同步…**」，快捷键 `Ctrl+Shift+M`）；动作 `qact_sync_ids` |
| 12201 | **★ 批量修改分组（多选 / 整批）**：`wnd_act_batch_group`（菜单「编辑 → 批量修改分组…」/ 工具栏 / 右键菜单入口，取当前选中与当前列表可见条目交给对话框）/ `wnd_assign_group_to_selection`（右键「加入已有分组」子菜单与「清除分组」一键归组，返回真正改动条数）/ `wnd_after_group_batch`（统一收尾：刷新表格与分组筛选下拉、标记未保存、写日志）/ `wnd_build_group_quick_menu`（「加入已有分组（选中条目）」子菜单，最多列 30 个分组，没选中时给灰色提示）；动作 `qact_batch_group`（`Ctrl+G`） |
| 12201 | **★ 台标自动匹配**：`wnd_act_match_logos`（菜单「工具 → 台标自动匹配…」/ 右键菜单入口；有选中条目时默认只处理选中的那些）/ `wnd_logo_match_dialog`（按范围建对话框，共用文档 / 历史库 / 设置；**v1.8.3：建好后调用一次 `dlg_offer_bundled_library`，第一次打开就把随程序的网络台标库作为默认来源**）/ `wnd_run_logo_match`（真正执行：套用 → 刷新表格、标记未保存、写日志、落盘运行设置）；动作 `qact_match_logos`（`Ctrl+Shift+L`） |
| 12201 | **★ 播放内核只剩 FFmpeg / VLC 的设置迁移**：`wnd_migrate_player_settings`（启动时把旧的 `player/backend` 取值归到默认内核并**写回设置**、把已移除内核遗留的设置键（libmpv 路径与依赖修复、HTML5 渲染方式与回退）从 INI 里 `remove()` 掉，返回「是否有改动」并写日志） |
| 7288 | **★ 同一弹窗只播一路、且不卡界面**：`dlg_backend_widgets`（弹窗内所有非 HTML5 内核控件）/ `dlg_dispose_backend_widget`（停止 → 释放 → 移出界面 → 销毁，换内核时先销毁旧控件；**v1.7.5：后台还在销毁的控件先隐藏挂起，销毁完成后再删**）/ `dlg_release_backends`（释放全部内核的库资源）/ `dlg_stop_all_backends`（停止内嵌播放页与栈内每一个内核控件）/ `dlg_silence_other_backends`（开播前停掉不是本次要用的内核）/ **v1.7.5：`dlg_backend_teardown_pending` / `dlg_wait_backend_teardown`（关闭前最多等 1.5 秒）/ `dlg_start_retired_sweep` / `dlg_sweep_retired_widgets`（300ms 轮询，销毁完才 deleteLater）**；`dlg_play_index` 开头调用 `dlg_silence_other_backends`，`dlg_stop_playback` 改为走 `dlg_stop_all_backends`，`dlg_setup_backend_chain` 换内核时先 `dlg_stop_playback`，`closeEvent` 停止并释放全部内核 |

## 4. 命令行参数

主程序支持的参数（从 argparse 定义抽取）：

| 参数 | 说明 |
| --- | --- |
| `--stage` | （源码未写 help） |
| `--stream-url` | （源码未写 help） |
| `--keep` | 保留临时目录 |

## 5. 配置文件与数据

程序把配置写在自身目录或用户目录下；.gitignore 已排除运行期产生的配置与日志，首次运行会自动生成。

## 6. 工作原理（技术参考）

```
用户操作 → PySide6 → 业务逻辑 → 结果输出
```

- 入口文件 `M3U_Live_Editor.py`，带 if __name__ == '__main__' 保护。
- 依赖的第三方库：`PySide6`、`requests`、`urllib3`、`vlc`。
- 全部业务逻辑在仓库内可见，没有编译产物、没有联网下发代码。

## 7. 排错手册

| 现象 | 原因 | 解决 |
| --- | --- | --- |
| python 不是内部或外部命令 | 安装时没勾 PATH | 重装 Python 并勾选 Add python.exe to PATH，或改用 py 命令 |
| ModuleNotFoundError: No module named xxx | 依赖没装 | 按第 3 步 pip install 对应包 |
| 双击 .bat 一闪而过 | 出错后窗口立即关闭 | 用 cmd 进入目录再执行命令，看清报错 |
| 界面显示乱码 | 控制台编码不是 UTF-8 | 先执行 chcp 65001，或用 python -X utf8 主程序.py |
| 杀毒软件拦截 | 未签名脚本被误判 | 加入信任/白名单；本项目只提供源码，可自行审阅 |

## 8. 常见问题 FAQ

**Q1：需要装 Visual Studio 之类的编译工具吗？**
A：不需要。这里只提供 Python 源码，pip 装的是预编译轮子。

**Q2：能在 macOS / Linux 上跑吗？**
A：本项目按 Windows 环境开发与验证；其他系统未测试，可能需要改路径与系统 API 调用。

**Q3：为什么 Releases 里只有源码 zip，没有 exe？**
A：只分发源码，避免二进制被误判；需要 exe 请按第 10 节自行打包。

**Q4：改了代码怎么运行？**
A：直接 python 主程序.py，改动立即生效，无需编译。

**Q5：数据存在哪？会不会被上传？**
A：只存在本机（程序目录或用户目录）。本程序不含上传逻辑。

**Q6：怎么反馈问题？**
A：到 https://github.com/duma520/M3U_Live_Editor/issues 提 Issue，附上报错原文与复现步骤。

## 9. 目录结构

```
M3U_Live_Editor/
_scaffold/
assets/
backups/
build_output/
data/
libmpv/
.env
.env.example
.gitignore
0_nuitka_pyside6_clang_auto.bat
1.bat
2_debug.bat
M3U_Live_Editor.py
M3U_Live_Editor.spec
README.md
icon.ico
requirements.txt
xteve.m3u
广州珠江宽频的m3u8直播源 - 154.m3u
广州珠江宽频的m3u8直播源 - 999.m3u
软件升级迭代记录.md
M3U_Live_Editor\Cryptodome/
M3U_Live_Editor\PySide6/
M3U_Live_Editor\assets/
M3U_Live_Editor\backports/
M3U_Live_Editor\backups/
M3U_Live_Editor\bcj/
M3U_Live_Editor\certifi/
M3U_Live_Editor\charset_normalizer/
M3U_Live_Editor\cryptography/
M3U_Live_Editor\data/
M3U_Live_Editor\inflate64/
M3U_Live_Editor\pyppmd/
M3U_Live_Editor\shiboken6/
M3U_Live_Editor\simplejson/
M3U_Live_Editor\M3U_Live_Editor.exe
M3U_Live_Editor\QtWebEngineProcess.exe
M3U_Live_Editor\_brotli.pyd
M3U_Live_Editor\_bz2.pyd
M3U_Live_Editor\_cffi_backend.pyd
M3U_Live_Editor\_ctypes.pyd
M3U_Live_Editor\_decimal.pyd
M3U_Live_Editor\_hashlib.pyd
M3U_Live_Editor\_lzma.pyd
```

## 10. 开发与构建

- 直接运行（开发态）：`python M3U_Live_Editor.py`
- 语法自检：`python -m py_compile M3U_Live_Editor.py`
- 打包 exe（可选）：装 pyinstaller 后执行 `pyinstaller -F -w M3U_Live_Editor.py`

## 11. 已知限制与安全说明

- 只提供源码，不提供预编译二进制。
- 仓库不含任何凭据；.env / *.pem / *.key / 日志与运行期数据均在 .gitignore 中排除。
- 若程序需要联网，请在源码中确认目标地址后再运行。

## 12. 许可

AGPL-3.0，详见仓库根目录 LICENSE。
