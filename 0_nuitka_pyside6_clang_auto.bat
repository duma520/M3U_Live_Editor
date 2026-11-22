nuitka --standalone ^
    --enable-plugin=pyside6 ^
    --windows-console-mode=disable ^
    --windows-icon-from-ico=icon.ico ^
    --include-data-files=icon.ico=icon.ico ^
    --include-data-dir=assets=assets ^
    --include-data-files=data\*.csv=data/ ^
    --include-qt-plugins=multimedia ^
    --include-package=requests ^
    --include-package=certifi ^
    --include-package=urllib3 ^
    --include-package=charset_normalizer ^
    --include-package=idna ^
    --follow-imports ^
    --jobs=4 ^
    --clang ^
    --remove-output ^
    --output-dir=build_output ^
    M3U_Live_Editor.py

rem NOTE (v1.8.3): data\*.csv packages the shipped logo library
rem   (data\<Chinese file name>.csv, used by "logo auto match" -> "import network logo library").
rem   Wildcard and pure ASCII on purpose: this .bat has to stay readable no matter
rem   which console code page (936 / 65001 / 437) runs it. Keep it ASCII-only.
rem   Non-ASCII build inputs would need this file re-encoded to the console code page,
rem   so reference them with wildcards or rename them instead.
rem
rem NOTE (v1.8.4): --include-qt-plugins=multimedia is REQUIRED for playback in the
rem   compiled build. Nuitka's "sensible" Qt plugin set only covers "mediaservice"
rem   (the Qt5 name for that plugin family); Qt6 ships its media backends in the
rem   "multimedia" family, so without this flag the build has qt6multimedia.dll but
rem   no ffmpegmediaplugin.dll -> Qt Multimedia has no backend and playback silently
rem   fails (no error, zero frames). Verified with Nuitka 4.0.7: with the flag the
rem   FFmpeg runtime DLLs (avcodec/avformat/avutil/swresample/swscale) are bundled too.
rem   Self test after building:
rem     M3U_Live_Editor.exe --selftest-player=<m3u8 url>
rem   (prints decoded frame count and exits 0 only when a frame was decoded).
