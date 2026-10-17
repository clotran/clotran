@echo off
rem clotran-deps, from a clotran release for Windows: clotran.deps/-main on
rem the clotran beside it, with no shell.
setlocal
for /f "tokens=2 delims=:" %%a in ('chcp') do set "CLOTRAN_CP=%%a"
chcp 65001 >nul
if not defined HOME set "HOME=%USERPROFILE%"
set "CLOTRAN_PATH=%~dp0..\lib\clotran-deps\src"
"%~dp0..\lib\clotran\clotran-bin.exe" --launch -m clotran.deps %*
set "CLOTRAN_RC=%ERRORLEVEL%"
if defined CLOTRAN_CP chcp %CLOTRAN_CP% >nul
exit /b %CLOTRAN_RC%
