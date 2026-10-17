@echo off
rem clotran, from a clotran release for Windows: clotran-bin.exe --launch
rem is the command itself (clotran.launcher), with no shell.
setlocal
rem clotran reads and writes UTF-8: the console's code page too, while it
rem runs, put back as it was after
for /f "tokens=2 delims=:" %%a in ('chcp') do set "CLOTRAN_CP=%%a"
chcp 65001 >nul
if not defined HOME set "HOME=%USERPROFILE%"
"%~dp0..\lib\clotran\clotran-bin.exe" --launch %*
set "CLOTRAN_RC=%ERRORLEVEL%"
if defined CLOTRAN_CP chcp %CLOTRAN_CP% >nul
exit /b %CLOTRAN_RC%
