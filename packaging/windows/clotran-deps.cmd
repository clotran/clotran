@echo off
rem clotran-deps, from a clotran release for Windows: its sh script, run by
rem the sh clotran carries (see clotran.cmd).
setlocal
rem clotran reads and writes UTF-8: the console's code page too, while it
rem runs, put back as it was after
for /f "tokens=2 delims=:" %%a in ('chcp') do set "CLOTRAN_CP=%%a"
chcp 65001 >nul
set "CLOTRAN_SH=%~dp0..\lib\clotran\sh.exe"
if not defined HOME set "HOME=%USERPROFILE%"
"%CLOTRAN_SH%" "%~dp0..\lib\clotran-deps\bin\clotran-deps" %*
set "CLOTRAN_RC=%ERRORLEVEL%"
if defined CLOTRAN_CP chcp %CLOTRAN_CP% >nul
exit /b %CLOTRAN_RC%
