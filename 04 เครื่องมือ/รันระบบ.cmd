@echo off
setlocal EnableExtensions DisableDelayedExpansion
chcp 65001 >nul

set "SMS_SCRIPT_DIR=%~dp0"
set "SMS_MACHINE_CONFIG=%SMS_SCRIPT_DIR%machine.json"

if not exist "%SMS_MACHINE_CONFIG%" (
  echo [ERROR] machine.json was not found:
  echo %SMS_MACHINE_CONFIG%
  pause
  exit /b 2
)

powershell.exe -NoProfile -ExecutionPolicy Bypass -Command "$config = Get-Content -LiteralPath '%SMS_MACHINE_CONFIG%' -Raw | ConvertFrom-Json; $qgisPython = [string]$config.qgis.python_bat; if (-not (Test-Path -LiteralPath $qgisPython -PathType Leaf)) { Write-Error ('QGIS Python was not found: ' + $qgisPython); exit 2 }; & $qgisPython '%SMS_SCRIPT_DIR%sms_pipeline.py' menu; exit $LASTEXITCODE"
set "SMS_EXIT_CODE=%ERRORLEVEL%"

echo.
if not "%SMS_EXIT_CODE%"=="0" echo The system finished with exit code %SMS_EXIT_CODE%.
pause
exit /b %SMS_EXIT_CODE%
