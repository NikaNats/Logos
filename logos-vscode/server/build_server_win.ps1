Param(
  [string]$Python = "py"
)

$ErrorActionPreference = "Stop"

$repoRoot = Split-Path -Parent $PSScriptRoot
$serverDir = $PSScriptRoot
$distDir = Join-Path $serverDir "bin\win32"
$workDir = Join-Path $serverDir "build\pyinstaller"

Write-Host "Building Logos LSP server (Windows) with PyInstaller..."
Write-Host "Server dir: $serverDir"
Write-Host "Dist dir:   $distDir"

New-Item -ItemType Directory -Force -Path $distDir | Out-Null
New-Item -ItemType Directory -Force -Path $workDir | Out-Null

# Install build deps into the current Python environment.
& $Python -m pip install --upgrade pip | Out-Null
& $Python -m pip install -r (Join-Path $serverDir "requirements.txt") | Out-Null
& $Python -m pip install pyinstaller | Out-Null

# Build a single-file executable.
# NOTE: On Windows, --add-data uses a semicolon (;) separator.
& $Python -m PyInstaller `
  --onefile `
  --name logos-lang-server `
  --distpath $distDir `
  --workpath $workDir `
  --specpath $workDir `
  --clean `
  --add-data (Join-Path $serverDir "logos.lark")+";." `
  (Join-Path $serverDir "lsp_server.py")

Write-Host "Done. Output: $(Join-Path $distDir "logos-lang-server.exe")"
