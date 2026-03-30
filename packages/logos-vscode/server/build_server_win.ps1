Param(
  [string]$Uv = "uv"
)

$ErrorActionPreference = "Stop"

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot "..\..\..")
$serverDir = $PSScriptRoot
$distDir = Join-Path $serverDir "bin\win32"
$workDir = Join-Path $serverDir "build\pyinstaller"

Write-Host "Building Logos LSP server (Windows) with PyInstaller..."
Write-Host "Server dir: $serverDir"
Write-Host "Dist dir:   $distDir"

New-Item -ItemType Directory -Force -Path $distDir | Out-Null
New-Item -ItemType Directory -Force -Path $workDir | Out-Null

# Resolve dependencies from pyproject.toml and build with uv's managed env.
Push-Location $repoRoot
try {
  & $Uv sync --extra lsp --extra build | Out-Null

  # Build a single-file executable.
  # NOTE: On Windows, --add-data uses a semicolon (;) separator.
  & $Uv run pyinstaller `
    --onefile `
    --name logos-lang-server `
    --distpath $distDir `
    --workpath $workDir `
    --specpath $workDir `
    --clean `
    --add-data (Join-Path $serverDir "logos.lark")+";." `
    (Join-Path $serverDir "lsp_server.py")
}
finally {
  Pop-Location
}

Write-Host "Done. Output: $(Join-Path $distDir "logos-lang-server.exe")"
