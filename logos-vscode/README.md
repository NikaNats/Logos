# Logos (Orthodox)

Liturgical programming language support for Logos (`.lg`) in Visual Studio Code.

## Install and test (Debug Mode)

1. Open the `logos-vscode` folder in VS Code.
2. Press `F5` to launch an **Extension Development Host** window.
3. In the new window, create a file named `test.lg`.
4. Paste your Logos code.

You should see highlighting for:

- `mystery` (storage/type)
- `proclaim` (keyword)
- `Verily` / `Nay` (constants)
- Strings in `"..."`
- `//` line comments

## Packaging (Distribution)

### Option A: Bundled Binary Language Server (Recommended)

By default the extension can run a Python LSP server, but that requires end users to have a working Python environment with dependencies installed.

The professional distribution approach is to ship a bundled executable built with PyInstaller:

1. Build the Windows server binary:

```powershell
cd logos-vscode\server
./build_server_win.ps1
```

This produces:

- `logos-vscode/server/bin/win32/logos-lang-server.exe`

2. Package the extension:

```bash
cd logos-vscode
npx --yes @vscode/vsce package --allow-missing-repository
```

The VSIX will include the bundled server binary, and end users will not need Python.

### Classic Packaging

```bash
npm install -g vsce
cd logos-vscode
vsce package
```

This produces `logos-lang-1.0.0.vsix`.

## Install from VSIX

- In VS Code: Extensions view → `...` → **Install from VSIX...** → select the generated `.vsix`.
