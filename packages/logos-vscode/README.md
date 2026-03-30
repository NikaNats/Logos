# Logos (Orthodox)

Liturgical programming language support for Logos (`.lg`) in Visual Studio Code.

The extension now runs a TypeScript Language Server by default and provides:

- Semantic token highlighting (keywords, declarations, types, built-in calls)
- Type inlay hints for `inscribe` declarations without explicit annotations
- TextMate grammar fallback for base syntax scopes

## Install and test (Debug Mode)

1. Open the `packages/logos-vscode` folder in VS Code.
2. Press `F5` to launch an **Extension Development Host** window.
3. In the new window, create a file named `test.lg`.
4. Paste your Logos code.

You should see highlighting for:

- `mystery` (storage/type)
- `proclaim` (keyword)
- `Verily` / `Nay` (constants)
- Strings in `"..."`
- `//` line comments

You should also see type inlay hints such as `: HolyInt` after declarations like:

```logos
inscribe age = 42;
inscribe is_elder = Verily;
```

## Packaging (Distribution)

### Default Runtime (Recommended)

The extension ships with a TypeScript Language Server compiled into `dist/server.js`.

Build it before packaging:

```bash
cd packages/logos-vscode
npm install
npm run compile
```

Then create the VSIX:

```bash
npx --yes @vscode/vsce package --allow-missing-repository
```

### Legacy Optional Runtime: Bundled Python Binary

If you want a native executable fallback built from the legacy Python server, build it with PyInstaller:

1. Build the Windows server binary:

```powershell
cd packages\logos-vscode\server
./build_server_win.ps1
```

This produces:

- `packages/logos-vscode/server/bin/win32/logos-lang-server.exe`

Then package the extension:

```bash
cd packages/logos-vscode
npx --yes @vscode/vsce package --allow-missing-repository
```

At runtime, the extension resolves servers in this order:

1. TypeScript server (`dist/server.js`)
2. Bundled native binary (`server/bin/...`)
3. Python server (`server/lsp_server.py`)

### Classic Packaging

```bash
npm install -g vsce
cd packages/logos-vscode
vsce package
```

This produces `logos-lang-1.0.0.vsix`.

## Install from VSIX

- In VS Code: Extensions view → `...` → **Install from VSIX...** → select the generated `.vsix`.
