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

```bash
npm install -g vsce
cd logos-vscode
vsce package
```

This produces `logos-lang-1.0.0.vsix`.

## Install from VSIX

- In VS Code: Extensions view → `...` → **Install from VSIX...** → select the generated `.vsix`.
