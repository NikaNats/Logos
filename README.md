# ☩ Logos

[![CI](https://github.com/NikaNats/Logos/actions/workflows/ci.yml/badge.svg)](https://github.com/NikaNats/Logos/actions/workflows/ci.yml)

An esoteric, imperative programming language with Orthodox liturgical syntax: gradual typing enforced at runtime, tail-call optimization, a sandboxed runtime, and VS Code support.

```logos
tradition "std:numeri";

icon Monk { name: Text; prayers: HolyInt; } amen

mystery pray(monk: Monk, times: HolyInt) -> HolyInt {
    inscribe i: HolyInt = 0;
    chant i < times {
        amend monk.prayers = monk.prayers + 1;
        amend i = i + 1;
    } amen
    offer monk.prayers;
} amen

inscribe paisios = write Monk { name = "Paisios", prayers = 0 };
inscribe total: HolyInt = pray(paisios, 3);
proclaim paisios.name + " prayed " + (transfigure total into Text) + " times.";

discern (is_even(total)) {
    proclaim "An even rule.";
} otherwise {
    proclaim "An odd rule.";
} amen

vigil {
    proclaim 1 / 0;
} confess sin {
    proclaim "Recovered: " + sin;
} amen
```

```console
$ logos tour.lg
☩ Paisios prayed 3 times.
☩ An odd rule.
☩ Recovered: Anathema: Division by zero.
```

## Install

Requires Python 3.12+ and [uv](https://docs.astral.sh/uv/).

```bash
uv tool install git+https://github.com/NikaNats/Logos
logos program.lg      # run a program
logos                 # interactive REPL (type `exit` to leave)
```

## The language

| Logos | Meaning |
|---|---|
| `inscribe x: HolyInt = 1;` / `amend x = 2;` | declare / reassign |
| `proclaim expr;` / `supplicate "prompt"` | print / read input |
| `discern (c) { } otherwise { } amen` | if / else |
| `chant c { } amen` | while |
| `contemplate (x) { aspect 1: …; aspect _: …; } amen` | match |
| `mystery f(a: Text) -> Bool { offer …; } amen` | function / return |
| `icon Name { field: Type; } amen`, `write Name { field = … }` | struct type / instance |
| `vigil { } confess err { } amen` | try / catch |
| `transfigure x into Text` | cast |
| `tradition "file.lg";` / `tradition "std:genesis" as g;` | import |
| `is`, `is not`, `Verily`, `Nay` | equality, booleans |

Types: `HolyInt`, `HolyFloat`, `Text`, `Bool`, `Procession` (list), and your icons. Annotations are optional and enforced at runtime. Tail calls (`offer f(…);`) don't grow the stack.

Standard library, imported with `std:`: `genesis` (time, environment, files), `numeri` (math), `psalms` (text), `canon` (legacy typed helpers). See the [API reference](docs/CANON_API_REFERENCE.md).

## Security defaults

Programs are sandboxed by default:
- **File access** stays inside the script's directory, and scripts can't write code files (`.py`, `.lg`, `.dll`, …).
- **Imports** resolve only inside that directory and `std:`; grant more with `--import-root DIR`.
- **Sandbox violations** can't be caught by `vigil`.
- **Native code** (`apocrypha`, via ctypes) is disabled unless you opt in:

```bash
logos program.lg --unsafe-ffi                                # allow whitelisted libc/libm math functions
logos program.lg --unsafe-ffi --require-os-sandbox-for-ffi   # ...only inside an attested OS sandbox
```

`logos --help` lists every option, including the bytecode VM (`--execution-engine vm-strict`) and bytecode/WASI output (`--emit-bytecode`, `--execution-target wasi`).

## Editor support

`packages/logos-vscode` is a VS Code extension with syntax highlighting, diagnostics, semantic tokens and inlay type hints. To try it, run `npm ci && npm run compile` there and press F5 in VS Code.

## Development

```bash
git clone https://github.com/NikaNats/Logos && cd Logos
uv sync --group dev
uv run pytest              # tests
uv run ruff check .        # lint
uv run mypy                # strict type check
uv run logos examples/smoke_test.lg
```

The extension's unit tests run from `packages/logos-vscode` with `npm run test:unit`. CI runs all of the above on Linux and Windows.

Reference: [language specification](docs/FORMAL_LANGUAGE_SPEC.md) · [API reference](docs/CANON_API_REFERENCE.md) · [idioms guide](docs/PILGRIMS_PATH.md) · [testing architecture](docs/TESTING_ARCHITECTURE.md). More programs live in [`examples/`](examples) and [`programs/`](programs).

## License

[MIT](LICENSE) © 2025 NikaNats
