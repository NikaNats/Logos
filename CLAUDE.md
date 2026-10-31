# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

Logos is an esoteric, liturgy-themed programming language (`.lg` files) implemented in Python 3.12+ on top of Lark, plus a VS Code extension with a TypeScript language server.

## Commands

Python tooling is managed with `uv` (dev deps live in the `dev` dependency group; `pygls` is the optional `lsp` extra).

```bash
uv sync --group dev --extra lsp            # full dev environment
uv run --extra lsp pytest -q               # full suite (without --extra lsp, tests/test_lsp*.py fail on missing pygls)
uv run pytest tests/canon_runner.py::CanonTests::test_variable_shadowing   # single test
uv run pytest tests/test_security.py -k symlink                            # filter by name
uv run ruff check .                        # lint (rules E4,E7,E9,F,I; line length 100)
uv run mypy                                # strict mypy over logos_lang/ only
uv run coverage run -m pytest && uv run coverage report -m   # .coveragerc enforces fail_under = 90
uv run mutmut run && uv run mutmut results # mutation testing over logos_lang/

uv run python logos.py examples/smoke_test.lg   # smoke test — required gate when runtime or lib/ changes
uv run python logos.py                          # REPL
uv run python logos.py prog.lg --execution-engine vm-strict   # fail instead of falling back to the visitor
uv run python logos.py prog.lg --emit-bytecode out.json       # dump lowered bytecode
```

VS Code extension (`packages/logos-vscode`): `npm install`, `npm run compile` (tsc → `dist/`), `npm run test:extension-host`. F5 in VS Code launches the extension dev host.

Tests are `unittest.TestCase` classes collected by pytest. Opt-in env flags: `LOGOS_ENABLE_DESTRUCTIVE_FFI_TESTS=1` (segfault isolation probe). The canon tests write `canon_io.tmp` to the current directory; don't commit it.

## Architecture

**Execution pipeline.** `logos.py` (CLI/REPL, builds a `SecurityContext` from flags) → `Lark(LOGOS_GRAMMAR, parser="lalr")` (`logos_lang/grammar.py`) → `LogosInterpreter.visit(start_tree)` (`logos_lang/interpreter.py`). After the top-level program runs, a user-defined `main` mystery is invoked automatically if one exists. `logos.py` owns the CLI parser, REPL, flag → `SecurityContext` mapping and WASI dispatch; all language logic lives in `logos_lang/`, which tests import directly (tests replicate the run-then-`main` sequence themselves, see `tests/canon_runner.py`).

**WASI target.** `--emit-bytecode` / `--execution-target wasi` serialize the compiled `BytecodeProgram` to JSON and `WasiExecutionBridge` (`logos_lang/wasi.py`) hands it to an external `wasmtime` + runtime module (`--wasi-module` or `LOGOS_WASI_MODULE`, binary via `LOGOS_WASMTIME_BIN`). No WASM runtime ships in this repo; changes to opcodes or `BytecodeProgram.to_dict` change that artifact format.

**Two execution engines, one semantics.** `LogosInterpreter` is a Lark `Interpreter` whose methods are named after grammar rules (`inscribe`, `amend`, `chant`, `vigil`, `mystery_def`, …). Before that visitor runs, `_execute_start_tree` tries to lower the whole program with `BytecodeCompiler` (`logos_lang/bytecode.py`) and run it on the stack-based `BytecodeVM`. Any construct the compiler hasn't lowered raises `BytecodeUnsupported`; in the default `vm-hybrid` engine that silently falls back to the AST visitor, in `vm`/`vm-strict` it becomes a `LogosError`. Consequence: **a semantic change usually has to be made in both `interpreter.py` and `bytecode.py`** (the VM calls back into the interpreter for function invocation, type enforcement and casts, but has its own opcode handlers and `_cast_value`). Test under both engines (`execution_engine="visitor"` vs `"vm-strict"`) — `tests/test_vm_and_type_elision.py` shows the pattern.

**Error boundary.** Everything surfaced to Logos code must be a `LogosError` (or its subclass `SecurityError`) from `logos_lang/exceptions.py`. Top-level `visit` wraps any leaked host exception into `LogosError("Anathema: Unhandled host exception…")`; the fuzz suite (`tests/fuzz/test_fuzz_parser.py`, Hypothesis) asserts no native exception escapes. `vigil`/`confess` (visitor only; the bytecode compiler does not lower it) catches any `Exception`, not just `LogosError`, and binds `str(e)` to the confess variable. `ReturnValue`/`TailCall` (`models.py`) are plain dataclasses that are *returned* up through `block`/visit, not raised, so `offer` inside a vigil is unaffected by the `except`.

**Functions, TCO, recursion.** `_invoke_user_function` trampolines `TailCall` objects (bounded by `LOGOS_MAX_TCO`); non-tail recursion is capped by `LOGOS_MAX_RECURSION` (default 1000) and reports "Pride".

**Types.** Optional annotations (`HolyInt`, `HolyFloat`, `Text`, `Bool`, `Procession`, icon names) are enforced at runtime via `TypeCanon` (`types.py`). `StaticTypeAnalyzer` (`static_analysis.py`) is a conservative pre-pass that elides provably redundant *global* type checks; it can also ingest trusted facts from the LSP (`--lsp-type-elision-file`). If you change typing rules, keep the analyzer conservative — an unsound elision is a type-safety hole.

**Stdlib = two layers.** `logos_lang/stdlib.py` registers Python builtins into the global scope (`__sys_open`, `__sys_time`, `measure`, `passage`, `append`, …). The Logos-level libraries in `lib/*.lg` (`genesis`, `numeri`, `psalms`, `canon`) are thin wrappers over those builtins and are imported with `tradition`. Constitution rule: every `lib/` mystery must map to a real runtime builtin. `CANON_API_REFERENCE.md` documents the contracts — update it with any stdlib change.

**Modules (`tradition`).** `ModuleManager` (`modules.py`) loads each imported file in a child `LogosInterpreter` that inherits the parent's security context, IO handler, engine and type-elision settings; modules are cached by realpath, cycles return a partial module. Import paths are realpath-contained to the workspace root (first ancestor with `pyproject.toml`, `README.md` or `.git`) — traversal raises `SecurityError`.

**Security posture.** `SecurityContext` (`models.py`) is strict by default: FFI (`apocrypha`, `ffi.py`, ctypes backend) is denied unless `--unsafe-ffi`/`--allow-lib`; pointer-like types need `--allow-unsafe-pointers`; inferred signatures need `--allow-inferred-ffi-signatures`; `--require-os-sandbox-for-ffi` gates on an env-var attestation. File I/O in `stdlib.py` is realpath-contained to `base_path`. Private/dunder attribute access from Logos is blocked.

**Language servers — two implementations.** `packages/logos-vscode/src/server.ts` is the primary TypeScript LSP (diagnostics, semantic tokens, inlay hints); `packages/logos-vscode/server/lsp_server.py` is the legacy pygls server, which imports `logos_lang` and is what `tests/test_lsp.py` / `tests/test_lsp_jsonrpc.py` exercise. Grammar/keyword changes also need `syntaxes/logos.tmLanguage.json` and both servers updated.

**Reference docs.** `FORMAL_LANGUAGE_SPEC.md` (grammar, typing, execution model), `CANON_API_REFERENCE.md` (stdlib), `PILGRIMS_PATH.md` (idioms), `TESTING_ARCHITECTURE.md` (which suite covers which domain). Keep the spec in sync with grammar/semantic changes.

## Project rules (from `.specify/memory/constitution.md`)

- Brownfield: preserve observable behavior; minimal, scoped diffs; keep bug fixes separate from refactors.
- Every bug fix adds or updates a regression test. Security-sensitive changes (FFI, file I/O, imports, attribute access) need a failing-before/passing-after test — security fixtures live in `tests/fixtures/security/` and `.lg` fixtures generally in `tests/fixtures/`.
- Done means: targeted tests + full suite green, plus the smoke test when runtime or `lib/` is touched; CLI and VS Code/LSP tooling must still work.
- Non-trivial features follow the spec-kit flow (`.specify/` templates and scripts; prompts in `.github/prompts/speckit.*`): constitution → specify → plan → tasks → implement.
- Error messages should be actionable and point at the real failing surface; new failure modes should assert on message text where reasonable.

The constitution's hard-coded `PYTHONPATH` fallback to another checkout (`.../Trinity/.venv`) is stale — use `uv run`.

## Tooling notes

- `ruff check .` and `mypy` are not clean on `main`. Before claiming a change introduced or fixed lint/type errors, compare against the baseline (`git stash; uv run mypy; git stash pop`) rather than assuming zero.
- `mypy --strict` is the authoritative type checker. The pyright LSP (`[tool.pyright]` in `pyproject.toml`) is there for navigation; its diagnostics differ from mypy's (notably on ctypes), so don't "fix" pyright-only complaints.
- `.claude/hooks/ruff_check.py` runs after every Python edit and reports only ruff violations that are new relative to the file's `HEAD` version, so pre-existing lint never needs to be touched in unrelated changes.
- The `logos-testing` project skill covers Hypothesis-based differential testing (visitor vs bytecode VM, elision on vs off).
