# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

Logos is an esoteric, liturgy-themed programming language (`.lg` files) implemented in Python 3.12+ on top of Lark, plus a VS Code extension with a TypeScript language server.

## Commands

Python tooling is managed with `uv` (dev deps, including `pygls` for the LSP tests, live in the `dev` dependency group).

```bash
uv sync --group dev                        # full dev environment
uv run pytest -q                           # full suite
uv run pytest tests/canon_runner.py::CanonTests::test_variable_shadowing   # single test
uv run pytest tests/test_security.py -k symlink                            # filter by name
uv run ruff check .                        # lint (rules E4,E7,E9,F,I; line length 100)
uv run mypy                                # strict mypy: logos_lang/, logos.py, legacy lsp_server.py
uv run coverage run -m pytest && uv run coverage report -m   # .coveragerc enforces fail_under = 90
uv run mutmut run && uv run mutmut results # mutation testing over logos_lang/

uv run python logos.py examples/smoke_test.lg   # smoke test — required gate when runtime or lib/ changes
uv run python logos.py                          # REPL
uv run python logos.py prog.lg --execution-engine vm-strict   # fail instead of falling back to the visitor
uv run python logos.py prog.lg --emit-bytecode out.json       # dump lowered bytecode
```

VS Code extension (`packages/logos-vscode`): `npm ci`, `npm run compile` (tsc → `dist/`), `npm run test:unit` (plain-Node mocha over `src/analysis.ts`, no VS Code needed), `npm run test:extension-host`. F5 in VS Code launches the extension dev host.

Tests are `unittest.TestCase` classes collected by pytest. Opt-in env flags: `LOGOS_ENABLE_DESTRUCTIVE_FFI_TESTS=1` (segfault isolation probe). Pass env overrides to fixtures via `_execute_fixture(env=...)` (it uses `mock.patch.dict`); never write `os.environ` directly in tests.

## Architecture

**Execution pipeline.** `logos.py` (CLI/REPL, builds a `SecurityContext` from flags) → `create_parser()` (`logos_lang/grammar.py`; always use it — it enables `propagate_positions`, which runtime error locations depend on) → `LogosInterpreter.visit(start_tree)` (`logos_lang/interpreter.py`). After the top-level program runs, a user-defined `main` mystery is invoked automatically if one exists. `logos.py` owns the CLI parser, REPL, flag → `SecurityContext` mapping and WASI dispatch; all language logic lives in `logos_lang/`, which tests import directly (tests replicate the run-then-`main` sequence themselves, see `tests/canon_runner.py`).

**WASI target.** `--emit-bytecode` / `--execution-target wasi` serialize the compiled `BytecodeProgram` to JSON and `WasiExecutionBridge` (`logos_lang/wasi.py`) hands it to an external `wasmtime` + runtime module (`--wasi-module` or `LOGOS_WASI_MODULE`, binary via `LOGOS_WASMTIME_BIN`). No WASM runtime ships in this repo; changes to opcodes or `BytecodeProgram.to_dict` change that artifact format.

**Two execution engines, one semantics.** `LogosInterpreter` is a Lark `Interpreter` whose methods are named after grammar rules (`inscribe`, `amend`, `chant`, `vigil`, `mystery_def`, …). Before that visitor runs, `_execute_start_tree` tries to lower the whole program with `BytecodeCompiler` (`logos_lang/bytecode.py`) and run it on the stack-based `BytecodeVM`. Any construct the compiler hasn't lowered raises `BytecodeUnsupported`; in the default `vm-hybrid` engine that silently falls back to the AST visitor, in `vm`/`vm-strict` it becomes a `LogosError`. The VM owns only control flow and the operand stack: operators (`_eval_binary_op`), equality (`TypeCanon.values_equal`), casts, calls (`_call_by_name`, which also handles module functions), output formatting and block scopes (`_push_block_scope`/`_pop_block_scope`) are interpreter methods it delegates to — put new semantics there, not in an opcode handler. Only a subset is lowered (`proclaim`, `inscribe`, direct-variable `amend`, blocks, `discern`, `chant`, expressions without attribute/index access), so most real programs still run on the visitor; lowering a new construct means adding compiler + opcode support. Test under both engines (`"visitor"` vs `"vm-strict"`, or `"vm-hybrid"` when the program uses unlowered constructs) — the dogma suites loop over `ENGINES`.

**Error boundary.** Everything surfaced to Logos code must be a `LogosError` (or its subclass `SecurityError`) from `logos_lang/exceptions.py`. Top-level `visit` wraps any leaked host exception into `LogosError("Anathema: Unhandled host exception…")`; the fuzz suite (`tests/fuzz/test_fuzz_parser.py`, Hypothesis) asserts no native exception escapes. `vigil`/`confess` (visitor only; the bytecode compiler does not lower it) catches any `Exception` except `SecurityError`, which is terminal, and binds `str(e)` to the confess variable. `depart`/`__sys_exit` raise `LogosExit` (a `BaseException`), which halts the interpreter without killing the host and is never caught by `vigil`; the CLI maps it to the exit code. `LogosError` carries `line`/`column`/`source_file`, filled by `visit` (innermost node wins) and by the VM from per-instruction positions; the CLI prints `file:line:col: message`. `ReturnValue`/`TailCall` (`models.py`) are plain dataclasses that are *returned* up through `block`/visit, not raised, so `offer` inside a vigil is unaffected by the `except`.

**Functions, TCO, recursion.** `_invoke_user_function` trampolines `TailCall` objects (bounded by `LOGOS_MAX_TCO`); non-tail recursion is capped by `LOGOS_MAX_RECURSION` (default 1000) and reports "Pride".

**Types.** Optional annotations (`HolyInt`, `HolyFloat`, `Text`, `Bool`, `Procession`, icon names) are enforced at runtime via `TypeCanon` (`types.py`). `StaticTypeAnalyzer` (`static_analysis.py`) is a conservative pre-pass that elides provably redundant *global* type checks; it can also ingest trusted facts from the LSP (`--lsp-type-elision-file`). If you change typing rules, keep the analyzer conservative — an unsound elision is a type-safety hole.

**Stdlib = two layers.** `logos_lang/stdlib.py` registers Python builtins into the global scope (`__sys_open`, `__sys_time`, `measure`, `passage`, `append`, …). The Logos-level libraries in `lib/*.lg` (`genesis`, `numeri`, `psalms`, `canon`) are thin wrappers over those builtins and are imported with `tradition`. Constitution rule: every `lib/` mystery must map to a real runtime builtin. `CANON_API_REFERENCE.md` documents the contracts — update it with any stdlib change.

**Modules (`tradition`).** `ModuleManager` (`modules.py`) loads each imported file in a child `LogosInterpreter` that inherits the parent's security context, IO handler, engine and type-elision settings; modules are cached by realpath; a cyclic importer receives the same `Module` object that is filled in place once loading finishes. Calling a module function syncs alias-written values into the module's globals before the call and publishes its globals back to `exports` after. Imports must resolve inside the program root (`base_path`), the bundled `lib/` (`BUNDLED_LIB_DIR`), or `SecurityContext.import_roots` (`--import-root`); anything else raises `SecurityError`.

**Security posture.** `SecurityContext` (`models.py`) is strict by default: FFI (`apocrypha`, `ffi.py`, ctypes backend) is denied unless `--unsafe-ffi`/`--allow-lib`; pointer-like types need `--allow-unsafe-pointers`; inferred signatures need `--allow-inferred-ffi-signatures`; `--require-os-sandbox-for-ffi` gates on an env-var attestation. File I/O in `stdlib.py` is realpath-contained to `base_path`, refuses writes to executable/source suffixes, caps open scrolls at 64, and is released by `LogosInterpreter.close()` (context manager; the CLI calls it). Underscore attribute reads and writes are blocked, and only Logos aggregates (dicts) are mutable via `amend obj.attr`. Icons are closed records on both construction and mutation.

**Language servers — two implementations.** `packages/logos-vscode/src/server.ts` is the primary TypeScript LSP — connection wiring only; the line/regex-based analysis (diagnostics, semantic tokens, inlay hints, `//` and `#` comments) is in `src/analysis.ts`; `packages/logos-vscode/server/lsp_server.py` is the legacy pygls server, which imports `logos_lang` and is what `tests/test_lsp.py` / `tests/test_lsp_jsonrpc.py` exercise. Grammar/keyword changes also need `syntaxes/logos.tmLanguage.json` and both servers updated.

**Reference docs.** `FORMAL_LANGUAGE_SPEC.md` (grammar, typing, execution model), `CANON_API_REFERENCE.md` (stdlib), `PILGRIMS_PATH.md` (idioms), `TESTING_ARCHITECTURE.md` (which suite covers which domain). Keep the spec in sync with grammar/semantic changes.

## Project rules (from `.specify/memory/constitution.md`)

- Brownfield: preserve observable behavior; minimal, scoped diffs; keep bug fixes separate from refactors.
- Every bug fix adds or updates a regression test. Security-sensitive changes (FFI, file I/O, imports, attribute access) need a failing-before/passing-after test — security fixtures live in `tests/fixtures/security/` and `.lg` fixtures generally in `tests/fixtures/`.
- Done means: targeted tests + full suite green, plus the smoke test when runtime or `lib/` is touched; CLI and VS Code/LSP tooling must still work.
- Non-trivial features follow the spec-kit flow (`.specify/` templates and scripts; prompts in `.github/prompts/speckit.*`): constitution → specify → plan → tasks → implement.
- Error messages should be actionable and point at the real failing surface; new failure modes should assert on message text where reasonable.

## Tooling notes

- `ruff check .` and `mypy` are expected to be clean; keep them that way.
- `mypy --strict` is the authoritative type checker. The pyright LSP (`[tool.pyright]` in `pyproject.toml`) is there for navigation; its diagnostics differ from mypy's (notably on ctypes), so don't "fix" pyright-only complaints.
- `.claude/hooks/ruff_check.py` runs after every Python edit and reports only ruff violations that are new relative to the file's `HEAD` version, so pre-existing lint never needs to be touched in unrelated changes.
- The `logos-testing` project skill covers Hypothesis-based differential testing (visitor vs bytecode VM, elision on vs off).
