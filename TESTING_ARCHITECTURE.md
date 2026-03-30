# Logos Testing Architecture (Advanced)

This document maps production-hardening test domains to concrete suites in this repository.

## 1) Formal Language Conformance (Spectest-style)

- File: `tests/test_conformance_spectest.py`
- Coverage:
  - Operator precedence and associativity validated via `ScopeManager` state assertions.
  - Function frame push/pop and shadowing rules validated via final scope + empty frame stack.
  - Type coercion matrix over `TypeCanon.resolve_binary_op` for numeric/text/bool combinations.
  - Runtime invalid-coercion path asserted to emit `LogosError`.

## 2) AST-Aware Property-Based Testing

- File: `tests/fuzz/test_fuzz_parser.py`
- Coverage:
  - Grammar-aware recursive generation for syntactically valid, semantically chaotic programs.
  - Interpreter invariant: valid generated programs may fail with `LogosError`/`SecurityError`, but must not leak unhandled native exceptions.

## 3) Out-of-Process FFI Resilience

- File: `tests/test_ffi_resilience.py`
- Coverage:
  - Subprocess isolation harness for foreign binding failures.
  - Optional destructive segfault probe (`LOGOS_ENABLE_DESTRUCTIVE_FFI_TESTS=1`) to verify crash isolation.
  - Memory growth probe for repeated ctypes calls (Windows + `psutil`).

## 4) End-to-End LSP Verification

- Files:
  - `tests/test_lsp.py` (semantic engine checks)
  - `tests/test_lsp_jsonrpc.py` (real JSON-RPC over stdio)
- Coverage:
  - `initialize`/`didOpen`/`didChange` lifecycle with `textDocument/publishDiagnostics` assertions.
  - pygls API compatibility for workspace/document and diagnostics publication in
    `packages/logos-vscode/server/lsp_server.py`.
- Extension host:
  - `packages/logos-vscode/src/test/**` with `@vscode/test-electron` harness.
  - Run with `npm run test:extension-host` in `packages/logos-vscode`.

## 5) Advanced Sandbox Penetration

- File: `tests/test_security.py`
- Coverage:
  - Existing reflection/private-attribute and traversal fixtures.
  - Symlink escape scenario against `__sys_open` realpath enforcement.
  - Poisoned host builtins environment check to ensure no runtime escape via interpreter namespace.

## 6) Mutation Testing

- Config: `[tool.mutmut]` in `pyproject.toml`
- Guide: `tests/mutation/README.md`
- Run:

```bash
uv sync --group dev
uv run mutmut run
uv run mutmut results
```

## Runtime Invariant Guard

- File: `logos_lang/interpreter.py`
- Top-level `visit(start)` now traps unexpected host exceptions and re-raises as `LogosError`,
  preserving language-level error boundaries for adversarial workloads.
