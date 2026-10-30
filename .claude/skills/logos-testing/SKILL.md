---
name: logos-testing
description: Write or extend tests for the Logos runtime — regression tests with .lg fixtures, engine-parity tests, and Hypothesis property/differential tests (visitor vs bytecode VM, static type elision on vs off, grammar-aware program generators). Use when adding tests for interpreter, bytecode, static_analysis, stdlib, modules or security changes, or when a Hypothesis counterexample needs triage.
---

# Testing the Logos runtime

## House style (match it)

- `unittest.TestCase` classes, collected by pytest. No `conftest.py`, no pytest fixtures, no new test dependencies — Hypothesis, psutil and pytest are already in the `dev` group.
- Parse with `Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")`; construct `logos_lang.LogosInterpreter(...)` directly; capture output with `contextlib.redirect_stdout(io.StringIO())` (default `ConsoleIO` prints).
- Program-level regressions go in `tests/fixtures/*.lg` (security cases in `tests/fixtures/security/`) and run through `_execute_fixture` in `tests/canon_runner.py`, which also invokes `main` like the CLI does.
- Assert errors as `logos_lang.LogosError` / `SecurityError`, and assert on message text when the failure mode is new.
- Run: `uv run pytest -q tests/<file>.py::<Class>::<test>`; full suite `uv run --extra lsp pytest -q`.

## Engine parity is the main correctness risk

The default engine (`vm-hybrid`) runs `BytecodeCompiler` + `BytecodeVM` and silently falls back to the AST visitor for unlowered constructs. A behavior fix applied to only one engine passes most tests. For any semantic change, test both explicitly:

```python
for engine in ("visitor", "vm-strict"):
    with self.subTest(engine=engine):
        interp = logos_lang.LogosInterpreter(execution_engine=engine)
        ...
```

`vm-strict` raises `LogosError` on unlowered constructs (e.g. `vigil`, `mystery_def`); check with `logos_lang.BytecodeCompiler().compile(tree)` — it raises `BytecodeUnsupported` — before asserting VM behavior.

## Differential properties (strongest oracles here)

Reuse the generators in `tests/fuzz/test_fuzz_parser.py` (`_expr_strategy`, `_statement_strategy`, `_program_strategy`); extend them there rather than forking.

1. **Visitor == VM.** For any program that parses and compiles to bytecode, `(stdout, error type)` under `execution_engine="visitor"` equals that under `"vm-strict"`. Skip (`hypothesis.assume`) programs that fail to parse or raise `BytecodeUnsupported`.
2. **Elision is unobservable.** `enable_static_type_elision=True` and `False` give identical `(stdout, error type)`. An elision that changes behavior is a type-safety hole in `StaticTypeAnalyzer` — keep it conservative.
3. **No host exception leaks.** Any parsed program either completes or raises `LogosError`/`SecurityError` (existing `FuzzTests`).
4. **Bytecode artifact round-trip.** `BytecodeProgram.to_dict()` is JSON-serializable and stable for the same tree (it's the WASI artifact format).

Compare error *types* (or categories), not full messages, across engines unless message parity is the point of the test.

Use `@settings(deadline=None, suppress_health_check=[HealthCheck.too_slow])` like the existing fuzz test; a fresh interpreter per example (state leaks across examples otherwise).

## Triage a shrunk counterexample

1. Re-run the minimal program by hand under both engines / both elision settings to confirm it's real.
2. Decide which side is wrong using `FORMAL_LANGUAGE_SPEC.md`, not whichever engine is "older".
3. If the generator produced something outside the language (invalid but parseable), tighten the generator; otherwise pin the shrunk program as a fixture or `@hypothesis.example` regression and fix the runtime (in both engines if needed).
