# Mutation Testing Baseline

This folder documents the mutation-testing workflow for Logos runtime semantics.

## Purpose

Line coverage alone is insufficient for language-runtime correctness. Mutation testing
injects controlled semantic faults and verifies that tests fail as expected.

## Local Workflow

Run from repository root:

```bash
uv sync --group dev
uv run mutmut run
uv run mutmut results
```

## Interpretation

- Killed mutant: test suite correctly detected injected bug.
- Survived mutant: semantic area likely under-tested and needs stronger assertions.

## High-Value Targets

- `logos_lang/types.py`: operator/type compatibility logic.
- `logos_lang/interpreter.py`: declaration/amend/type-enforcement control flow.
- `logos_lang/ffi.py`: policy and sandbox gates.
