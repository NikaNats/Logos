# Logos Brownfield Constitution

## Core Principles

### I. Security-First Runtime Changes
- FFI access remains deny-by-default unless explicitly enabled.
- Pointer-like FFI behavior must require explicit opt-in and be enforced for declared and inferred paths.
- Any change in security-sensitive surfaces must include a failing-before/fixed-after security regression test.

### II. Behavior over Refactor
- Brownfield work prioritizes preserving observable behavior unless behavior change is explicitly specified.
- Keep diffs minimal and scoped to the feature/problem statement.
- Separate bug fixes from broad refactors when practical.

### III. Test-Backed Delivery (Non-Negotiable)
- Every bug fix must add or update regression tests.
- Critical areas must maintain coverage: interpreter, modules, stdlib, FFI, and LSP diagnostics.
- A task is not complete until tests pass in the current environment.

### IV. Compatibility of Canon and Tooling
- Canonical libraries under lib must remain runnable and mapped to real runtime builtins.
- Examples and docs commands must be executable, especially smoke test flows.
- Developer tooling (CLI and VS Code/LSP) must remain operational after changes.

### V. Clear Diagnostics and Operability
- Errors should be actionable and point to the true failing surface.
- New failure modes must include test assertions on message quality when reasonable.
- Prefer deterministic commands and reproducible local validation steps.

## Brownfield Constraints

- Python runtime baseline: Python 3.11+.
- Preferred local validation command set:
  - py -3.13 -m pytest -q
  - py -3.13 logos.py examples/smoke_test.lg
- If local virtualenv interpreter is unavailable, use repository site-packages fallback:
  - $env:PYTHONPATH = "c:/Users/Nika/Downloads/Trinity/.venv/Lib/site-packages"
  - py -3.13 -m pytest -q

## Development Workflow and Quality Gates

- Specification and planning flow for non-trivial changes:
  1. /speckit.constitution
  2. /speckit.specify
  3. /speckit.plan
  4. /speckit.tasks
  5. /speckit.implement
- Required completion gates:
  - Targeted tests for touched surfaces.
  - Full test suite green.
  - Smoke test green when runtime/core libs are touched.

## Governance

- This constitution supersedes ad-hoc development preferences for this repository.
- Amendments require rationale, risk assessment, and updated tests/documentation if behavior changes.
- Versioning policy for this constitution follows semantic versioning:
	- MAJOR: backward-incompatible governance/principle redefinition or removal.
	- MINOR: new principle/section or materially expanded guidance.
	- PATCH: wording clarifications and alignment updates without policy shifts.
- Pull requests must state which principle(s) were applied and how gates were satisfied.

**Version**: 1.0.1 | **Ratified**: 2026-03-30 | **Last Amended**: 2026-03-30
