# Logos Brownfield Constitution

## Core Principles

### I. Security-First Runtime Changes
- FFI access remains deny-by-default unless explicitly enabled.
- Pointer-like FFI behavior must require explicit opt-in and be enforced for
	both declared and inferred type paths.
- Any security-sensitive runtime change must include negative-path regression
	tests.

### II. Behavior over Refactor
- Brownfield work preserves observable behavior unless behavior change is
	explicitly specified and approved.
- Keep changes minimal and scoped to the feature/problem statement.
- Separate refactors from bug fixes when practical.

### III. Test-Backed Delivery (Non-Negotiable)
- Every bug fix must add or update regression tests.
- Critical areas maintain coverage: interpreter, modules, stdlib, FFI, and LSP.
- Work is not complete until required tests pass in the current environment.

### IV. Compatibility of Canon and Tooling
- Canonical libraries under lib must map to real runtime builtins.
- Documentation and examples must stay runnable.
- CLI and VS Code/LSP tooling behavior must remain operational after changes.

### V. Clear Diagnostics and Operability
- Errors should be actionable and identify the failing surface.
- New failure modes should include message-quality assertions when reasonable.
- Validation commands should be deterministic and reproducible.

## Brownfield Constraints

- Python baseline: 3.11+.
- Required validation commands:
	- py -3.13 -m pytest -q
	- py -3.13 logos.py examples/smoke_test.lg
- Fallback when local virtualenv interpreter is unavailable:
	- $env:PYTHONPATH = "c:/Users/Nika/Downloads/Trinity/.venv/Lib/site-packages"
	- py -3.13 -m pytest -q

## Development Workflow and Quality Gates

- Non-trivial feature flow:
	1. /speckit.constitution
	2. /speckit.specify
	3. /speckit.plan
	4. /speckit.tasks
	5. /speckit.implement
- Completion gates:
	- Targeted tests for touched surfaces.
	- Full test suite green.
	- Smoke test green when runtime/core libraries are touched.

## Governance

- This constitution supersedes ad-hoc development preferences for this repo.
- Amendments require rationale, risk assessment, and updated tests/docs for
	behavioral changes.
- Semantic versioning policy:
	- MAJOR: backward-incompatible governance or principle removals/redefinitions.
	- MINOR: new principle/section or materially expanded guidance.
	- PATCH: clarifications and wording improvements without policy changes.
- Pull requests must declare which principles were applied and which gates were
	satisfied.

**Version**: [CONSTITUTION_VERSION] | **Ratified**: [RATIFICATION_DATE] | **Last Amended**: [LAST_AMENDED_DATE]
