# Implementation Plan: [FEATURE]

**Branch**: `[###-feature-name]` | **Date**: [DATE] | **Spec**: [link]
**Input**: Feature specification from `/specs/[###-feature-name]/spec.md`

**Note**: This template is filled in by the `/speckit.plan` command. See `.specify/templates/plan-template.md` for the execution workflow.

## Summary

[Extract from feature spec: primary requirement + technical approach from research]

## Technical Context

Use these project defaults and override only when the feature requires it.

**Language/Version**: Python 3.12 host runtime + Logos DSL grammar (Lark)  
**Primary Dependencies**: lark, ctypes, pygls (LSP), pytest  
**Storage**: Repository files (lib/, programs/, examples/, tests/fixtures/); no DB by default  
**Testing**: pytest (unit + integration + security + stress/fuzz subsets)  
**Target Platform**: Windows/Linux/macOS runtime + VS Code extension host  
**Project Type**: Language runtime + canonical stdlib + editor tooling  
**Performance Goals**: Preserve current recursion/TCO behavior and test runtime envelope  
**Constraints**: Security-first FFI defaults, minimal diffs, backward compatibility for canonical libraries  
**Scale/Scope**: Single repository with Python runtime core and TypeScript/Python VS Code package

## Constitution Check

*GATE: Must pass before Phase 0 research. Re-check after Phase 1 design.*

- [ ] Security-first runtime controls remain deny-by-default where required.
- [ ] Behavior changes are explicit and justified (no accidental regressions).
- [ ] Regression tests are specified for touched critical paths.
- [ ] Canonical libraries and documentation examples remain runnable.
- [ ] Validation commands are defined (targeted tests + full suite + smoke test when applicable).

## Project Structure

### Documentation (this feature)

```text
specs/[###-feature]/
├── plan.md              # This file (/speckit.plan command output)
├── research.md          # Phase 0 output (/speckit.plan command)
├── data-model.md        # Phase 1 output (/speckit.plan command)
├── quickstart.md        # Phase 1 output (/speckit.plan command)
├── contracts/           # Phase 1 output (/speckit.plan command)
└── tasks.md             # Phase 2 output (/speckit.tasks command - NOT created by /speckit.plan)
```

### Source Code (repository root)

```text
logos.py
logos_lang/
lib/
examples/
programs/
tests/
packages/
└── logos-vscode/
    ├── src/
    └── server/
```

**Structure Decision**: Use the existing monorepo layout. Keep runtime changes
in logos_lang/, canonical library changes in lib/, and tooling changes under
packages/logos-vscode/.

## Complexity Tracking

> **Fill ONLY if Constitution Check has violations that must be justified**

| Violation | Why Needed | Simpler Alternative Rejected Because |
|-----------|------------|-------------------------------------|
| [e.g., 4th project] | [current need] | [why 3 projects insufficient] |
| [e.g., Repository pattern] | [specific problem] | [why direct DB access insufficient] |
