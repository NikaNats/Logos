# Pilgrim's Path: User Guides and Idioms

This guide is about writing Logos in an idiomatic and safe way.

- API surface reference: see [CANON_API_REFERENCE.md](CANON_API_REFERENCE.md)
- Language semantics: see [FORMAL_LANGUAGE_SPEC.md](FORMAL_LANGUAGE_SPEC.md)

## 1. Control Flow and Liturgical Idioms

### 1.1 Writing safe chants (`chant`)

`chant` is a while loop:

```logos
chant condition {
    # work
} amen
```

A chant can run forever if `condition` never becomes false. Logos does not currently provide a `break` keyword, so idiomatic loops use explicit state mutation and loop budgets.

#### Idiom: budgeted chant

```logos
inscribe attempts: HolyInt = 0;
inscribe max_attempts: HolyInt = 1000;
inscribe done: Bool = Nay;

chant (done is Nay) {
    # work unit here

    amend attempts = attempts + 1;

    discern (attempts >= max_attempts) {
        proclaim "Loop budget reached";
        amend done = Verily;
    } otherwise {
        silence;
    } amen
} amen
```

Why this is safe:

- The loop has a deterministic shutdown path.
- The guard and budget are explicit and reviewable.
- If the inner logic regresses, the budget still prevents infinite execution.

#### Idiom: progress-based chant

Use a monotonic variable that must move toward termination each iteration.

```logos
inscribe i: HolyInt = 0;
inscribe n: HolyInt = 10;

chant (i < n) {
    proclaim i;
    amend i = i + 1;
} amen
```

### 1.2 When to use `discern` vs `contemplate`

Use `discern` for boolean decision logic.

```logos
discern ((x > 0) is Verily) {
    proclaim "positive";
} otherwise {
    proclaim "non-positive";
} amen
```

Use `contemplate` when one subject is matched against many patterns.

```logos
contemplate (command) {
    aspect "start": proclaim "starting";
    aspect "stop": proclaim "stopping";
    aspect _: proclaim "unknown command";
} amen
```

Practical rule:

- Prefer `discern` for one-or-two branch boolean flow.
- Prefer `contemplate` when branching on a single value with many cases.
- Put `aspect _` last as a default catch-all.

### 1.3 Using `vigil` and `confess` safely

`vigil` catches runtime faults and binds the message text to the variable named after `confess`.

```logos
vigil {
    proclaim 1 / 0;
} confess err {
    proclaim "Recovered:";
    proclaim err;
} amen
```

Idioms for robust fault handling:

- Keep the `vigil` block narrow: wrap only fault-prone operations.
- In `confess`, convert failure into a safe fallback value/state.
- Do not silently swallow faults in core business logic; log or proclaim an explicit recovery path.

Example with explicit fallback:

```logos
inscribe result: HolyInt = 0;

vigil {
    amend result = risky_division(10, 0);
} confess err {
    proclaim "Division failed, using fallback";
    amend result = -1;
} amen

proclaim result;
```

Important note: some system APIs signal failure by value (for example file open may return `0`) instead of raising exceptions. For those APIs, combine value checks with `vigil`:

```logos
inscribe fd = open_scroll("missing.txt", 0);
discern (fd is 0) {
    proclaim "open failed";
} otherwise {
    # continue with read/write
    silence;
} amen
```

## 2. The Apocrypha Guide (Safe FFI)

Apocrypha is powerful and dangerous. Treat it as a privileged boundary.

### 2.1 Security defaults and CLI controls

Default behavior is strict:

- FFI disabled unless explicitly allowed.
- Pointer-like types blocked unless explicitly allowed.
- Inferred signatures disabled unless explicitly allowed.

Relevant CLI flags in `logos.py`:

- `--unsafe-ffi`: enables permissive FFI baseline policy.
- `--allow-unsafe-pointers`: allows pointer-like FFI types such as `Text`/`String`.
- `--allow-inferred-ffi-signatures`: allows runtime arg-type inference when declaration omits params.
- `--ffi-backend {ctypes|rust|wasm}`: backend policy gate. Raw Apocrypha bindings require `ctypes` policy.
- `--require-os-sandbox-for-ffi` with `--sandbox-attestation-env`: requires sandbox attestation before loading any foreign library.

Note on naming: this guide uses the CLI spelling (`--allow-unsafe-pointers`). Some prose may refer to the internal setting as `allow_unsafe_pointers`.

### 2.2 Type mapping between Logos and C (`ctypes`)

Current runtime mappings (`FFIManager.get_ctype`):

- `HolyFloat`, `Float`, `Double` -> `ctypes.c_double`
- `HolyInt`, `Int` -> `ctypes.c_longlong`
- `Bool`, `Verily`, `Nay` -> `ctypes.c_bool`
- `Text`, `String` -> `ctypes.c_char_p` (raw pointer boundary)
- Unknown type names -> `ctypes.c_double` fallback

Argument marshalling behavior:

- `Text`/`String` args are UTF-8 encoded to bytes for `c_char_p`.
- Numeric args are converted with Python `float(...)` / `int(...)`.

### 2.3 Prefer explicit signatures over inference

Good:

```logos
apocrypha "msvcrt" mystery puts(s: Text) -> HolyInt;
```

Risky/less safe (inferred arg types at call time):

```logos
apocrypha "msvcrt" mystery puts() -> HolyInt;
# calling puts("hi") now depends on inferred signatures policy
```

Inference is blocked unless `--allow-inferred-ffi-signatures` is set.

### 2.4 Why external DLL bindings are dangerous

Binding directly to external DLLs (for example `msvcrt`) can break memory safety if contracts are wrong.

Common failure modes:

- Ownership mismatch: function returns memory that must be freed by matching allocator.
- ABI mismatch: wrong parameter or return type corrupts stack/register state.
- Pointer lifetime bugs: using stale `char*` or invalid buffers.
- Variadic functions: hard to call safely without exact ABI handling.

Logos already blocks many dangerous symbols (for example process-spawn/load-library families), but this is not a complete safety proof.

### 2.5 Recommended safe FFI posture

- Use explicit Apocrypha signatures.
- Restrict to pure/stateless numeric functions when possible (`cos`, `sqrt`, `abs`).
- Avoid pointer-heavy APIs unless unavoidable.
- Enable `--allow-unsafe-pointers` only when required.
- Prefer memory-safe bridges (`--ffi-backend rust` or `--ffi-backend wasm` policy) for production hardening.
- Run untrusted scripts under OS sandboxing and require attestation for FFI.

Example hardened launch:

```bash
python logos.py programs/main.lg \
  --unsafe-ffi \
  --ffi-backend ctypes \
  --require-os-sandbox-for-ffi \
  --sandbox-attestation-env LOGOS_OS_SANDBOX
```

## 3. Project Structure with `tradition`

### 3.1 Import path resolution model

`tradition "..."` is resolved relative to the importing file, not global process CWD.

This means imports remain stable when launching from different directories.

### 3.2 Direct import vs alias import

Direct import:

```logos
tradition "math.lg";
```

- Exports are merged into current scope.
- Name collisions can overwrite existing names.

Alias import:

```logos
tradition "math.lg" as Math;
proclaim Math.value;
```

- Exports are namespaced under alias.
- Better for large programs and collision prevention.

Recommended default for multi-file projects: alias imports.

### 3.3 Suggested layout for larger projects

```text
programs/
  main.lg
  domain/
    billing.lg
    users.lg
  infra/
    io.lg
    ffi_math.lg
lib/
  canon.lg
  genesis.lg
  numeri.lg
  psalms.lg
```

In `main.lg`, prefer explicit aliases:

```logos
tradition "domain/billing.lg" as Billing;
tradition "domain/users.lg" as Users;
tradition "infra/io.lg" as IO;
```

### 3.4 How ModuleManager prevents cyclic import loops

`ModuleManager` uses two internal sets keyed by absolute path:

- `_modules`: cache of fully loaded modules.
- `_loading`: modules currently being loaded.

Behavior:

1. If path is already in `_modules`, cached module is returned immediately.
2. If path is in `_loading`, a partial empty module is returned to break recursion.
3. Otherwise the module is parsed/evaluated, exports are captured, and result is cached.

Why this matters:

- Prevents infinite recursion from A -> B -> A cycles.
- Prevents repeated work by reusing cached module objects.

Cycle caveat:

- During a cycle, back-edge imports may see partial exports until the first load completes.
- Avoid top-level cross-module initialization that depends on symbols from a module that also imports you.
- Prefer computing dependent values inside `mystery main()` or dedicated init mysteries after imports settle.

### 3.5 Practical import hygiene checklist

- Keep top-level code in traditions minimal (declarations and mystery defs).
- Put side effects in explicit mysteries called from `main()`.
- Use alias imports by default.
- Avoid relying on overwrite order from direct imports.
- Keep filenames stable and paths explicit.

---

If you are new to Logos, start with:

1. `examples/smoke_test.lg`
2. `examples/ffi_typed_test.lg`
3. `programs/main.lg`

Then apply the idioms in this guide as your baseline style.
