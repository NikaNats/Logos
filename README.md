# ☩ Logos

## The Liturgical Programming Language

> *"In the beginning was the Word, and the Word was with God, and the Word was God."* — John 1:1

**Logos** is an esoteric, imperative programming language whose syntax draws inspiration from Orthodox Christian liturgy and theological concepts. Beneath its uniquely themed surface, Logos functions as a robust, interpreted language built on Python and leveraging the `Lark` parsing library. It features advanced capabilities such as **Tail Call Optimization (TCO)** for efficient recursion, a **Foreign Function Interface (FFI)** powered by `ctypes`, comprehensive **Runtime Type Enforcement**, and a dedicated **Language Server Protocol (LSP)** implementation for enhanced developer experience.

---

## 🔥 Quickstart: Embarking on the Pilgrimage

To begin your journey with Logos, ensure you have **Python 3.12+** installed.

1.  **Clone the Repository:**
    ```bash
    git clone https://github.com/nikanats/nikanats-logos.git
    cd nikanats-logos
    ```

2.  **Set Up Virtual Environment:**
    It is best practice to work within a virtual environment to manage dependencies.
    ```bash
    python -m venv .venv
    # Activate on Linux/macOS:
    source ./.venv/bin/activate
    # Activate on Windows (Cmd/Git Bash):
    ./.venv/Scripts/activate
    # Activate on Windows (PowerShell):
    ./.venv/Scripts/Activate.ps1
    ```

3.  **Install Core Dependencies:**
    Dependencies are managed via `pyproject.toml`.
    ```bash
    uv sync --group dev
    ```

4.  **Run a Sample Liturgy:**
    Execute the `smoke_test.lg` example to confirm everything is working:
    ```bash
    uv run logos examples/smoke_test.lg
    ```
    This script performs basic system checks, including time, math, and file I/O operations, proclaiming the results to your console.

    To use `logos` outside this checkout, install it as a tool: `uv tool install .` (or `pipx install .`).

5.  **Interactive Confessional (REPL):**
    For immediate exploration, run Logos in interactive mode:
    ```bash
    uv run logos
    ```
    Type `silence;` to execute a statement and `exit` or `depart(0);` to leave.

6.  **VM / WASI (Optional):**
    ```bash
    # Force strict bytecode VM execution (no visitor fallback)
    uv run logos programs/main.lg --execution-engine vm-strict

    # Emit portable bytecode artifact
    uv run logos programs/main.lg --emit-bytecode .logos/main.bytecode.json

    # Dispatch bytecode into an external WASI runtime module
    uv run logos programs/main.lg --execution-target wasi --wasi-module ./runtime/logos_vm_wasi.wasm
    ```

---

## 📜 The Canon: Core Capabilities and Dogmas

Logos is designed with specific "canonical" principles, offering a unique set of programming capabilities:

*   **Liturgical Syntax**: Core language constructs are re-imagined with theological terms:
    *   `mystery`: Function definition
    *   `vigil` / `confess`: Exception handling (try/catch)
    *   `icon`: Data structure (struct/object) definition
    *   `proclaim`: Output to console (print)
    *   `offer`: Return value
*   **The Apocrypha (FFI)**: Bind foreign symbols via `apocrypha` with strict policy controls. Raw `ctypes` is treated as a legacy backend; memory-safe Rust/WASM bridges are the recommended deployment path for hardened environments.
*   **Runtime Type Dogma**: Logos supports optional gradual typing (e.g., `inscribe x: HolyInt`). These type annotations are strictly enforced at runtime and validated by the LSP.
*   **Tail Call Optimization (TCO)**: To prevent "Pride" (recursion depth exceeded errors), Logos implements a trampolining mechanism for tail-recursive `mystery` invocations.
*   **Bytecode VM Transition**: Logos supports a stack-based bytecode engine (`vm-hybrid` by default) with automatic fallback to the AST visitor when a construct is not yet lowered.
*   **Static Type Elision**: A conservative static pre-pass can skip redundant global runtime type checks when assignments are provably type-compatible, and can ingest trusted LSP facts.
*   **The Iconostasis (Structs)**: Define custom data structures using `icon`. These icons support field validation during instantiation (`write Icon { ... }`) and mutable attributes.
*   **LSP Support**: A custom Language Server (TypeScript runtime) provides real-time diagnostics, semantic token highlighting, and type inlay hints for compatible editors like VS Code. A Python server remains available as a legacy fallback.
*   **Sandbox Posture**: File I/O applies real-path containment checks, and FFI can be configured to require OS-level sandbox attestation before any foreign library is loaded.
*   **WASM-First Path**: Logos can emit bytecode artifacts suitable for execution by a WASI runtime module, enabling sandboxed non-Python hosting.

---

## 🕯️ Syntax at a Glance: Speaking the Sacred Tongue

### Variables & Types

*   Declare variables with `inscribe`.
*   Modify existing variables using `amend`.
*   Primitive types: `HolyInt` (int), `HolyFloat` (float), `Text` (string), `Bool` (`Verily`/`Nay`).
*   Aggregate types: `Procession` (list), `Icon` (struct).

```logos
// Declare an integer variable 'age'
inscribe age: HolyInt = 30;
// Mutate the value of 'age'
amend age = 31;
// Declare a string variable 'name'
inscribe name: Text = "Theophilus";
// Proclaim values to the console
proclaim name + " is " + transfigure age into Text; // Output: Theophilus is 31
```

### Control Flow: Chants, Discernment, and Contemplation

*   **Loops**: `chant` (while loop).
*   **Conditionals**: `discern` / `otherwise` (if/else).
*   **Pattern Matching**: `contemplate` / `aspect` (switch/match).

```logos
// A chant (while loop)
chant age < 100 {
    amend age = age + 1;
    proclaim age;
} amen // 'amen' signifies the end of a block

// A discernment (if-else)
discern (age >= 100) {
    proclaim "A century of devotion reached.";
} otherwise {
    proclaim "Pilgrimage continues.";
} amen

// Contemplation (pattern matching)
contemplate (age) {
    aspect 100: proclaim "The time is fulfilled.";
    aspect _:   proclaim "Still journeying...";
} amen
```

### Mysteries (Functions)

Functions are defined as `mystery` and values are returned using `offer`.

```logos
mystery calculate_penance(sins: HolyInt) -> HolyInt {
    discern (sins > 10) {
        offer sins * 2;
    } otherwise {
        offer sins;
    } amen
} amen
```

### The Vigil (Error Handling)

```logos
vigil {
    inscribe x = 1 / 0; // Runtime error
} confess sin {
    proclaim "A fault occurred during the vigil:";
    proclaim sin;
} amen
```

### The Apocrypha (Foreign Function Interface)

```logos
// Binds to the 'cos' function in msvcrt.dll (Windows) or libm.so (Linux)
apocrypha "msvcrt" mystery cos(x: HolyFloat) -> HolyFloat;

inscribe pi = 3.14159;
proclaim cos(pi); // Output: ~ -1.0
```

### Hardened Apocrypha Execution

For untrusted liturgies, keep FFI disabled (default strict mode). If FFI is required, prefer explicit signatures and enable OS-sandbox attestation gates:

```bash
uv run logos script.lg \
    --unsafe-ffi \
    --ffi-backend ctypes \
    --require-os-sandbox-for-ffi \
    --sandbox-attestation-env LOGOS_OS_SANDBOX
```

Then set `LOGOS_OS_SANDBOX` from your launcher/container only when seccomp/eBPF/AppContainer (or equivalent OS isolation) is active.

---

## 🛠️ Tooling: The Iconostasis (VS Code Extension)

The Logos VS Code extension resides in `packages/logos-vscode` and provides syntax highlighting, semantic tokens, inlay hints, and LSP diagnostics.

### Installation & Development

1.  **Navigate to the Extension Directory:**
    ```bash
    cd packages/logos-vscode
    ```
2.  **Install Node.js Dependencies:**
    ```bash
    npm install
    ```
3.  **Build the TypeScript Language Server:**
    Compile the extension client + server:
    ```bash
    npm run compile
    ```
4.  **Launch Extension Development Host:**
    In VS Code, press `F5` to open a window with the extension loaded.

### Bundled Server (Optional Legacy Fallback)

The extension can also ship with a bundled native executable of the legacy Python Language Server (built with PyInstaller).

*   **Building the Windows Server Binary:**
    ```powershell
    cd packages\logos-vscode\server
    .\build_server_win.ps1
    ```
    This generates `packages\logos-vscode\server\bin\win32\logos-lang-server.exe`.

---

## 🧪 Testing: The Inquisitor's Examination

Logos maintains a robust test suite to ensure the integrity of its "Canon."

To run all tests:

```bash
uv run pytest
```

To include coverage reports:

```bash
uv sync --group dev
uv run coverage run -m pytest
uv run coverage report
```

The suite covers grammar, runtime internals (`logos_lang`), security sandboxing, fuzzing, FFI resilience, and LSP protocol integrity.

For advanced conformance and adversarial testing domains, see [TESTING_ARCHITECTURE.md](docs/TESTING_ARCHITECTURE.md).

For the formal language definition (grammar, typing, and execution model), see [FORMAL_LANGUAGE_SPEC.md](docs/FORMAL_LANGUAGE_SPEC.md).

For the bundled standard-library contracts and builtin mysteries, see [CANON_API_REFERENCE.md](docs/CANON_API_REFERENCE.md).

For idiomatic control flow, safe Apocrypha usage, and multi-file tradition architecture, see [PILGRIMS_PATH.md](docs/PILGRIMS_PATH.md).

---

## 🏛️ Directory Layout: The Grand Design

The project uses the standard `src/` layout: one installable Python package, its bundled standard library, and separate tooling.

```
logos/
├── src/logos_lang/          # The Core Logic (The Soul) — the installable package:
│   ├── cli.py               # `logos` command / `python -m logos_lang`: CLI and REPL.
│   ├── interpreter.py       # The Runtime (The Spirit): AST visitor.
│   ├── bytecode.py          # Bytecode compiler + stack VM.
│   ├── grammar.py           # The Grammar Definition (Lark).
│   ├── ffi.py               # Foreign Function Interface logic.
│   ├── stdlib.py            # Native Python bindings for the Standard Lib.
│   ├── ...                  # Scope, types, modules, static analysis, WASI bridge.
│   └── lib/                 # The Standard Library (The Canon), imported as `tradition "std:<book>";`
│       ├── genesis.lg       # System, Time, and File I/O.
│       ├── numeri.lg        # Mathematics.
│       ├── psalms.lg        # String manipulation.
│       └── canon.lg         # Legacy typed bundle.
├── docs/                    # Formal spec, canon API reference, guide, testing architecture.
├── examples/                # Small liturgies showcasing features.
├── programs/                # Complex, multi-file programs (e.g., monk.lg, creed.lg).
├── packages/logos-vscode/   # VS Code extension:
│   ├── src/                 # TypeScript client + LSP server (analysis.ts = pure, unit-tested logic).
│   ├── server/              # Legacy Python LSP implementation (pygls).
│   └── syntaxes/            # TextMate grammar.
└── tests/                   # The Inquisitor (Test Suite):
    ├── fixtures/            # .lg programs exercised by the suites (incl. fixtures/security/).
    ├── fuzz/                # Hypothesis fuzzing and the visitor-vs-VM differential test.
    ├── stress/              # TCO benchmark tests.
    └── test_*.py            # Dogma, security, runtime, LSP and CLI suites.
```

---

## 🏗️ Architecture: The Divine Order

### The Pilgrim's Journey: Workflow Overview

```mermaid
graph TD
    User("👤 <b>The Pilgrim</b><br/>(User)")

    subgraph Stage1 ["🟦 Phase 1: Creation"]
        direction LR
        Editor("📝 <b>VS Code</b><br/>(Client)")
        LSP("💡 <b>Logos Server</b><br/>(LSP/TypeScript)")
    end

    subgraph Stage2 ["🟪 Phase 2: Execution"]
        direction LR
        CLI("logos (CLI)")
        Core("⚙️ <b>logos_lang</b><br/>(Interpreter)")
        Lib("📚 <b>std:* books</b><br/>(Canon)")
    end

    subgraph Stage3 ["🟩 Phase 3: Revelation"]
        Console("🖥️ <b>Proclamation</b><br/>(Output)")
    end

    User ==>|Writes| Editor
    Editor <-->|Diagnostics| LSP
    User ==>|Executes| CLI
    CLI --> Core
    Core -->|Imports| Lib
    Core -->|Proclaims| Console
```

---

## ⚖️ License

This project is licensed under the **MIT License**.

*Copyright (c) 2025 NikaNats*