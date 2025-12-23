# LOGOS (v1.2) — The Kairos Edition

### *"In the beginning was the Word, and the Word was with God, and the Word was God."*

**LOGOS** is a programming language designed with the moral and logical rigor of Orthodox Christian theology. It is not merely a tool for computation, but a framework for **Digital Asceticism**. In LOGOS, code is an icon of internal truth, and the act of programming is a discipline of the soul.

---

## Ⅰ. The Core Dogmas

### 1. Apophatic Type Fencing
Following the Apophatic tradition, LOGOS defines data by what it is *not*. A type is a "Nature" with set boundaries. If a value violates its nature, the program refuses to witness a lie and ceases execution.

### 2. Digital Asceticism (Anti-Vanity)
The LOGOS compiler implements **Watchfulness (Nepsis)**. It performs a census of symbols; any variable declared but not used is considered an "Idle Word" (*Argos Logos*). The compiler will refuse to sanctify (compile) any program containing vanity.

### 3. Sobornost (Conciliar Concurrency)
Concurrency is handled through **Sobornost** (Conciliarity). Threads are **Intercessors** that do not compete for resources but reach consensus through a **Synod** (Shared State) with reentrant locks.

### 4. Kairos vs. Chronos (Temporal Logic)
LOGOS distinguishes between quantitative time (**Chronos**) and the opportune moment of fulfillment (**Kairos**). Intercessors can wait for the "fullness of time" when ontological conditions are met, using reactive signaling without polling.

---

## Ⅱ. Linguistic Architecture

| Keyword | Theological Significance | Technical Equivalent |
| :--- | :--- | :--- |
| `essence` | Unchangeable Truth | Immutable Constant |
| `gift` | State granted by Grace | Mutable Variable |
| `service` | Pure action | Pure Function (No side effects) |
| `ministry` | Worldly interaction | Impure Function (I/O, Side effects) |
| `intercessor` | Cooperative task | Async Task / Thread |
| `council` | Consensus block | Thread-safe Lock/Critical Section |
| `witness` | Transfiguration | Safe Type Casting |
| `hamartia` | "Missing the mark" | Error / Exception |
| `repent` | Metanoia (Change of mind) | Error Handling / Catch |
| `behold` | Manifestation | Print / Logging |
| `fast` | Chronos (mechanical time) | Async Sleep |
| `wait until kairos` | Kairos (opportune moment) | Condition Wait with Timeout |
| `gather` | Communal execution | Asyncio Gather |
| `amen` | Finality and Truth | Block Terminator (`}`) |

---

## Ⅲ. Installation: The Liturgical CLI

To officiate LOGOS programs, you must have the **Logos Liturgical Engine** installed.

```bash
# Clone the repository of the faithful
git clone https://github.com/theology/logos.git
cd logos

# Install dependencies (Lark Parser)
pip install lark

# Use the 'logos' command to officiate a script
python compiler.py script.lg
```

---

## Ⅳ. Canonical Code Examples

### The Prayer of Numbers (Basic Logic)
```logos
type Probability = essence {
    not < 0;
    not > 1;
} amen

ministry main() -> Void {
    essence p : Probability = 0.7;
    behold "The nature of probability is revealed:";
    behold p;
} amen
```

### The Council of Intercessors (Sobornost & Kairos)
```logos
ministry main() -> Void {
    essence treasury = create_synod(gold=0);

    intercessor donor(t: Synod) -> Void {
        cycle (t.read("gold") < 100) limit 10 {
            await t.petition("gold", (t.read("gold") + 50));
            fast 1; // Mechanical Chronos delay
        } amen
    } amen

    intercessor distributor(t: Synod) -> Void {
        // Waiting for the Kairos of fulfillment
        wait until kairos (t.read("gold") >= 100) timeout 5 {
            behold "The gold is fulfilled. Distributing...";
            await t.petition("gold", 0);
        } repent {
            behold "The time was not fulfilled.";
        } amen
    } amen

    gather(donor(treasury), distributor(treasury));
} amen
```

---

## Ⅴ. Pastoral Guidance (Error Handling)

LOGOS does not provide cold stack traces. It provides **Pastoral Guidance**.

*   **Pride Error**: Attempting to declare global state. Logic must be contained within the "body" of a service.
*   **Gluttony Error**: A `cycle` that exceeds its `limit` of CPU cycles.
*   **Sanctity Error**: Using `behold` (I/O) inside a pure `service`.
*   **Watchfulness Error**: Attempting a `witness` (cast) without a `try/repent` block.
*   **Duplicity Error**: Shadowing an already declared name.
*   **Moral Error**: Attempting to mutate an `essence`.
*   **Ontological Error**: Violating type constraints.

---

## Ⅵ. The Philokalia (Standard Library)

The `Logos.Philokalia` module is injected into every program, providing:
*   `AbsoluteZero`: The ontological null.
*   `Trinity`: The primary 3-tuple nature.
*   `Hesychia(seconds)`: A state of stillness (async sleep).
*   `Sanctify(data)`: A function that deeply freezes any data structure into an immutable essence.
*   `SynodalState`: Shared state with reentrant locks and condition variables for Kairos.
*   `create_synod(**kwargs)`: Factory for SynodalState.

---

## Ⅶ. Contribution: The Great Synod

To contribute to LOGOS, submit a **Petition** (Pull Request). Your code will be reviewed by the **Synod Validator** for:
1.  **Logical Purity**: Does it violate Apophatic Fencing?
2.  **Asceticism**: Does it contain "Idle Words"?
3.  **Synergy**: Does it cooperate with the existing Intercessors?

**Amen.**
