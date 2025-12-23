# Sanctified Virtual Machine (SVM)

The SVM is the high-integrity runtime for the LOGOS language, written in Rust.

## Building

```bash
cargo build --release
```

## Running

1. Compile your LOGOS source to bytecode:
   ```bash
   python logos/compiler.py your_prayer.lg lbc
   ```

2. Execute the bytecode with the SVM:
   ```bash
   ./target/release/logos-svm your_prayer.lbc
   ```

## Architecture

- **Stack-based**: All operations perform acts of stewardship on a unified stack.
- **Synodal State**: A global key-value store for persistent essences and gifts.
- **Ontological Strictness**: Type violations and unknown spirits trigger immediate termination.
