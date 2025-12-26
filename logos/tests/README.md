## LOGOS tests

Run from the repo root:

- `python -m unittest -v`

Or run just the foreign-FFI encoding tests:

- `python -m unittest -v logos.tests.test_foreign_ffi_encoding`

Notes:
- These tests exercise the Python compiler + LBC format + Python disassembler.
- Rust VM execution tests are not included here because they require a Rust toolchain and OS-native libraries at runtime.
