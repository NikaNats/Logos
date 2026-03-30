# Canon API Reference

Version: 1.0-draft
Status: Normative reference for bundled Logos modules and injected mysteries

This manual documents the bundled standard modules under `lib/` and the built-ins injected by the runtime.
It is intended as an implementation-level contract for users, tooling, and alternate runtimes.

## 1. Module Index

- Book of Genesis: `lib/genesis.lg` (time, environment, file I/O wrappers)
- Book of Numbers: `lib/numeri.lg` (numeric helpers)
- Book of Psalms: `lib/psalms.lg` (text and sequence helpers)
- Legacy Canon bundle: `lib/canon.lg` (typed helper set)

Import behavior:

- `tradition "...";` imports exported mysteries into current scope.
- `tradition "..." as alias;` binds exports under namespace map `alias`.

## 2. Book of Genesis (`lib/genesis.lg`)

## 2.1 now

Signature:

- `now() -> HolyInt`

Contract:

- Returns Unix epoch time in milliseconds as an integer.
- Value format is numeric, not string.

Complexity:

- Time: O(1)
- Space: O(1)

Failure behavior:

- Normal operation is non-throwing.

## 2.2 rest

Signature:

- `rest(ms) -> Void`

Contract:

- Sleeps for `ms / 1000` seconds.

Complexity:

- Time: O(1) setup + wall-clock sleep duration
- Space: O(1)

Failure behavior:

- If `ms` is not convertible to numeric, host conversion error may occur.

## 2.3 since

Signature:

- `since(start_time) -> HolyInt | HolyFloat`

Contract:

- Returns elapsed milliseconds: `__sys_time() - start_time`.

Complexity:

- Time: O(1)
- Space: O(1)

Failure behavior:

- Type mismatch in subtraction raises runtime error.

## 2.4 depart

Signature:

- `depart(code) -> Never`

Contract:

- Terminates process with status code `int(code)` via `__sys_exit`.

Failure behavior:

- Raises host `SystemExit` for termination semantics.
- This is not a normal `Exception`; a `vigil` block does not guarantee interception.

## 2.5 get_env

Signature:

- `get_env(key, default) -> Text`

Contract:

- Reads environment key via `__sys_env(key)`.
- If resulting text length is zero, returns `default`; otherwise returns environment value.

Complexity:

- Time: O(|value|) due to `measure(val)`
- Space: O(1) excluding returned text

Semantics note:

- Missing key and empty-string key value are treated identically (both return `default`).

## 2.6 open_scroll

Signature:

- `open_scroll(path, mode) -> HolyInt`

Contract:

- Forwards to `__sys_open(path, mode)`.
- Mode mapping in runtime:
  - `0` => read (`r`)
  - `1` => write (`w`)
  - `2` => append (`a`)
  - any other value => read (`r`)

Failure behavior:

- On sandbox/path/IO failure, returns `0`.
- Does not throw by contract for ordinary failure paths.

## 2.7 close_scroll

Signature:

- `close_scroll(fd) -> Void`

Contract:

- Closes descriptor if valid; otherwise no-op.

Complexity:

- Time: O(1)
- Space: O(1)

## 2.8 write_line

Signature:

- `write_line(fd, text) -> Bool`

Contract:

- Writes `text`, then newline `"\n"`.
- Returns result of newline write (`Verily` on success, `Nay` on failure).

Complexity:

- Time: O(|text|)
- Space: O(1)

Failure behavior:

- Invalid descriptor yields `Nay`.

## 2.9 read_passage

Signature:

- `read_passage(fd, length) -> Text`

Contract:

- Returns up to `length` characters from descriptor.

Complexity:

- Time: O(min(length, remaining_file_chars))
- Space: O(returned_text)

Failure behavior:

- Invalid descriptor returns empty string `""`.

## 2.10 read_all

Signature:

- `read_all(fd) -> Text`

Contract:

- Equivalent to `__sys_read(fd, -1)`; returns all remaining text.

Complexity:

- Time: O(remaining_file_chars)
- Space: O(returned_text)

Failure behavior:

- Invalid descriptor returns empty string `""`.

## 3. Book of Numbers (`lib/numeri.lg`)

## 3.1 abs

Signature:

- `abs(n) -> same as n domain`

Contract:

- Returns magnitude using branch `n < 0 ? 0 - n : n`.

Complexity:

- Time: O(1)
- Space: O(1)

## 3.2 max

Signature:

- `max(a, b) -> one of {a, b}`

Contract:

- Returns greater operand by `>` comparison.

Complexity:

- Time: O(1)
- Space: O(1)

## 3.3 min

Signature:

- `min(a, b) -> one of {a, b}`

Contract:

- Returns smaller operand by `<` comparison.

Complexity:

- Time: O(1)
- Space: O(1)

## 3.4 is_even

Signature:

- `is_even(n) -> Bool`

Contract:

- Computes `half = n / 2`, then checks `half * 2 is n`.
- Intended for integer-style parity checks.

Complexity:

- Time: O(1)
- Space: O(1)

## 3.5 power

Signature:

- `power(base, exp) -> numeric`

Contract:

- Iterative repeated multiplication from `i = 0` while `i < exp`.

Complexity:

- Time: O(exp)
- Space: O(1)

Domain note:

- Designed for non-negative integer `exp`.
- Negative or non-integer exponents are not mathematically normalized by this implementation.

## 3.6 factorial

Signature:

- `factorial(n) -> HolyInt`

Contract:

- Returns `1` for `n <= 1`.
- Otherwise iteratively multiplies from `2..n`.
- Implementation intentionally avoids recursive formulation.

Complexity:

- Time: O(n)
- Space: O(1)

Domain note:

- Designed for non-negative integer `n`.

## 4. Book of Psalms (`lib/psalms.lg`)

## 4.1 is_empty

Signature:

- `is_empty(text) -> Bool`

Contract:

- Returns `Verily` when `measure(text) is 0`, else `Nay`.

Complexity:

- Time: O(1) for typical host string/list length metadata
- Space: O(1)

## 4.2 first_char

Signature:

- `first_char(text) -> Text`

Contract:

- Returns first character (`passage(text, 0, 1)`) if non-empty.
- Returns empty string `""` if empty.

Complexity:

- Time: O(1)
- Space: O(1)

## 4.3 concat_procession

Signature:

- `concat_procession(list) -> Text`

Contract:

- Concatenates procession items from index `0..len-1`.

Complexity:

- Time: O(total_chars^2) worst-case on immutable-string hosts due to repeated concatenation
- Space: O(total_chars)

Practical note:

- Not ideal for massive concatenation workloads.

## 4.4 contains

Signature:

- `contains(haystack, needle) -> Bool`

Contract:

- Performs naive sliding-window substring search using `passage` + equality.
- Early exits on first match.

Complexity:

- Worst case: O(N x M), where N = `measure(haystack)`, M = `measure(needle)`
- Best case: O(M) for immediate prefix match

Practical note:

- Not suitable for large-scale text search where asymptotic performance is critical.

## 5. Built-in Mysteries (Runtime-Injected)

These are implicitly injected by runtime startup and available without import.

## 5.1 Core Collection/Text Helpers

### measure

Signature:

- `measure(x: Procession | Text | any __len__-capable) -> HolyInt`

Contract:

- Returns length for values implementing host `len`.
- Returns `0` for values without length protocol.

Complexity:

- Time: O(1) for standard host sequence types

### adorn

Signature:

- `adorn(xs: Procession[T], item: T) -> Procession[T]`

Contract:

- Alias of `append`.
- Mutates `xs` in place by appending `item`.
- Returns same list object.

Complexity:

- Amortized O(1)

### append

Signature:

- `append(xs: Procession[T], item: T) -> Procession[T]`

Contract:

- In-place append; returns mutated list.

Complexity:

- Amortized O(1)

### extract

Signature:

- `extract(xs: Procession[T]) -> T | None`

Contract:

- Pops and returns last element.
- Returns `None` on empty list.

Complexity:

- O(1)

### purge

Signature:

- `purge(xs: Procession[Any]) -> Void`

Contract:

- Clears list in place.

Complexity:

- O(n) element release in typical host memory model

### passage

Signature:

- `passage(text, start, length) -> Text`

Contract:

- Converts `text` to string.
- Returns substring `[start : start + length]`.
- `length <= 0` => `""`
- Negative `start` counts from end and clamps to 0.

Complexity:

- O(length) for produced slice size

## 5.2 Time, Environment, Process

### now

Signature:

- `now() -> HolyInt`

Contract:

- Epoch milliseconds integer.

### env

Signature:

- `env(key) -> Text`

Contract:

- Returns env var text or empty string if missing.

### __sys_time

Alias of `now`.

### __sys_env

Alias of `env`.

### __sys_sleep

Signature:

- `__sys_sleep(ms) -> Void`

Contract:

- Sleeps `float(ms) / 1000.0`.

### __sys_exit

Signature:

- `__sys_exit(code) -> Never`

Contract:

- Terminates process via `SystemExit(int(code))`.

## 5.3 File I/O Built-ins

### __sys_open

Signature:

- `__sys_open(path, mode) -> HolyInt`

Contract:

- Resolves path under interpreter base path using realpath containment.
- Blocks traversal and symlink escape outside base path.
- Opens in UTF-8 text mode.
- Returns file descriptor >= 3 on success.
- Returns `0` on failure.

### __sys_close

Signature:

- `__sys_close(fd) -> Void`

Contract:

- Closes known descriptor; no-op otherwise.

### __sys_write

Signature:

- `__sys_write(fd, content) -> Bool`

Contract:

- Writes `str(content)` and flushes.
- Returns `Verily` on success, `Nay` on invalid descriptor.

### __sys_read

Signature:

- `__sys_read(fd, length) -> Text`

Contract:

- If `length < 0`, reads all remaining text.
- Else reads up to `int(length)` characters.
- Returns empty string on invalid descriptor.

Expected format:

- Returns plain text string exactly as decoded from file stream (UTF-8 file mode).
- Does not return bytes.

### __sys_str

Signature:

- `__sys_str(x) -> Text`

Contract:

- Host string conversion.

## 5.4 Runtime Argv

### argv

Signature:

- `argv -> Procession[Text]`

Contract:

- Injected as startup argument tail from host process.

## 6. Legacy Canon Bundle (`lib/canon.lg`)

`lib/canon.lg` provides an older composite helper set (typed mysteries such as `pow`, `equals`, `ask_int`, logical helpers). It remains useful for compatibility, but for explicit domain APIs prefer:

- `lib/numeri.lg` for numeric helpers
- `lib/psalms.lg` for text/sequence helpers
- `lib/genesis.lg` for system and I/O wrappers

## 7. Error and Vigil Interoperability Notes

- Sentinel-return APIs:
  - `__sys_open` returns `0` on failure.
  - `__sys_read` returns `""` on invalid descriptor.
  - `__sys_write` returns `Nay` on invalid descriptor.
- Exceptional APIs:
  - `__sys_exit` terminates process (`SystemExit`).
  - Numeric/string conversion errors in helper functions can raise host exceptions.

Best practice:

- Wrap risky operations in `vigil { ... } confess err { ... } amen` when graceful handling is desired.
