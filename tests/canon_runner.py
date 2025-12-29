from __future__ import annotations

import os
import re
import sys
import unittest
from contextlib import redirect_stdout
from dataclasses import dataclass
from io import StringIO
from pathlib import Path

from lark import Lark

import logos_lang


ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "tests" / "fixtures"


@dataclass
class _ExecResult:
    stdout: str
    error: Exception | None


def _execute_fixture(
    fixture_name: str,
    *,
    env: dict[str, str] | None = None,
    security: logos_lang.SecurityContext | None = None,
) -> _ExecResult:
    fixture_path = FIXTURES / fixture_name
    if not fixture_path.exists():
        raise FileNotFoundError(f"Missing fixture: {fixture_path}")

    if env:
        for k, v in env.items():
            os.environ[str(k)] = str(v)

    interpreter = logos_lang.LogosInterpreter(
        base_path=str(FIXTURES), 
        security=security or logos_lang.SecurityContext.strict()
    )
    interpreter._current_file = str(fixture_path)
    parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")

    buf = StringIO()
    err: Exception | None = None
    # Patch IO to ensure we capture interpreter output deterministically.
    interpreter.io = logos_lang.ConsoleIO()

    with redirect_stdout(buf):
        try:
            source = fixture_path.read_text(encoding="utf-8")
            interpreter.visit(parser.parse(source))

            # Invoke main if defined.
            try:
                main_func = interpreter.scope.get("main")
            except logos_lang.LogosError:
                main_func = None
            if isinstance(main_func, logos_lang.UserFunction):
                interpreter._invoke_user_function(main_func, [])
        except Exception as e:
            err = e

    return _ExecResult(stdout=buf.getvalue(), error=err)


def _permissive_security(allow_pointers: bool = False) -> logos_lang.SecurityContext:
    sec = logos_lang.SecurityContext.permissive()
    sec.allow_unsafe_pointers = allow_pointers
    return sec


def _assert_value_line(test: unittest.TestCase, stdout: str, value: str) -> None:
    # Interpreter may print with a Unicode prefix (☩) or ASCII fallback (+).
    pattern = rf"(?:☩|\+)\s+{re.escape(value)}"
    test.assertRegex(stdout, pattern)


class CanonTests(unittest.TestCase):
    # I. Dogma (Syntax & Semantics)

    def test_precedence_multiplication_before_addition(self) -> None:
        r = _execute_fixture("precedence_1.lg")
        self.assertIsNone(r.error)
        _assert_value_line(self, r.stdout, "14")

    def test_associativity_left(self) -> None:
        r = _execute_fixture("precedence_2.lg")
        self.assertIsNone(r.error)
        _assert_value_line(self, r.stdout, "3")

    def test_variable_shadowing(self) -> None:
        r = _execute_fixture("shadowing.lg")
        self.assertIsNone(r.error)
        # Expect Local then Global.
        self.assertRegex(r.stdout, r"(?:☩|\+)\s+Local")
        self.assertRegex(r.stdout, r"(?:☩|\+)\s+Global")
        self.assertLess(r.stdout.index("Local"), r.stdout.index("Global"))

    def test_chant_false_initially(self) -> None:
        r = _execute_fixture("chant_false_initially.lg")
        self.assertIsNone(r.error)
        self.assertNotIn("Heresy", r.stdout)

    # III. Confessional (Error Handling)

    def test_vigil_catches_runtime_exception(self) -> None:
        r = _execute_fixture("vigil_div0.lg")
        self.assertIsNone(r.error)
        self.assertRegex(r.stdout, r"(?:☩|\+)\s+Forgiven")

    def test_vigil_reraises_return_signal(self) -> None:
        r = _execute_fixture("vigil_return_signal.lg")
        self.assertIsNone(r.error)
        self.assertIn("before", r.stdout)
        self.assertNotIn("bad", r.stdout)
        self.assertNotIn("after", r.stdout)

    def test_recursion_limit_reports_pride(self) -> None:
        # Use a small limit to keep the test fast and avoid hitting Python recursion.
        r = _execute_fixture("recursion_overflow.lg", env={"LOGOS_MAX_RECURSION": "50"})
        self.assertIsNotNone(r.error)
        self.assertIn("Pride: Recursion depth exceeded", str(r.error))

    # IV. Iconostasis (Data Structures)

    def test_icon_reference_semantics(self) -> None:
        r = _execute_fixture("icon_reference_semantics.lg")
        self.assertIsNone(r.error)
        _assert_value_line(self, r.stdout, "2")

    def test_empty_extract_safe(self) -> None:
        r = _execute_fixture("empty_extract.lg")
        self.assertIsNone(r.error)
        _assert_value_line(self, r.stdout, "None")

    # Type system facade (runtime enforcement)

    def test_amend_type_mismatch_errors(self) -> None:
        r = _execute_fixture("type_mismatch_amend.lg")
        self.assertIsNotNone(r.error)
        self.assertIn("Canon Error: Type mismatch", str(r.error))

    # Recursion mitigation (tail-call optimization)

    def test_tail_call_optimization_deep(self) -> None:
        r = _execute_fixture("tco_deep.lg")
        self.assertIsNone(r.error)
        _assert_value_line(self, r.stdout, "0")

    def test_tail_call_optimization_mutual_recursion(self) -> None:
        r = _execute_fixture("mutual_tco_even_odd.lg")
        self.assertIsNone(r.error)
        # is_even(10000) should be True
        _assert_value_line(self, r.stdout, "Verily")

    # II. Apocrypha (FFI)

    @unittest.skipUnless(sys.platform.startswith("win"), "Windows-only FFI test")
    def test_ffi_puts_no_crash(self) -> None:
        r = _execute_fixture(
            "ffi_puts_windows.lg", security=_permissive_security(allow_pointers=True)
        )
        self.assertIsNone(r.error)
        # NOTE: msvcrt.puts writes via the C runtime and may bypass Python stdout capture.

    @unittest.skipUnless(sys.platform.startswith("win"), "Windows-only FFI test")
    def test_ffi_arity_mismatch_rejected(self) -> None:
        r = _execute_fixture(
            "foreign_arity_mismatch.lg",
            security=_permissive_security(allow_pointers=True),
        )
        self.assertIsNotNone(r.error)
        self.assertIn("Invocation Error", str(r.error))

    @unittest.skipUnless(sys.platform.startswith("win"), "Windows-only FFI test")
    def test_ffi_infer_argtypes(self) -> None:
        r = _execute_fixture(
            "ffi_infer_argtypes_windows.lg",
            security=_permissive_security(allow_pointers=True),
        )
        self.assertIsNone(r.error)
        # NOTE: msvcrt.puts writes via the C runtime and may bypass Python stdout capture.

    # Misc semantic paths for coverage

    def test_contemplation_wildcard(self) -> None:
        r = _execute_fixture("contemplation_wildcard.lg")
        self.assertIsNone(r.error)
        _assert_value_line(self, r.stdout, "9")

    def test_transfigure(self) -> None:
        r = _execute_fixture("transfigure_test.lg")
        self.assertIsNone(r.error)
        _assert_value_line(self, r.stdout, "5")

    def test_mutation_out_of_bounds_caught(self) -> None:
        r = _execute_fixture("mutation_out_of_bounds_caught.lg")
        self.assertIsNone(r.error)
        self.assertRegex(r.stdout, r"(?:☩|\+)\s+Forgiven")
        self.assertIn("Invalid mutation access", r.stdout)

    def test_get_item_out_of_bounds_caught(self) -> None:
        r = _execute_fixture("get_item_out_of_bounds_caught.lg")
        self.assertIsNone(r.error)
        self.assertRegex(r.stdout, r"(?:☩|\+)\s+Forgiven")
        self.assertIn("Index", r.stdout)

    def test_sys_open_missing_returns_zero(self) -> None:
        r = _execute_fixture("sys_open_missing.lg")
        self.assertIsNone(r.error)
        _assert_value_line(self, r.stdout, "0")

    def test_sys_read_write_roundtrip(self) -> None:
        r = _execute_fixture("sys_read_write_roundtrip.lg")
        self.assertIsNone(r.error)
        self.assertIn("hello", r.stdout)

    def test_tradition_import(self) -> None:
        r = _execute_fixture("tradition_import.lg")
        self.assertIsNone(r.error)
        _assert_value_line(self, r.stdout, "42")

    def test_tradition_cyclic_imports_do_not_loop(self) -> None:
        r = _execute_fixture("cyclic_import_main.lg")
        self.assertIsNone(r.error)
        _assert_value_line(self, r.stdout, "3")

    def test_tradition_namespace_collision_overwrites(self) -> None:
        r = _execute_fixture("polluted_altar_main.lg")
        self.assertIsNone(r.error)
        # Current semantics: imported file executes immediately in the same interpreter instance.
        _assert_value_line(self, r.stdout, "1")

    def test_tradition_aliases_isolate_globals(self) -> None:
        r = _execute_fixture("tradition_alias_isolation.lg")
        self.assertIsNone(r.error)
        _assert_value_line(self, r.stdout, "1")
        _assert_value_line(self, r.stdout, "2")
        _assert_value_line(self, r.stdout, "100")
        _assert_value_line(self, r.stdout, "11")
        _assert_value_line(self, r.stdout, "20")


if __name__ == "__main__":
    unittest.main(verbosity=2)
