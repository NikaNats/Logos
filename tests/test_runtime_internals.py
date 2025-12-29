from __future__ import annotations
import io
import os
import tempfile
import unittest
from contextlib import redirect_stdout
from unittest.mock import patch
import ctypes

from lark import Lark

# Import from package
import logos_lang

class RuntimeInternalsTests(unittest.TestCase):
    def _run_program(self, source: str, base_path: str | None = None) -> tuple[logos_lang.LogosInterpreter, str]:
        interp = logos_lang.LogosInterpreter(base_path=base_path)
        # Mock IO for capture
        interp.io = logos_lang.ConsoleIO()
        parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")
        tree = parser.parse(source)
        buf = io.StringIO()
        with redirect_stdout(buf):
            interp.visit(tree)
        return interp, buf.getvalue()

    def _make_ffi(self, libs=None, allow_unsafe=True):
        libs = libs or ["m", "c"]
        whitelist = {name: set() for name in libs}
        sec = logos_lang.SecurityContext(allow_ffi=True, whitelist=whitelist, allow_unsafe_pointers=allow_unsafe)
        return logos_lang.FFIManager(sec)

    def test_scope_manager_get_set_declare(self) -> None:
        s = logos_lang.ScopeManager()
        s.set("g", 1)
        self.assertEqual(s.get("g"), 1)
        s.push_frame({"x": "local"})
        s.declare("g", 2)
        self.assertEqual(s.get("g"), 2)
        s.pop_frame()
        self.assertEqual(s.get("g"), 1)
        with self.assertRaises(logos_lang.LogosError):
            s.get("missing")

    def test_scope_manager_set_updates_existing_local_and_global(self) -> None:
        s = logos_lang.ScopeManager()
        s.set("x", 1)
        s.set("x", 2)
        self.assertEqual(s.get("x"), 2)
        s.push_frame({"y": 1})
        s.set("y", 2)
        self.assertEqual(s.get("y"), 2)
        s.pop_frame()

    def test_ffi_manager_type_mapping_and_infer(self) -> None:
        ffi = self._make_ffi()
        self.assertIs(ffi.get_ctype("HolyInt"), ctypes.c_longlong)
        self.assertIs(ffi.get_ctype("Text"), ctypes.c_char_p)
        self.assertIs(ffi.get_ctype("Unknown"), ctypes.c_double)
        self.assertIs(ffi.infer_ctype_from_value("x"), ctypes.c_char_p)
        self.assertIs(ffi.infer_ctype_from_value(True), ctypes.c_bool)
        self.assertIs(ffi.infer_ctype_from_value(1), ctypes.c_double)
        self.assertIs(ffi.infer_ctype_from_value(object()), ctypes.c_double)

    def test_ffi_load_library_error_path(self) -> None:
        ffi = self._make_ffi()
        with self.assertRaises(logos_lang.LogosError):
            ffi.load_library("definitely_not_a_real_library_12345")

    def test_ffi_marshal_args_bytes_and_numbers(self) -> None:
        ffi = self._make_ffi()
        dummy = logos_lang.ForeignFunction(
            func=None,
            restype=ctypes.c_double,
            argtypes=[ctypes.c_char_p, ctypes.c_double, ctypes.c_longlong],
        )
        out = ffi.marshal_args([b"hi", 1.5, 7], dummy)
        self.assertEqual(out[0], b"hi")
        self.assertEqual(out[1], 1.5)
        self.assertEqual(out[2], 7)

    def test_amend_undeclared_raises(self) -> None:
        interp = logos_lang.LogosInterpreter()
        parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")
        with self.assertRaises(logos_lang.LogosError):
            tree = parser.parse("amend x = 1;")
            interp.visit(tree)

    def test_stdlib_io_and_list_ops(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            std = logos_lang.StdLib(td)
            scope = logos_lang.ScopeManager()
            std.register_into(scope)
            fd = scope.get("__sys_open")("x.txt", 1)
            self.assertNotEqual(fd, 0)
            self.assertTrue(scope.get("__sys_write")(fd, "abc"))
            scope.get("__sys_close")(fd)
            self.assertEqual(scope.get("measure")([1, 2]), 2)

    def test_chant_runs_at_least_once(self) -> None:
        _, out = self._run_program("inscribe x=0; chant x<3 { amend x=x+1; } amen proclaim x;")
        self.assertIn("3", out)

    def test_mystery_def_invalid_name_raises(self) -> None:
        with self.assertRaises(logos_lang.LogosError):
            self._run_program("mystery BadName() { silence; } amen")

    def test_calling_non_callable_raises(self) -> None:
        with self.assertRaises(logos_lang.LogosError):
            self._run_program("inscribe x=1; x();")

    def test_transfigure_unknown_type_returns_value(self) -> None:
        _, out = self._run_program("proclaim transfigure 5 into Unknown;")
        self.assertIn("5", out)

    def test_unknown_tradition_raises(self) -> None:
        interp = logos_lang.LogosInterpreter(base_path=os.getcwd())
        parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr", start="statement")
        t = parser.parse('tradition "no_such_file_12345.lg";')
        with self.assertRaises(logos_lang.LogosError):
            interp.visit(t)

if __name__ == "__main__":
    unittest.main(verbosity=2)
