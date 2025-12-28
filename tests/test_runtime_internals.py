from __future__ import annotations

import io
import os
import tempfile
import unittest
from unittest.mock import patch
from contextlib import redirect_stdout

import ctypes

import logos


class RuntimeInternalsTests(unittest.TestCase):
    def _run_program(self, source: str, base_path: str | None = None) -> tuple[logos.LogosInterpreter, str]:
        interp = logos.LogosInterpreter(base_path=base_path)
        interp._current_file = os.path.join(interp.base_path, "__test__.lg")
        parser = logos.Lark(logos.LOGOS_GRAMMAR, parser="lalr")
        tree = parser.parse(source)
        buf = io.StringIO()
        with redirect_stdout(buf):
            interp.visit(tree)
        return interp, buf.getvalue()

    def _make_security(self, libs: list[str] | None = None, allow_unsafe_pointers: bool = True) -> logos.SecurityContext:
        libs = libs or [
            "mylib",
            "winlib",
            "m",
            "libm",
            "c",
            "libc",
            "definitely_not_a_real_library_12345",
        ]
        whitelist = {name: set() for name in libs}
        return logos.SecurityContext(allow_ffi=True, whitelist=whitelist, allow_unsafe_pointers=allow_unsafe_pointers)

    def _make_ffi(self, libs: list[str] | None = None, allow_unsafe_pointers: bool = True) -> logos.FFIManager:
        return logos.FFIManager(self._make_security(libs, allow_unsafe_pointers))

    def test_scope_manager_get_set_declare(self) -> None:
        s = logos.ScopeManager()
        s.set("g", 1)
        self.assertEqual(s.get("g"), 1)

        s.push_frame({"x": "local"})
        s.declare("g", 2)  # shadows global inside frame
        self.assertEqual(s.get("g"), 2)
        s.pop_frame()
        self.assertEqual(s.get("g"), 1)

        with self.assertRaises(logos.LogosError):
            s.get("missing")

    def test_scope_manager_set_updates_existing_local_and_global(self) -> None:
        s = logos.ScopeManager()

        # Update existing global
        s.set("x", 1)
        s.set("x", 2)
        self.assertEqual(s.get("x"), 2)

        # Update existing local
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

    def test_ffi_load_library_filename_selection_branches(self) -> None:
        ffi = self._make_ffi()

        # Explicit extension
        ffi.libs["mylib.dll"] = object()  # prevent CDLL load
        self.assertEqual(ffi.load_library("mylib.dll"), "mylib.dll")

        original_os_name = logos.os.name
        original_platform = logos.sys.platform
        try:
            # Windows filename branch
            logos.os.name = "nt"
            logos.sys.platform = "win32"
            ffi.libs["winlib.dll"] = object()
            self.assertEqual(ffi.load_library("winlib"), "winlib.dll")

            # macOS filename branch
            logos.os.name = "posix"
            logos.sys.platform = "darwin"
            ffi.libs["libm.dylib"] = object()
            self.assertEqual(ffi.load_library("m"), "libm.dylib")

            # Other POSIX filename branch
            logos.os.name = "posix"
            logos.sys.platform = "linux"
            ffi.libs["libc.so"] = object()
            self.assertEqual(ffi.load_library("c"), "libc.so")
        finally:
            logos.os.name = original_os_name
            logos.sys.platform = original_platform

    def test_ffi_load_library_error_path(self) -> None:
        ffi = self._make_ffi()
        with self.assertRaises(logos.LogosError):
            ffi.load_library("definitely_not_a_real_library_12345")

    def test_ffi_marshal_args_bytes_and_numbers(self) -> None:
        ffi = self._make_ffi()
        # Create a dummy ForeignFunction definition for marshalling only.
        dummy = logos.ForeignFunction(func=None, restype=ctypes.c_double, argtypes=[ctypes.c_char_p, ctypes.c_double, ctypes.c_longlong])
        out = ffi.marshal_args([b"hi", 1.5, 7], dummy)
        self.assertEqual(out[0], b"hi")
        self.assertEqual(out[1], 1.5)
        self.assertEqual(out[2], 7)

    def test_ffi_marshal_args_else_branch(self) -> None:
        ffi = self._make_ffi()
        dummy = logos.ForeignFunction(func=None, restype=ctypes.c_double, argtypes=[ctypes.c_bool])
        out = ffi.marshal_args([True], dummy)
        self.assertEqual(out, [True])

    def test_amend_undeclared_raises(self) -> None:
        interp = logos.LogosInterpreter()
        parser = logos.Lark(logos.LOGOS_GRAMMAR, parser="lalr")
        with self.assertRaises(logos.LogosError):
            tree = parser.parse("amend x = 1;")
            interp.visit(tree)

    def test_stdlib_io_and_list_ops(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            std = logos.StdLib(td)
            scope = logos.ScopeManager()
            std.register_into(scope)

            fd = scope.get("__sys_open")("x.txt", 1)
            self.assertNotEqual(fd, 0)
            self.assertTrue(scope.get("__sys_write")(fd, "abc"))
            scope.get("__sys_close")(fd)

            fd2 = scope.get("__sys_open")("x.txt", 0)
            self.assertNotEqual(fd2, 0)
            self.assertEqual(scope.get("__sys_read")(fd2, -1), "abc")
            scope.get("__sys_close")(fd2)

            # measure/append/extract/purge
            self.assertEqual(scope.get("measure")([1, 2, 3]), 3)
            self.assertEqual(scope.get("measure")(123), 0)
            lst = []
            scope.get("append")(lst, 1)
            self.assertEqual(lst, [1])
            self.assertEqual(scope.get("extract")([]), None)
            scope.get("purge")(lst)
            self.assertEqual(lst, [])

            # _write false branch (bad fd)
            self.assertFalse(scope.get("__sys_write")(9999, "x"))

    def test_builtin_exit_and_sleep_are_callable(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            std = logos.StdLib(td)
            scope = logos.ScopeManager()
            std.register_into(scope)

            with patch("time.sleep") as sleep:
                scope.get("__sys_sleep")(1)
                sleep.assert_called()

            with self.assertRaises(SystemExit):
                scope.get("__sys_exit")(0)

    def test_interpreter_init_handles_recursionlimit_failure(self) -> None:
        original = logos.sys.setrecursionlimit
        try:
            def boom(_):
                raise Exception("nope")

            logos.sys.setrecursionlimit = boom
            _ = logos.LogosInterpreter()
        finally:
            logos.sys.setrecursionlimit = original

    def test_emit_unicode_fallback_path(self) -> None:
        calls: list[str] = []

        def flaky_print(msg: str):
            # Fail only for the first attempt (the unicode symbol path).
            if not calls:
                calls.append("raised")
                raise UnicodeEncodeError("cp1252", "x", 0, 1, "boom")
            calls.append(msg)

        original_print = getattr(logos, "print", None)
        try:
            logos.print = flaky_print  # type: ignore[attr-defined]
            logos.LogosInterpreter._emit("☩", "hello")
        finally:
            if original_print is None:
                delattr(logos, "print")
            else:
                logos.print = original_print  # type: ignore[assignment]

        self.assertTrue(any("hello" in c for c in calls if c != "raised"))

    def test_supplicate_can_be_tested(self) -> None:
        interp = logos.LogosInterpreter()
        # Build a small parse tree for `supplicate "x"` and patch input.
        parser = logos.Lark(logos.LOGOS_GRAMMAR, parser="lalr", start="expr")
        tree = parser.parse('supplicate "prompt"')
        with patch("builtins.input", return_value="answer"):
            self.assertEqual(interp.visit(tree), "answer")

    def test_chant_runs_at_least_once(self) -> None:
        _, out = self._run_program(
            "\n".join(
                [
                    "inscribe x = 0;",
                    "chant x < 3 { amend x = x + 1; } amen",
                    "proclaim x;",
                ]
            )
        )
        self.assertIn("3", out)

    def test_silence_statement_executes(self) -> None:
        _, out = self._run_program("silence;")
        self.assertEqual(out, "")

    def test_mystery_def_invalid_name_raises(self) -> None:
        with self.assertRaises(logos.LogosError):
            self._run_program("mystery BadName() { silence; } amen")

    def test_mystery_def_return_type_is_accepted(self) -> None:
        _, out = self._run_program(
            "\n".join(
                [
                    "mystery foo() -> HolyInt { offer 1; } amen",
                    "proclaim foo();",
                ]
            )
        )
        self.assertIn("1", out)

    def test_calling_non_callable_raises(self) -> None:
        with self.assertRaises(logos.LogosError):
            self._run_program("inscribe x = 1; x();")

    def test_user_function_arity_mismatch_raises(self) -> None:
        with self.assertRaises(logos.LogosError):
            self._run_program("mystery foo(a) { offer a; } amen\nfoo();")

    def test_icon_def_invalid_name_raises(self) -> None:
        with self.assertRaises(logos.LogosError):
            self._run_program("icon bad { a: HolyInt; } amen")

    def test_icon_def_skips_non_field_decl_child(self) -> None:
        interp = logos.LogosInterpreter()

        class Dummy:
            def __init__(self, data: str):
                self.data = data
                self.children: list[object] = []

        class FakeTree:
            def __init__(self):
                self.children = ["MyIcon", Dummy("not_field_decl")]

        interp.icon_def(FakeTree())
        self.assertEqual(interp._icons.get("MyIcon"), {})

    def test_amend_var_hits_mut_var_set(self) -> None:
        _, out = self._run_program("inscribe x: HolyInt = 1; amend x = 2; proclaim x;")
        self.assertIn("2", out)

    def test_amend_attr_non_dict_hits_setattr(self) -> None:
        # `now` is a builtin lambda in the global scope; it is not a dict.
        self._run_program("amend now.some_attr = 1;")

    def test_perform_mutation_invalid_target_raises(self) -> None:
        interp = logos.LogosInterpreter()

        class FakeNode:
            data = "mut_weird"
            children: list[object] = []

        with self.assertRaises(logos.LogosError):
            interp._perform_mutation(FakeNode(), 1)

    def test_declare_type_redeclaration_errors_global_and_local(self) -> None:
        interp = logos.LogosInterpreter()

        # Global redeclare
        interp._declare_type("x", "HolyInt")
        with self.assertRaises(logos.LogosError):
            interp._declare_type("x", "HolyFloat")

        # Local redeclare
        interp.scope.push_frame({})
        interp._type_stack.append({})
        try:
            interp._declare_type("y", "HolyInt")
            with self.assertRaises(logos.LogosError):
                interp._declare_type("y", "HolyFloat")
        finally:
            interp._type_stack.pop()
            interp.scope.pop_frame()

    def test_enforce_icon_field_type_early_returns(self) -> None:
        interp = logos.LogosInterpreter()

        # No __icon__
        interp._enforce_icon_field_type({}, "a", 1)

        # __icon__ but no schema
        interp._enforce_icon_field_type({"__icon__": "NoSuch"}, "a", 1)

        # Schema exists but field missing
        interp._icons["Thing"] = {"x": "HolyInt"}
        interp._enforce_icon_field_type({"__icon__": "Thing"}, "missing", 1)

    def test_enforce_value_type_branches_and_unknown_type(self) -> None:
        interp = logos.LogosInterpreter()
        interp._enforce_value_type(1, "HolyInt", context="x")
        interp._enforce_value_type(1.0, "Float", context="x")
        interp._enforce_value_type(True, "Bool", context="x")
        interp._enforce_value_type("s", "Text", context="x")
        interp._enforce_value_type([], "Procession", context="x")
        # Unknown types are accepted
        interp._enforce_value_type(object(), "MysteryType", context="x")

        with self.assertRaises(logos.LogosError):
            interp._enforce_value_type("nope", "HolyInt", context="x")

    def test_evaluate_mutable_target_attr_and_item_paths(self) -> None:
        interp = logos.LogosInterpreter()

        class Node:
            def __init__(self, data: str, children: list[object]):
                self.data = data
                self.children = children

        # dict attribute
        interp.scope.set("d", {"k": 9})
        node = Node("mut_attr", [Node("mut_var", ["d"]), "k"])
        self.assertEqual(interp._evaluate_mutable_target(node), 9)

        # list item
        interp.scope.set("lst", [1, 2, 3])
        idx_tree = logos.Lark(logos.LOGOS_GRAMMAR, parser="lalr", start="expr").parse("1")
        node2 = Node("mut_item", [Node("mut_var", ["lst"]), idx_tree])
        # The index is a parse tree; visit will return int.
        self.assertEqual(interp._evaluate_mutable_target(node2), 2)

        # Fallback branch: visit the node directly
        expr_tree = logos.Lark(logos.LOGOS_GRAMMAR, parser="lalr", start="expr").parse("1")
        self.assertEqual(interp._evaluate_mutable_target(expr_tree), 1)

    def test_transfigure_unknown_type_returns_value(self) -> None:
        _, out = self._run_program("proclaim transfigure 5 into Unknown;")
        self.assertIn("5", out)

    def test_contemplation_no_match_returns_none(self) -> None:
        # As a statement; return value is ignored, but we still exercise the code path.
        self._run_program("contemplate(1){ aspect 2: { silence; } } amen")

    def test_unknown_tradition_raises(self) -> None:
        interp = logos.LogosInterpreter(base_path=os.getcwd())
        parser = logos.Lark(logos.LOGOS_GRAMMAR, parser="lalr", start="statement")
        t = parser.parse('tradition "no_such_file_12345.lg";')
        with self.assertRaises(logos.LogosError):
            interp.visit(t)


if __name__ == "__main__":  # pragma: no cover
    unittest.main(verbosity=2)
