from __future__ import annotations

import os
import unittest
from lark import Lark

import logos_lang


class FFISecurityDogmaTests(unittest.TestCase):
    def setUp(self) -> None:
        self.parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")

    def test_unknown_ffi_type_rejected(self) -> None:
        sec = logos_lang.SecurityContext(
            allow_ffi=True,
            whitelist={"msvcrt": {"cos"}, "m": {"cos"}},
            allow_unsafe_pointers=True,
        )
        ffi = logos_lang.FFIManager(sec)
        with self.assertRaises(logos_lang.SecurityError) as ctx:
            ffi.get_ctype("Texxt")
        self.assertIn("Unknown or unsupported FFI type", str(ctx.exception))

    def test_prototype_isolation_no_shared_state_mutation(self) -> None:
        sec = logos_lang.SecurityContext(
            allow_ffi=True,
            whitelist={"msvcrt": {"cos"}, "m": {"cos"}},
            allow_unsafe_pointers=True,
        )
        lib_name = "msvcrt" if os.name == "nt" else "m"
        ffi = logos_lang.FFIManager(sec)

        f1 = ffi.bind_function(lib_name, "cos", ["Float"], "Float")
        f2 = ffi.bind_function(lib_name, "cos", ["Double"], "Double")

        self.assertIsNot(f1.func, f2.func)

    def test_non_whitelisted_symbol_rejected(self) -> None:
        sec = logos_lang.SecurityContext(
            allow_ffi=True,
            whitelist={"msvcrt": {"cos"}, "m": {"cos"}},
        )
        ffi = logos_lang.FFIManager(sec)
        lib_name = "msvcrt" if os.name == "nt" else "m"

        with self.assertRaises(logos_lang.SecurityError) as ctx:
            ffi.bind_function(lib_name, "sin", ["Float"], "Float")
        self.assertIn("forbidden", str(ctx.exception))

    def test_path_like_library_rejected(self) -> None:
        sec = logos_lang.SecurityContext(
            allow_ffi=True,
            whitelist={"../evil": {"func"}},
        )
        ffi = logos_lang.FFIManager(sec)

        with self.assertRaises(logos_lang.SecurityError) as ctx:
            ffi.load_library("../evil")
        self.assertIn("Path-like", str(ctx.exception))


if __name__ == "__main__":
    unittest.main(verbosity=2)