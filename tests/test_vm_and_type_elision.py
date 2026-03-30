from __future__ import annotations

import io
import unittest
from contextlib import redirect_stdout

from lark import Lark

import logos_lang


class VMAndTypeElisionTests(unittest.TestCase):
    def _parse(self, source: str):
        return Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr").parse(source)

    def test_vm_hybrid_executes_simple_program(self) -> None:
        source = "inscribe age: HolyInt = 40; amend age = age + 2; proclaim age;"
        tree = self._parse(source)
        interp = logos_lang.LogosInterpreter(execution_engine="vm-hybrid")

        buf = io.StringIO()
        with redirect_stdout(buf):
            interp.visit(tree)

        self.assertEqual(interp._last_execution_backend, "vm")
        self.assertIn("42", buf.getvalue())

    def test_vm_strict_rejects_unsupported_construct(self) -> None:
        source = "vigil { silence; } confess err { silence; } amen"
        tree = self._parse(source)
        interp = logos_lang.LogosInterpreter(execution_engine="vm-strict")

        with self.assertRaises(logos_lang.LogosError):
            interp.visit(tree)

    def test_static_type_elision_skips_proven_global_checks(self) -> None:
        source = "inscribe age: HolyInt = 1; amend age = age + 1; proclaim age;"
        tree = self._parse(source)
        interp = logos_lang.LogosInterpreter(execution_engine="visitor", enable_static_type_elision=True)

        calls: list[str] = []
        original = interp._enforce_value_type

        def tracking_enforce(value, type_name, context):
            calls.append(context)
            return original(value, type_name, context)

        interp._enforce_value_type = tracking_enforce  # type: ignore[method-assign]
        interp.visit(tree)

        self.assertEqual(interp._elided_declared_types.get("age"), "HolyInt")
        self.assertNotIn("age", calls)

    def test_static_type_elision_preserves_incompatible_runtime_guard(self) -> None:
        source = "inscribe age: HolyInt = 1; amend age = transfigure 1.25 into HolyFloat;"
        tree = self._parse(source)
        interp = logos_lang.LogosInterpreter(execution_engine="visitor", enable_static_type_elision=True)

        with self.assertRaises(logos_lang.LogosError):
            interp.visit(tree)


if __name__ == "__main__":
    unittest.main(verbosity=2)
