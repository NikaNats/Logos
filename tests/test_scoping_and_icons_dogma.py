from __future__ import annotations

import io
import unittest
from contextlib import redirect_stdout

from lark import Lark

import logos_lang


class ScopingAndIconsDogmaTests(unittest.TestCase):
    def setUp(self) -> None:
        self.parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")

    def test_block_scope_variable_isolation(self) -> None:
        src = (
            "inscribe x = 1;\n"
            "discern (Verily) {\n"
            "    inscribe x = 2;\n"
            "    proclaim x;\n"
            "} otherwise { silence; } amen\n"
            "proclaim x;\n"
        )
        interp = logos_lang.LogosInterpreter(execution_engine="visitor")
        buf = io.StringIO()
        with redirect_stdout(buf):
            interp.visit(self.parser.parse(src))

        out = buf.getvalue()
        # First proclaim inside block outputs 2, second proclaim outside block outputs 1
        lines = [line.strip() for line in out.splitlines() if line.strip()]
        self.assertEqual(lines, ["☩ 2", "☩ 1"])

    def test_nested_function_definition_does_not_leak_globally(self) -> None:
        src = (
            "mystery outer() {\n"
            "    mystery inner() { proclaim \"inner\"; } amen\n"
            "    inner();\n"
            "} amen\n"
            "outer();\n"
            "inner();\n"  # Must fail because inner is scoped to outer()
        )
        interp = logos_lang.LogosInterpreter(execution_engine="visitor")
        tree = self.parser.parse(src)
        with self.assertRaises(logos_lang.LogosError) as ctx:
            interp.visit(tree)
        self.assertIn("Unknown spirit 'inner'", str(ctx.exception))

    def test_missing_icon_attribute_access_raises_error(self) -> None:
        src = (
            "icon Monk { name: Text; rank: Text; } amen\n"
            "inscribe m = write Monk { name = \"Paisios\", rank = \"Novice\" };\n"
            "proclaim m.age;\n"  # Missing attribute 'age'
        )
        interp = logos_lang.LogosInterpreter(execution_engine="visitor")
        tree = self.parser.parse(src)
        with self.assertRaises(logos_lang.LogosError) as ctx:
            interp.visit(tree)
        self.assertIn("has no attribute 'age'", str(ctx.exception))

    def test_undeclared_icon_field_construction_rejected(self) -> None:
        src = (
            "icon Monk { name: Text; } amen\n"
            "inscribe m = write Monk { name = \"Paisios\", extra = \"unneeded\" };\n"
        )
        interp = logos_lang.LogosInterpreter(execution_engine="visitor")
        tree = self.parser.parse(src)
        with self.assertRaises(logos_lang.LogosError) as ctx:
            interp.visit(tree)
        self.assertIn("Undeclared field 'extra'", str(ctx.exception))


if __name__ == "__main__":
    unittest.main(verbosity=2)