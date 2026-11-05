from __future__ import annotations

import io
import unittest
from contextlib import redirect_stdout

import logos_lang

# Every dogma must hold on both engines; vm-hybrid runs lowered programs on the bytecode VM.
ENGINES = ("visitor", "vm-hybrid")


class ScopingAndIconsDogmaTests(unittest.TestCase):
    def setUp(self) -> None:
        self.parser = logos_lang.create_parser()

    def _expect_error(self, src: str, fragment: str) -> None:
        for engine in ENGINES:
            with self.subTest(engine=engine):
                interp = logos_lang.LogosInterpreter(execution_engine=engine)
                with self.assertRaises(logos_lang.LogosError) as ctx:
                    interp.visit(self.parser.parse(src))
                self.assertIn(fragment, str(ctx.exception))

    def test_block_scope_variable_isolation(self) -> None:
        src = (
            "inscribe x = 1;\n"
            "discern (Verily) {\n"
            "    inscribe x = 2;\n"
            "    proclaim x;\n"
            "} otherwise { silence; } amen\n"
            "proclaim x;\n"
        )
        for engine in ENGINES:
            with self.subTest(engine=engine):
                interp = logos_lang.LogosInterpreter(execution_engine=engine)
                buf = io.StringIO()
                with redirect_stdout(buf):
                    interp.visit(self.parser.parse(src))

                # First proclaim inside block outputs 2, second outside outputs 1
                lines = [line.strip() for line in buf.getvalue().splitlines() if line.strip()]
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
        self._expect_error(src, "Unknown spirit 'inner'")

    def test_missing_icon_attribute_access_raises_error(self) -> None:
        src = (
            "icon Monk { name: Text; rank: Text; } amen\n"
            "inscribe m = write Monk { name = \"Paisios\", rank = \"Novice\" };\n"
            "proclaim m.age;\n"  # Missing attribute 'age'
        )
        self._expect_error(src, "has no attribute 'age'")

    def test_undeclared_icon_field_construction_rejected(self) -> None:
        src = (
            "icon Monk { name: Text; } amen\n"
            "inscribe m = write Monk { name = \"Paisios\", extra = \"unneeded\" };\n"
        )
        self._expect_error(src, "Undeclared field 'extra'")


if __name__ == "__main__":
    unittest.main(verbosity=2)