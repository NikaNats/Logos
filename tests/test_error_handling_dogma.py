from __future__ import annotations

import io
import unittest
from contextlib import redirect_stdout
from pathlib import Path

from lark import Lark

import logos_lang

ROOT = Path(__file__).resolve().parents[1]


class ErrorHandlingDogmaTests(unittest.TestCase):
    def setUp(self) -> None:
        self.parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")

    def test_write_line_fails_on_invalid_descriptor(self) -> None:
        genesis_path = ROOT / "lib" / "genesis.lg"
        interp = logos_lang.LogosInterpreter(base_path=str(ROOT / "lib"))
        interp._current_file = str(genesis_path)

        buf = io.StringIO()
        with redirect_stdout(buf):
            interp.visit(
                self.parser.parse(
                    f'tradition "{genesis_path.as_posix()}";\n'
                    'proclaim write_line(999, "invalid_fd");\n'
                )
            )
        out = buf.getvalue()
        self.assertIn("Nay", out)

    def test_structured_logos_error_attributes(self) -> None:
        err = logos_lang.LogosError(
            message="Test error",
            category="TypeError",
            line=10,
            column=5,
            source_file="test.lg",
        )
        self.assertEqual(err.message, "Test error")
        self.assertEqual(err.category, "TypeError")
        self.assertEqual(err.line, 10)
        self.assertEqual(err.column, 5)
        self.assertEqual(err.source_file, "test.lg")

    def test_structured_security_error_attributes(self) -> None:
        err = logos_lang.SecurityError(message="Forbidden access")
        self.assertEqual(err.message, "Forbidden access")
        self.assertEqual(err.category, "SecurityError")
        self.assertIsInstance(err, logos_lang.LogosError)


if __name__ == "__main__":
    unittest.main(verbosity=2)