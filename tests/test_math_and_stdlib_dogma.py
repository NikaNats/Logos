from __future__ import annotations

import io
import unittest
from contextlib import redirect_stdout
from pathlib import Path

from lark import Lark

import logos_lang

ROOT = Path(__file__).resolve().parents[1]


class MathAndStdLibDogmaTests(unittest.TestCase):
    def setUp(self) -> None:
        self.parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")

    def test_modulo_operator_evaluation(self) -> None:
        interp = logos_lang.LogosInterpreter(execution_engine="visitor")
        buf = io.StringIO()
        with redirect_stdout(buf):
            interp.visit(
                self.parser.parse(
                    "proclaim 5 % 2;\n"
                    "proclaim 10 % 3;\n"
                    "proclaim 4 % 2;\n"
                )
            )
        out = buf.getvalue()
        self.assertIn("1", out)
        self.assertIn("0", out)

    def test_is_even_correctness(self) -> None:
        numeri_path = ROOT / "lib" / "numeri.lg"
        interp = logos_lang.LogosInterpreter(base_path=str(ROOT / "lib"))
        interp._current_file = str(numeri_path)

        buf = io.StringIO()
        with redirect_stdout(buf):
            interp.visit(
                self.parser.parse(
                    f'tradition "{numeri_path.as_posix()}";\n'
                    "proclaim is_even(4);\n"
                    "proclaim is_even(5);\n"
                )
            )
        out = buf.getvalue()
        self.assertIn("Verily", out)
        self.assertIn("Nay", out)

    def test_canon_iterative_pow_and_chant(self) -> None:
        canon_path = ROOT / "lib" / "canon.lg"
        interp = logos_lang.LogosInterpreter(base_path=str(ROOT / "lib"))
        interp._current_file = str(canon_path)

        buf = io.StringIO()
        with redirect_stdout(buf):
            interp.visit(
                self.parser.parse(
                    f'tradition "{canon_path.as_posix()}";\n'
                    "proclaim pow(2, 10);\n"
                    'proclaim chant("Amen!", 3);\n'
                )
            )
        out = buf.getvalue()
        self.assertIn("1024", out)
        self.assertIn("Amen!Amen!Amen!", out)


if __name__ == "__main__":
    unittest.main(verbosity=2)