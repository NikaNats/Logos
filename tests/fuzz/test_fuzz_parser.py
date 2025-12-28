import unittest

import pytest

import logos


hypothesis = pytest.importorskip("hypothesis")
strategies = hypothesis.strategies


class FuzzTests(unittest.TestCase):
    @hypothesis.given(strategies.text())
    def test_fuzz_interpreter_stability(self, trash_text: str) -> None:
        try:
            interp = logos.LogosInterpreter()
            parser = logos.Lark(logos.LOGOS_GRAMMAR, parser="lalr")
            tree = parser.parse(trash_text)
            interp.visit(tree)
        except logos.LogosError:
            # Expected failure path for invalid programs.
            return
        except Exception as e:
            # Allow Lark to raise its own UnexpectedInput, but fail on other internal errors.
            if "UnexpectedInput" not in type(e).__name__:
                self.fail(f"Interpreter crashed on input: {e}")


if __name__ == "__main__":  # pragma: no cover
    unittest.main(verbosity=2)
