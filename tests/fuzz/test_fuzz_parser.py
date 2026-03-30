import unittest

import pytest
from lark import Lark
from lark.exceptions import UnexpectedInput

# IMPORT FROM NEW PACKAGE
import logos_lang

hypothesis = pytest.importorskip("hypothesis")
strategies = hypothesis.strategies
settings = hypothesis.settings
HealthCheck = hypothesis.HealthCheck

IDENTIFIERS = strategies.sampled_from(["a", "b", "c", "age", "n", "tmp"])


def _number_literals():
    ints = strategies.integers(min_value=0, max_value=999).map(str)
    floats = strategies.tuples(
        strategies.integers(min_value=0, max_value=99),
        strategies.integers(min_value=0, max_value=99),
    ).map(lambda t: f"{t[0]}.{t[1]}")
    return strategies.one_of(ints, floats)


def _expr_strategy():
    base = strategies.one_of(
        _number_literals(),
        strategies.sampled_from(['"pilgrim"', '"beacon"', '"amen"']),
        strategies.sampled_from(["Verily", "Nay"]),
        IDENTIFIERS,
    )

    return strategies.recursive(
        base,
        lambda child: strategies.one_of(
            strategies.tuples(
                child,
                strategies.sampled_from(["+", "-", "*", "/", "is", "<", ">", "<=", ">="]),
                child,
            ).map(lambda t: f"({t[0]} {t[1]} {t[2]})"),
            child.map(lambda e: f"transfigure {e} into HolyFloat"),
            child.map(lambda e: f"-({e})"),
            child.map(lambda e: f"[{e}]"),
        ),
        max_leaves=20,
    )


def _statement_strategy():
    exprs = _expr_strategy()
    return strategies.one_of(
        strategies.tuples(IDENTIFIERS, exprs).map(lambda t: f"inscribe {t[0]} = {t[1]};"),
        strategies.tuples(IDENTIFIERS, exprs).map(lambda t: f"amend {t[0]} = {t[1]};"),
        exprs.map(lambda e: f"proclaim {e};"),
        exprs.map(lambda e: f"{e};"),
        strategies.just("silence;"),
    )


def _program_strategy():
    return strategies.lists(_statement_strategy(), min_size=1, max_size=24).map("\n".join)


class FuzzTests(unittest.TestCase):
    @settings(
        max_examples=120,
        deadline=None,
        suppress_health_check=[
            HealthCheck.too_slow,
        ],
    )
    @hypothesis.given(_program_strategy())
    def test_grammar_aware_fuzz_interpreter_stability(self, source: str) -> None:
        parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")
        interp = logos_lang.LogosInterpreter(execution_engine="vm-hybrid")

        try:
            tree = parser.parse(source)
            interp.visit(tree)
        except (logos_lang.LogosError, logos_lang.SecurityError):
            return
        except Exception as e:
            self.fail(f"Unhandled native exception leaked from interpreter: {type(e).__name__}: {e}")

    @hypothesis.given(strategies.text())
    def test_fuzz_interpreter_stability(self, trash_text: str) -> None:
        try:
            # Use Library Interpreter
            interp = logos_lang.LogosInterpreter()
            # Use Library Grammar
            parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")
            tree = parser.parse(trash_text)
            interp.visit(tree)
        except logos_lang.LogosError:
            # Expected failure path for invalid programs.
            return
        except UnexpectedInput:
            # Parser-level rejection is expected for random text.
            return
        except Exception as e:
            self.fail(f"Interpreter crashed on input: {e}")


if __name__ == "__main__":
    unittest.main(verbosity=2)
