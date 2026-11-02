import io
import unittest
from contextlib import redirect_stdout

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


PARSER = logos_lang.create_parser()  # building the LALR tables is the expensive part
TYPES = strategies.sampled_from(["HolyInt", "HolyFloat", "Text", "Bool"])
PRELUDE = (
    'inscribe a = 1; inscribe b = 2.5; inscribe c = "c"; '
    "inscribe age = 3; inscribe n = 0; inscribe tmp = Verily;\n"
)


def _typed_literal(type_name: str):
    return {
        "HolyInt": strategies.integers(min_value=0, max_value=99).map(str),
        "HolyFloat": strategies.integers(min_value=0, max_value=99).map(lambda i: f"{i}.5"),
        "Text": strategies.sampled_from(['"pilgrim"', '"amen"']),
        "Bool": strategies.sampled_from(["Verily", "Nay"]),
    }[type_name]


def _scoped_program_strategy():
    """Programs mixing typed declarations, re-typed shadows, amends and nested `discern`
    blocks, i.e. the lexical scoping, type-stack and static-elision paths. Values are
    mostly well-typed so execution reaches that logic instead of failing immediately.
    Only VM-lowerable constructs are used."""
    exprs = _expr_strategy()
    typed_inscribe = TYPES.flatmap(
        lambda t: strategies.tuples(
            IDENTIFIERS, strategies.just(t), strategies.one_of(_typed_literal(t), exprs)
        )
    ).map(lambda t: f"inscribe {t[0]}: {t[1]} = {t[2]};")
    typed_amend = TYPES.flatmap(
        lambda t: strategies.tuples(IDENTIFIERS, _typed_literal(t))
    ).map(lambda t: f"amend {t[0]} = {t[1]};")
    flat = strategies.one_of(_statement_strategy(), typed_inscribe, typed_amend)

    def nest(children):
        body = strategies.lists(children, min_size=1, max_size=4).map(" ".join)
        condition = strategies.one_of(
            strategies.sampled_from(["Verily", "Nay"]),
            strategies.tuples(exprs, exprs).map(lambda t: f"{t[0]} < {t[1]}"),
        )
        return strategies.tuples(condition, body, body).map(
            lambda t: f"discern ({t[0]}) {{ {t[1]} }} otherwise {{ {t[2]} }} amen"
        )

    statements = strategies.recursive(flat, nest, max_leaves=12)
    # Declare every identifier first so programs get past name lookup into the
    # scoping/typing logic instead of failing on the first statement.
    return strategies.lists(statements, min_size=1, max_size=12).map(
        lambda body: PRELUDE + "\n".join(body)
    )


def _observe(source: str, engine: str, elision: bool) -> tuple[str, str | None]:
    """Run a program and return (stdout, error message): the comparison key across engines.

    Messages (not just types) must match: both engines share one implementation of the
    language semantics, so a differing message means they took different paths."""
    interp = logos_lang.LogosInterpreter(
        execution_engine=engine, enable_static_type_elision=elision
    )
    buf = io.StringIO()
    try:
        with redirect_stdout(buf):
            interp.visit(PARSER.parse(source))
    except logos_lang.LogosError as exc:
        return buf.getvalue(), f"{type(exc).__name__}: {exc}"
    return buf.getvalue(), None


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

    @settings(max_examples=200, deadline=None, suppress_health_check=[HealthCheck.too_slow])
    @hypothesis.given(strategies.one_of(_program_strategy(), _scoped_program_strategy()))
    # Known historical divergences, always replayed:
    # VM leaked a block-local typed declaration into the global type table.
    @hypothesis.example(
        'discern (Verily) { inscribe y: Text = "i"; } otherwise { silence; } amen\n'
        "inscribe y: HolyInt = 2;\nproclaim y;"
    )
    # A block-local shadow re-enabled global type-check elision (unsound).
    @hypothesis.example(
        'mystery give() { offer "t"; } amen\ninscribe x: HolyInt = 1;\namend x = give();\n'
        "discern (Verily) { inscribe x: HolyInt = 2; } otherwise { silence; } amen\nproclaim x;"
    )
    def test_engines_and_elision_are_unobservable(self, source: str) -> None:
        # Differential oracle: static type elision must never change behavior, and for any
        # program the compiler can lower, the bytecode VM must behave exactly like the
        # visitor (same output, same error message).
        try:
            tree = PARSER.parse(source)
        except UnexpectedInput:
            hypothesis.assume(False)
            return

        reference = _observe(source, "visitor", elision=True)
        self.assertEqual(_observe(source, "visitor", elision=False), reference, source)

        try:
            logos_lang.BytecodeCompiler().compile(tree)
        except logos_lang.BytecodeUnsupported:
            return
        self.assertEqual(_observe(source, "vm-strict", elision=True), reference, source)

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
