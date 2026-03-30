from __future__ import annotations

import unittest

from lark import Lark

import logos_lang


class SpectestConformanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls._parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")

    def _run(self, source: str) -> logos_lang.LogosInterpreter:
        interp = logos_lang.LogosInterpreter(execution_engine="visitor")
        tree = self._parser.parse(source)
        interp.visit(tree)
        return interp

    def test_operator_precedence_and_associativity_via_scope_state(self) -> None:
        interp = self._run(
            "\n".join(
                [
                    "inscribe a: HolyInt = 2 + 3 * 4;",
                    "inscribe b: HolyInt = (2 + 3) * 4;",
                    "inscribe c: HolyInt = 9 - 3 - 2;",
                    "inscribe d: HolyInt = transfigure (5 / 2) into HolyInt;",
                ]
            )
        )

        self.assertEqual(interp.scope.get("a"), 14)
        self.assertEqual(interp.scope.get("b"), 20)
        self.assertEqual(interp.scope.get("c"), 4)
        self.assertEqual(interp.scope.get("d"), 2)
        self.assertEqual(interp.scope.stack, [])

    def test_shadowing_and_frame_push_pop_rules(self) -> None:
        interp = self._run(
            "\n".join(
                [
                    "inscribe age: HolyInt = 40;",
                    "mystery elder(age: HolyInt) -> HolyInt {",
                    "  inscribe age: HolyInt = age + 2;",
                    "  offer age;",
                    "} amen",
                    "inscribe result: HolyInt = elder(age);",
                ]
            )
        )

        self.assertEqual(interp.scope.get("age"), 40)
        self.assertEqual(interp.scope.get("result"), 42)
        self.assertEqual(interp.scope.stack, [])

    def test_typecanon_coercion_matrix(self) -> None:
        atomic_types = ["HolyInt", "HolyFloat", "Text", "Bool"]

        for left in atomic_types:
            for right in atomic_types:
                with self.subTest(op="add", left=left, right=right):
                    actual = logos_lang.TypeCanon.resolve_binary_op("add", left, right)
                    if left in logos_lang.TypeCanon.NUMERIC and right in logos_lang.TypeCanon.NUMERIC:
                        expected = (
                            "HolyFloat"
                            if "HolyFloat" in (left, right) or "Float" in (left, right)
                            else "HolyInt"
                        )
                    elif left in logos_lang.TypeCanon.TEXT and right in logos_lang.TypeCanon.TEXT:
                        expected = "Text"
                    else:
                        expected = None
                    self.assertEqual(actual, expected)

                with self.subTest(op="sub", left=left, right=right):
                    actual = logos_lang.TypeCanon.resolve_binary_op("sub", left, right)
                    if left in logos_lang.TypeCanon.NUMERIC and right in logos_lang.TypeCanon.NUMERIC:
                        expected = (
                            "HolyFloat"
                            if "HolyFloat" in (left, right) or "Float" in (left, right)
                            else "HolyInt"
                        )
                    else:
                        expected = None
                    self.assertEqual(actual, expected)

                with self.subTest(op="eq", left=left, right=right):
                    self.assertEqual(logos_lang.TypeCanon.resolve_binary_op("eq", left, right), "Bool")

                with self.subTest(op="lt", left=left, right=right):
                    actual = logos_lang.TypeCanon.resolve_binary_op("lt", left, right)
                    expected = (
                        "Bool"
                        if left in logos_lang.TypeCanon.NUMERIC
                        and right in logos_lang.TypeCanon.NUMERIC
                        else None
                    )
                    self.assertEqual(actual, expected)

    def test_runtime_invalid_numeric_coercion_emits_logos_error(self) -> None:
        source = "\n".join(
            [
                'inscribe text: Text = "beacon";',
                "inscribe age: HolyInt = 3;",
                "inscribe broken = text - age;",
            ]
        )
        interp = logos_lang.LogosInterpreter(execution_engine="visitor")
        tree = self._parser.parse(source)

        with self.assertRaises(logos_lang.LogosError):
            interp.visit(tree)


if __name__ == "__main__":
    unittest.main(verbosity=2)
