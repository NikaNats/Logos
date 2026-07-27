from __future__ import annotations

import unittest
from lark import Lark

import logos_lang


class TypeEnforcementDogmaTests(unittest.TestCase):
    def setUp(self) -> None:
        self.parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")

    def _run(self, source: str) -> logos_lang.LogosInterpreter:
        interp = logos_lang.LogosInterpreter(execution_engine="visitor")
        tree = self.parser.parse(source)
        interp.visit(tree)
        return interp

    def test_function_param_type_enforcement(self) -> None:
        src = (
            'mystery id(x: HolyInt) -> HolyInt { offer x; } amen\n'
            'mystery main() { id("not an int"); } amen'
        )
        interp = logos_lang.LogosInterpreter(execution_engine="visitor")
        tree = self.parser.parse(src)
        interp.visit(tree)
        main_func = interp.scope.get("main")
        with self.assertRaises(logos_lang.LogosError) as ctx:
            interp._invoke_user_function(main_func, [])
        self.assertIn("Type mismatch", str(ctx.exception))

    def test_function_return_type_enforcement(self) -> None:
        src = (
            'mystery bad() -> HolyInt { offer "string"; } amen\n'
            'mystery main() { bad(); } amen'
        )
        interp = logos_lang.LogosInterpreter(execution_engine="visitor")
        tree = self.parser.parse(src)
        interp.visit(tree)
        main_func = interp.scope.get("main")
        with self.assertRaises(logos_lang.LogosError) as ctx:
            interp._invoke_user_function(main_func, [])
        self.assertIn("Type mismatch", str(ctx.exception))

    def test_binary_operator_type_enforcement(self) -> None:
        # String multiplication (string * int)
        with self.assertRaises(logos_lang.LogosError):
            self._run('proclaim "a" * 3;')

        # String subtraction
        with self.assertRaises(logos_lang.LogosError):
            self._run('proclaim "a" - 1;')

    def test_discern_non_boolean_condition_rejected(self) -> None:
        with self.assertRaises(logos_lang.LogosError):
            self._run('discern (1) { proclaim "yes"; } otherwise { proclaim "no"; } amen')

    def test_chant_non_boolean_condition_rejected(self) -> None:
        with self.assertRaises(logos_lang.LogosError):
            self._run("chant 1 { silence; } amen")

    def test_wrong_icon_type_assignment_rejected(self) -> None:
        src = (
            "icon Disciple { name: Text; age: HolyInt; } amen\n"
            "icon Saint { name: Text; miracles: HolyInt; } amen\n"
            'inscribe d = write Disciple { name = "Peter", age = 30 };\n'
            "inscribe s: Saint = d;"
        )
        with self.assertRaises(logos_lang.LogosError) as ctx:
            self._run(src)
        self.assertIn("Type mismatch", str(ctx.exception))

    def test_missing_icon_field_rejected(self) -> None:
        src = (
            "icon Monk { name: Text; rank: Text; } amen\n"
            'inscribe m = write Monk { name = "Paisios" };'
        )
        with self.assertRaises(logos_lang.LogosError) as ctx:
            self._run(src)
        self.assertIn("Missing field", str(ctx.exception))

    def test_unknown_type_name_declaration_rejected(self) -> None:
        with self.assertRaises(logos_lang.LogosError) as ctx:
            self._run("inscribe x: UnknownType = 5;")
        self.assertIn("Unknown type", str(ctx.exception))

    def test_unknown_type_name_transfigure_rejected(self) -> None:
        with self.assertRaises(logos_lang.LogosError) as ctx:
            self._run("proclaim transfigure 5 into UnknownType;")
        self.assertIn("Unknown transfigure target type", str(ctx.exception))


if __name__ == "__main__":
    unittest.main(verbosity=2)