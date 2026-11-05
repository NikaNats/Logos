from __future__ import annotations

import unittest

import logos_lang

# Every dogma must hold on both engines; vm-hybrid runs lowered programs on the bytecode VM.
ENGINES = ("visitor", "vm-hybrid")


class TypeEnforcementDogmaTests(unittest.TestCase):
    def setUp(self) -> None:
        self.parser = logos_lang.create_parser()

    def _expect_error(self, source: str, fragment: str = "") -> None:
        for engine in ENGINES:
            with self.subTest(engine=engine):
                interp = logos_lang.LogosInterpreter(execution_engine=engine)
                with self.assertRaises(logos_lang.LogosError) as ctx:
                    interp.visit(self.parser.parse(source))
                    main_func = interp.scope.globals.get("main")
                    if isinstance(main_func, logos_lang.UserFunction):
                        interp._invoke_user_function(main_func, [])
                self.assertIn(fragment, str(ctx.exception))

    def test_function_param_type_enforcement(self) -> None:
        src = (
            'mystery id(x: HolyInt) -> HolyInt { offer x; } amen\n'
            'mystery main() { id("not an int"); } amen'
        )
        self._expect_error(src, "Type mismatch")

    def test_function_return_type_enforcement(self) -> None:
        src = (
            'mystery bad() -> HolyInt { offer "string"; } amen\n'
            'mystery main() { bad(); } amen'
        )
        self._expect_error(src, "Type mismatch")

    def test_binary_operator_type_enforcement(self) -> None:
        # String multiplication (string * int)
        self._expect_error('proclaim "a" * 3;')

        # String subtraction
        self._expect_error('proclaim "a" - 1;')

    def test_discern_non_boolean_condition_rejected(self) -> None:
        self._expect_error('discern (1) { proclaim "yes"; } otherwise { proclaim "no"; } amen')

    def test_chant_non_boolean_condition_rejected(self) -> None:
        self._expect_error("chant 1 { silence; } amen")

    def test_wrong_icon_type_assignment_rejected(self) -> None:
        src = (
            "icon Disciple { name: Text; age: HolyInt; } amen\n"
            "icon Saint { name: Text; miracles: HolyInt; } amen\n"
            'inscribe d = write Disciple { name = "Peter", age = 30 };\n'
            "inscribe s: Saint = d;"
        )
        self._expect_error(src, "Type mismatch")

    def test_missing_icon_field_rejected(self) -> None:
        src = (
            "icon Monk { name: Text; rank: Text; } amen\n"
            'inscribe m = write Monk { name = "Paisios" };'
        )
        self._expect_error(src, "Missing field")

    def test_unknown_type_name_declaration_rejected(self) -> None:
        self._expect_error("inscribe x: UnknownType = 5;", "Unknown type")

    def test_unknown_type_name_transfigure_rejected(self) -> None:
        self._expect_error("proclaim transfigure 5 into UnknownType;", "Unknown transfigure target type")


if __name__ == "__main__":
    unittest.main(verbosity=2)