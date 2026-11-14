"""Regression tests for the runtime audit fixes (engine parity, elision soundness,
modules, closed icons, equality, diagnostics)."""

from __future__ import annotations

import io
import os
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest import mock

import logos_lang

ROOT = Path(__file__).resolve().parents[1]
PARSER = logos_lang.create_parser()


def run(
    source: str,
    engine: str = "visitor",
    *,
    base_path: str | None = None,
    elision: bool = True,
    interp: logos_lang.LogosInterpreter | None = None,
) -> tuple[logos_lang.LogosInterpreter, str]:
    interp = interp or logos_lang.LogosInterpreter(
        base_path=base_path, execution_engine=engine, enable_static_type_elision=elision
    )
    if base_path:
        interp._current_file = os.path.join(base_path, "main.lg")
    buf = io.StringIO()
    with redirect_stdout(buf):
        interp.visit(PARSER.parse(source))
    return interp, buf.getvalue()


def proclaimed(out: str) -> list[str]:
    return [line.split(" ", 1)[1] for line in out.splitlines() if line.strip()]


class EngineParityTests(unittest.TestCase):
    def test_vm_block_typed_declaration_is_block_local(self) -> None:
        src = (
            'discern (Verily) { inscribe y: Text = "inner"; } otherwise { silence; } amen\n'
            "inscribe y: HolyInt = 2;\n"
            "proclaim y;\n"
        )
        for engine in ("visitor", "vm-strict"):
            with self.subTest(engine=engine):
                _, out = run(src, engine)
                self.assertEqual(proclaimed(out), ["2"])

    def test_vm_restores_frames_after_error_mid_block(self) -> None:
        interp = logos_lang.LogosInterpreter(execution_engine="vm-strict")
        with self.assertRaises(logos_lang.LogosError):
            run("discern (Verily) { inscribe z = 1 / 0; } otherwise { silence; } amen", interp=interp)
        self.assertEqual(interp.scope.stack, [])
        self.assertEqual(interp._type_stack, [])


class StaticElisionSoundnessTests(unittest.TestCase):
    GIVE_TEXT = 'mystery give() { offer "text"; } amen\n'

    def test_block_local_shadow_does_not_reenable_global_elision(self) -> None:
        src = self.GIVE_TEXT + (
            "inscribe x: HolyInt = 1;\n"
            "amend x = give();\n"
            "discern (Verily) { inscribe x: HolyInt = 2; } otherwise { silence; } amen\n"
        )
        with self.assertRaises(logos_lang.LogosError) as ctx:
            run(src)
        self.assertIn("Type mismatch", str(ctx.exception))

    def test_untyped_reinscribe_of_typed_global_is_checked(self) -> None:
        src = self.GIVE_TEXT + "inscribe x: HolyInt = 1;\ninscribe x = give();\n"
        with self.assertRaises(logos_lang.LogosError) as ctx:
            run(src)
        self.assertIn("Type mismatch", str(ctx.exception))

    def test_amend_of_block_local_does_not_touch_global_plan(self) -> None:
        tree = PARSER.parse(
            "inscribe x: HolyInt = 1;\n"
            'discern (Verily) { inscribe x = "s"; amend x = "t"; } otherwise { silence; } amen\n'
        )
        plan = logos_lang.StaticTypeAnalyzer().analyze(tree)
        self.assertEqual(plan.bindings, {"x": "HolyInt"})


class ModuleTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.base = Path(self._tmp.name)

    def write(self, name: str, text: str) -> None:
        (self.base / name).write_text(text, encoding="utf-8")

    def test_vm_module_function_call_syncs_alias_exports(self) -> None:
        self.write(
            "counter.lg",
            "inscribe count = 0;\nmystery inc() { amend count = count + 1; offer count; } amen\n",
        )
        interp = logos_lang.LogosInterpreter(base_path=str(self.base))
        run('tradition "counter.lg";\ntradition "counter.lg" as C;\n', base_path=str(self.base), interp=interp)
        interp.execution_engine = "vm-strict"
        run("inc();\ninc();\n", interp=interp)
        interp.execution_engine = "visitor"
        _, out = run("proclaim C.count;\n", interp=interp)
        self.assertEqual(proclaimed(out), ["2"])

    def test_cyclic_import_receives_exports_once_loaded(self) -> None:
        self.write("a.lg", 'tradition "b.lg";\ninscribe a_val = 7;\n')
        self.write("b.lg", 'tradition "a.lg" as A;\nmystery peek() { offer A.a_val; } amen\n')
        buf = io.StringIO()
        with mock.patch("sys.stderr", buf):
            _, out = run(
                'tradition "a.lg";\ntradition "b.lg";\nproclaim peek();\n', base_path=str(self.base)
            )
        self.assertEqual(proclaimed(out), ["7"])
        self.assertIn("Cycle detected", buf.getvalue())



class IconClosedRecordTests(unittest.TestCase):
    def test_empty_icon_rejects_extra_fields(self) -> None:
        with self.assertRaises(logos_lang.LogosError) as ctx:
            run("icon Empty { } amen\ninscribe e = write Empty { extra = 1 };\n")
        self.assertIn("Undeclared field 'extra'", str(ctx.exception))

    def test_amend_undeclared_icon_field_rejected(self) -> None:
        src = 'icon Monk { name: Text; } amen\ninscribe m = write Monk { name = "P" };\n'
        with self.assertRaises(logos_lang.LogosError) as ctx:
            run(src + "amend m.rank = 1;\n")
        self.assertIn("no field 'rank'", str(ctx.exception))
        _, out = run(src + 'amend m.name = "Q";\nproclaim m.name;\n')
        self.assertEqual(proclaimed(out), ["Q"])



class EqualityTests(unittest.TestCase):
    def test_is_never_equates_bool_with_numbers(self) -> None:
        src = (
            "proclaim 1 is Verily;\nproclaim 0 is Nay;\nproclaim 1 is not Verily;\n"
            "proclaim 1 is 1.0;\nproclaim [1] is [Verily];\nproclaim Verily is Verily;\n"
        )
        for engine in ("visitor", "vm-strict"):
            with self.subTest(engine=engine):
                _, out = run(src, engine)
                self.assertEqual(proclaimed(out), ["Nay", "Nay", "Verily", "Verily", "Nay", "Verily"])

    def test_contemplate_does_not_match_bool_pattern_for_int(self) -> None:
        _, out = run(
            'contemplate (1) { aspect Verily: proclaim "bool"; aspect _: proclaim "int"; } amen\n'
        )
        self.assertEqual(proclaimed(out), ["int"])


class DiagnosticsTests(unittest.TestCase):
    def test_runtime_errors_carry_source_location_on_both_engines(self) -> None:
        for engine in ("visitor", "vm-strict"):
            with self.subTest(engine=engine):
                with tempfile.TemporaryDirectory() as td:
                    with self.assertRaises(logos_lang.LogosError) as ctx:
                        run('inscribe a = 1;\nproclaim a + "x";\n', engine, base_path=td)
                err = ctx.exception
                self.assertEqual(err.line, 2)
                self.assertIsNotNone(err.column)
                self.assertTrue(str(err.source_file).endswith("main.lg"))
                self.assertTrue(err.describe("main.lg").startswith("main.lg:2:"))

    def test_output_failure_is_reported_not_swallowed(self) -> None:
        class BrokenIO(logos_lang.ConsoleIO):
            def emit(self, symbol: str, message: str) -> None:
                raise OSError("stdout closed")

        interp = logos_lang.LogosInterpreter(io_handler=BrokenIO())
        with mock.patch("logos_lang.interpreter._resolve_print", return_value=self._raise):
            with self.assertRaises(logos_lang.LogosError) as ctx:
                run('proclaim "x";\n', interp=interp)
        self.assertIn("Could not proclaim", str(ctx.exception))

    @staticmethod
    def _raise(*_args: object) -> None:
        raise OSError("print unavailable")


if __name__ == "__main__":
    unittest.main(verbosity=2)
