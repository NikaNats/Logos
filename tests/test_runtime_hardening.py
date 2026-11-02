"""Regression tests for the runtime audit fixes (engine parity, elision soundness,
modules, closed icons, equality, sandbox containment, stdlib I/O, diagnostics)."""

from __future__ import annotations

import io
import os
import subprocess
import sys
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

    def test_import_outside_program_root_blocked_despite_workspace_markers(self) -> None:
        (self.base / "pyproject.toml").write_text("", encoding="utf-8")
        program = self.base / "program"
        program.mkdir()
        self.write("sibling.lg", "inscribe secret = 1;\n")
        with self.assertRaises(logos_lang.SecurityError):
            run('tradition "../sibling.lg";\n', base_path=str(program))

    def test_bundled_canon_and_granted_roots_are_importable(self) -> None:
        program = self.base / "program"
        program.mkdir()
        self.write("shared.lg", "inscribe shared = 5;\n")
        numeri = (ROOT / "lib" / "numeri.lg").as_posix()
        security = logos_lang.SecurityContext.strict()
        security.import_roots = [str(self.base)]
        interp = logos_lang.LogosInterpreter(base_path=str(program), security=security)
        _, out = run(
            f'tradition "{numeri}";\ntradition "../shared.lg";\nproclaim abs(0 - shared);\n',
            base_path=str(program),
            interp=interp,
        )
        self.assertEqual(proclaimed(out), ["5"])


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

    def test_nominal_tag_and_host_objects_are_immutable(self) -> None:
        for src in (
            'icon Monk { name: Text; } amen\ninscribe m = write Monk { name = "P" };\n'
            'amend m.__icon__ = "Saint";\n',
            "inscribe f = measure;\namend f.pwned = 1;\n",
        ):
            with self.subTest(src=src.splitlines()[-1]):
                with self.assertRaises(logos_lang.LogosError) as ctx:
                    run(src)
                self.assertIn("Attribute mutation forbidden", str(ctx.exception))


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


class SandboxTests(unittest.TestCase):
    def test_vigil_cannot_catch_security_errors(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            src = 'vigil { __sys_open("../../escape.txt", 0); } confess e { proclaim "caught"; } amen\n'
            with self.assertRaises(logos_lang.SecurityError):
                run(src, base_path=td)

    def test_vigil_still_catches_ordinary_errors(self) -> None:
        _, out = run('vigil { inscribe x = 1 / 0; } confess e { proclaim "caught"; } amen\n')
        self.assertEqual(proclaimed(out), ["caught"])

    def test_depart_halts_interpreter_not_host(self) -> None:
        for src in ("__sys_exit(3);\n", 'vigil { __sys_exit(3); } confess e { proclaim "no"; } amen\n'):
            with self.subTest(src=src):
                with self.assertRaises(logos_lang.LogosExit) as ctx:
                    run(src)
                self.assertEqual(ctx.exception.code, 3)

    def test_cli_maps_depart_to_exit_code(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            script = Path(td) / "bye.lg"
            script.write_text('proclaim "bye";\n__sys_exit(3);\n', encoding="utf-8")
            result = subprocess.run(
                [sys.executable, str(ROOT / "logos.py"), str(script)],
                capture_output=True, text=True, encoding="utf-8", cwd=ROOT,
            )
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)


class StdlibScrollTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.stdlib = logos_lang.StdLib(self._tmp.name)
        self.addCleanup(self.stdlib.close_all)

    def test_invalid_mode_is_an_error_not_a_silent_read(self) -> None:
        for mode in (7, "w"):
            with self.subTest(mode=mode):
                with self.assertRaises(logos_lang.LogosError) as ctx:
                    self.stdlib._open("data.txt", mode)
                self.assertIn("Invalid scroll mode", str(ctx.exception))

    def test_writing_source_or_native_files_blocked(self) -> None:
        for name in ("evil.py", "script.lg", "hijack.dll"):
            with self.subTest(name=name):
                with self.assertRaises(logos_lang.SecurityError):
                    self.stdlib._open(name, 1)

    def test_protected_suffix_tricks_blocked(self) -> None:
        tricks = ["EVIL.PY", "Script.Lg", "libx.so.6", "libx.so.1.2", "mod.wasm", "evil.py.txt.py"]
        if os.name == "nt":
            # Windows silently creates `evil.py` for these, and `a.txt:s` is an NTFS stream.
            tricks += ["evil.py.", "evil.py ", "evil.py. . ", "notes.txt:hidden.py", "notes.txt:x"]
        for name in tricks:
            with self.subTest(name=name):
                with self.assertRaises(logos_lang.SecurityError):
                    self.stdlib._open(name, 2)

    def test_data_files_with_dotted_names_still_writable(self) -> None:
        for name in ("data.v1.txt", "report.2026.csv", "notes.py.txt", "archive.so.backup"):
            with self.subTest(name=name):
                fd = self.stdlib._open(name, 1)
                self.assertGreater(fd, 0)
                self.stdlib._close(fd)

    @unittest.skipUnless(os.name == "nt", "Windows filename normalization")
    def test_trailing_dot_really_creates_source_file_on_windows(self) -> None:
        # Documents why the trailing-dot rule exists: the OS strips it on create.
        target = Path(self._tmp.name) / "probe.py."
        target.write_text("x", encoding="utf-8")
        self.assertTrue((Path(self._tmp.name) / "probe.py").exists())

    def test_open_scroll_limit_and_close_all(self) -> None:
        fds = [self.stdlib._open(f"f{i}.txt", 1) for i in range(logos_lang.StdLib.MAX_OPEN_SCROLLS)]
        self.assertNotIn(0, fds)
        with self.assertRaises(logos_lang.LogosError) as ctx:
            self.stdlib._open("one_too_many.txt", 1)
        self.assertIn("Too many open scrolls", str(ctx.exception))
        handles = list(self.stdlib._fds.values())
        self.stdlib.close_all()
        self.assertTrue(all(h.closed for h in handles))

    def test_unopenable_scroll_still_returns_zero(self) -> None:
        self.assertEqual(self.stdlib._open("missing_dir/x.txt", 0), 0)

    def test_interpreter_close_releases_scrolls(self) -> None:
        with logos_lang.LogosInterpreter(base_path=self._tmp.name) as interp:
            run('inscribe fd = __sys_open("log.txt", 1);\n', interp=interp)
            handles = list(interp.stdlib._fds.values())
        self.assertTrue(handles and all(h.closed for h in handles))


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
