from __future__ import annotations

import io
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

from lark import Lark

import logos_lang


class ModuleSystemDogmaTests(unittest.TestCase):
    def setUp(self) -> None:
        self.parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")

    def test_stateful_module_state_preserved_on_alias_import(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            temp_dir = Path(td)
            counter_mod = temp_dir / "counter.lg"
            counter_mod.write_text(
                "inscribe count = 0;\n"
                "mystery inc() {\n"
                "    amend count = count + 1;\n"
                "    offer count;\n"
                "} amen\n",
                encoding="utf-8",
            )

            main_script = temp_dir / "main.lg"
            main_script.write_text(
                'tradition "counter.lg" as Counter;\n'
                "inscribe inc_fn = Counter.inc;\n"
                "proclaim inc_fn();\n"
                "proclaim inc_fn();\n",
                encoding="utf-8",
            )

            interp = logos_lang.LogosInterpreter(base_path=str(temp_dir))
            interp._current_file = str(main_script)
            buf = io.StringIO()
            with redirect_stdout(buf):
                interp.visit(self.parser.parse(main_script.read_text(encoding="utf-8")))

            out = buf.getvalue()
            self.assertIn("1", out)
            self.assertIn("2", out)

    def test_direct_import_executes_in_module_context(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            temp_dir = Path(td)
            counter_mod = temp_dir / "counter_direct.lg"
            counter_mod.write_text(
                "inscribe val = 100;\n"
                "mystery get_val() {\n"
                "    offer val;\n"
                "} amen\n",
                encoding="utf-8",
            )

            main_script = temp_dir / "main_direct.lg"
            main_script.write_text(
                'tradition "counter_direct.lg";\n'
                "inscribe val = 999;\n"  # Local variable shadowing
                "proclaim get_val();\n",  # Must still return 100 from module context
                encoding="utf-8",
            )

            interp = logos_lang.LogosInterpreter(base_path=str(temp_dir))
            interp._current_file = str(main_script)
            buf = io.StringIO()
            with redirect_stdout(buf):
                interp.visit(self.parser.parse(main_script.read_text(encoding="utf-8")))

            self.assertIn("100", buf.getvalue())

    def test_cyclic_import_warning_redirected_to_stderr(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            temp_dir = Path(td)
            mod_a = temp_dir / "cycle_a.lg"
            mod_b = temp_dir / "cycle_b.lg"

            mod_a.write_text('tradition "cycle_b.lg";\nproclaim "A";\n', encoding="utf-8")
            mod_b.write_text('tradition "cycle_a.lg";\nproclaim "B";\n', encoding="utf-8")

            interp = logos_lang.LogosInterpreter(base_path=str(temp_dir))
            interp._current_file = str(mod_a)

            stdout_buf = io.StringIO()
            stderr_buf = io.StringIO()

            with redirect_stdout(stdout_buf), redirect_stderr(stderr_buf):
                interp.visit(self.parser.parse(mod_a.read_text(encoding="utf-8")))

            self.assertNotIn("Cycle detected", stdout_buf.getvalue())
            self.assertIn("Cycle detected", stderr_buf.getvalue())


if __name__ == "__main__":
    unittest.main(verbosity=2)