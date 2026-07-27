from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from lark import Lark

import logos_lang


class SecurityContainmentDogmaTests(unittest.TestCase):
    def setUp(self) -> None:
        self.parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")

    def test_tradition_import_path_traversal_blocked(self) -> None:
        with tempfile.TemporaryDirectory() as base_dir, tempfile.TemporaryDirectory() as outside_dir:
            outside_file = Path(outside_dir) / "secret.lg"
            outside_file.write_text('inscribe secret = "leaked";', encoding="utf-8")

            interp = logos_lang.LogosInterpreter(base_path=base_dir)
            # Relative path attempting to step outside workspace root
            rel_escape = "../" + outside_file.name

            tree = self.parser.parse(f'tradition "{rel_escape}";')
            with self.assertRaises(logos_lang.SecurityError) as ctx:
                interp.visit(tree)

            self.assertIn("Tradition path traversal blocked", str(ctx.exception))

    def test_sys_open_path_traversal_raises_security_error(self) -> None:
        with tempfile.TemporaryDirectory() as base_dir:
            interp = logos_lang.LogosInterpreter(base_path=base_dir)
            tree = self.parser.parse('proclaim __sys_open("../etc/passwd", 0);')

            with self.assertRaises(logos_lang.SecurityError) as ctx:
                interp.visit(tree)

            self.assertIn("Path traversal blocked", str(ctx.exception))

    def test_missing_tradition_does_not_reveal_absolute_paths(self) -> None:
        with tempfile.TemporaryDirectory() as base_dir:
            interp = logos_lang.LogosInterpreter(base_path=base_dir)
            rel_missing = "non_existent_module_999.lg"
            tree = self.parser.parse(f'tradition "{rel_missing}";')

            with self.assertRaises(logos_lang.LogosError) as ctx:
                interp.visit(tree)

            msg = str(ctx.exception)
            self.assertIn(rel_missing, msg)
            self.assertNotIn(base_dir, msg)  # Must not leak host absolute base path


if __name__ == "__main__":
    unittest.main(verbosity=2)