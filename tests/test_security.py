import builtins
import tempfile
import unittest
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path

from lark import Lark

import logos_lang
from tests.canon_runner import _execute_fixture


class SecurityTests(unittest.TestCase):
    def test_sandbox_escape_is_prevented(self) -> None:
        result = _execute_fixture("security/reflection_attack.lg")
        self.assertNotIn("HERESY", result.stdout)
        if result.stdout:
            self.assertIn("Access denied", result.stdout)
        else:
            self.assertIsNotNone(result.error)
            err_msg = str(result.error).lower()
            self.assertTrue(
                any(k in err_msg for k in ("blocked", "forbidden", "security violation"))
            )

    def test_path_traversal_blocked(self) -> None:
        result = _execute_fixture("security/path_traversal_blocked.lg")
        self.assertIsNotNone(result.error)
        self.assertIsInstance(result.error, logos_lang.SecurityError)
        self.assertIn("Path traversal blocked", str(result.error))

    def test_private_attribute_blocked(self) -> None:
        result = _execute_fixture("security/private_attr_block.lg")
        self.assertIsNone(result.error)
        self.assertIn("Denied", result.stdout)

    def test_symlink_escape_blocked_with_realpath_enforcement(self) -> None:
        with tempfile.TemporaryDirectory() as base, tempfile.TemporaryDirectory() as outside:
            secret = Path(outside) / "secret.txt"
            secret.write_text("forbidden", encoding="utf-8")

            link = Path(base) / "portal"
            try:
                link.symlink_to(Path(outside), target_is_directory=True)
            except (OSError, NotImplementedError):
                self.skipTest("Symlink creation is not permitted on this host")

            source = 'proclaim __sys_open("portal/secret.txt", 0);'
            parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")
            interp = logos_lang.LogosInterpreter(base_path=base)

            with self.assertRaises(logos_lang.SecurityError) as ctx:
                interp.visit(parser.parse(source))

            self.assertIn("Path traversal blocked", str(ctx.exception))

    def test_poisoned_host_environment_cannot_escape_interpreter(self) -> None:
        parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")
        source = "\n".join(
            [
                "vigil {",
                '  proclaim open("anything");',
                "} confess err {",
                '  proclaim "Denied";',
                "} amen",
            ]
        )

        original_open = builtins.open
        builtins.open = lambda *args, **kwargs: (_ for _ in ()).throw(RuntimeError("poisoned"))
        try:
            interp = logos_lang.LogosInterpreter()
            buf = StringIO()
            with redirect_stdout(buf):
                interp.visit(parser.parse(source))
            self.assertIn("Denied", buf.getvalue())
            self.assertNotIn("poisoned", buf.getvalue())
        finally:
            builtins.open = original_open


if __name__ == "__main__":
    unittest.main(verbosity=2)