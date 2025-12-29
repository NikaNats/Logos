from __future__ import annotations
import io
import os
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from unittest.mock import patch

from lark import Lark

# We import the entrypoint script specifically to test it
import logos 
# We also import the lang package to inspect exceptions/classes
import logos_lang

class EntrypointCoverageTests(unittest.TestCase):
    def test_host_recursion_limit_is_wrapped(self) -> None:
        source = "\n".join(
            [
                "mystery f(n) {",
                "  discern(n is 0) { offer 0; } otherwise { offer f(n - 1) + 1; } amen",
                "} amen",
                "proclaim f(500);",
            ]
        )
        tree = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr").parse(source)

        orig_limit = sys.getrecursionlimit()
        orig_set = sys.setrecursionlimit
        try:
            # Keep the host limit low enough to trip before Logos' own depth guard.
            orig_set(120)

            # Prevent LogosInterpreter.__init__ from increasing the host recursion limit.
            def boom(_: int) -> None:
                raise Exception("blocked")

            sys.setrecursionlimit = boom  # type: ignore[assignment]
            interp = logos_lang.LogosInterpreter()
        finally:
            sys.setrecursionlimit = orig_set

        try:
            interp._max_recursion = 10**9
            with self.assertRaises(logos_lang.LogosError) as ctx:
                interp.visit(tree)
            self.assertIn("Host recursion limit reached", str(ctx.exception))
        finally:
            orig_set(orig_limit)

    def test_main_runs_file(self) -> None:
        # Test the logos.py main() function
        with tempfile.TemporaryDirectory() as td:
            path = os.path.join(td, "test.lg")
            with open(path, "w") as f: f.write("proclaim 1;")
            
            buf = io.StringIO()
            with patch.object(sys, "argv", ["logos.py", path]), redirect_stdout(buf):
                logos.main()
            self.assertIn("1", buf.getvalue())

    def test_main_invokes_user_main_function_if_defined(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = os.path.join(td, "prog_with_main.lg")
            with open(path, "w", encoding="utf-8") as f:
                f.write("mystery main() { silence; } amen\n")
                f.write("proclaim 1;\n")

            buf = io.StringIO()
            with (
                patch.object(logos.sys, "argv", ["logos.py", path]),
                patch.object(logos.sys, "exit", side_effect=AssertionError("exit should not be called")),
                redirect_stdout(buf),
            ):
                logos.main()
            self.assertIn("1", buf.getvalue())

    def test_main_exits_on_error(self) -> None:
        missing_path = os.path.join(tempfile.gettempdir(), "no_such_file.lg")
        with (
            patch.object(logos.sys, "argv", ["logos.py", missing_path]),
            patch.object(logos.sys, "exit", side_effect=SystemExit(1)),
        ):
            with self.assertRaises(SystemExit) as ctx:
                logos.main()
            self.assertEqual(ctx.exception.code, 1)

if __name__ == "__main__":
    unittest.main(verbosity=2)
