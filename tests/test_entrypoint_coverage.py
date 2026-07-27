"""Tests for logos.py entrypoint CLI, REPL, and coverage requirements."""

from __future__ import annotations

import io
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from typing import Any
from unittest.mock import patch

from lark import Lark

import logos
import logos_lang


class EntrypointCoverageTests(unittest.TestCase):
    """Test suite targeting 100% statement and branch coverage for logos.py."""

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
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "test.lg"
            path.write_text("proclaim 1;", encoding="utf-8")

            buf = io.StringIO()
            with patch.object(sys, "argv", ["logos.py", str(path)]), redirect_stdout(buf):
                logos.main()
            self.assertIn("1", buf.getvalue())

    def test_main_invokes_user_main_function_if_defined(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "prog_with_main.lg"
            path.write_text("mystery main() { silence; } amen\nproclaim 1;\n", encoding="utf-8")

            buf = io.StringIO()
            with (
                patch.object(logos.sys, "argv", ["logos.py", str(path)]),
                patch.object(
                    logos.sys,
                    "exit",
                    side_effect=AssertionError("exit should not be called"),
                ),
                redirect_stdout(buf),
            ):
                logos.main()
            self.assertIn("1", buf.getvalue())

    def test_main_exits_on_error(self) -> None:
        missing_path = Path(tempfile.gettempdir()) / "no_such_file.lg"
        with (
            patch.object(logos.sys, "argv", ["logos.py", str(missing_path)]),
            patch.object(logos.sys, "exit", side_effect=SystemExit(1)),
        ):
            with self.assertRaises(SystemExit) as ctx:
                logos.main()
            self.assertEqual(ctx.exception.code, 1)

    def test_load_trusted_lsp_types(self) -> None:
        self.assertEqual(logos._load_trusted_lsp_types(None), {})
        with tempfile.TemporaryDirectory() as td:
            temp_dir = Path(td)
            missing = temp_dir / "missing.json"
            with self.assertRaises(logos_lang.LogosError):
                logos._load_trusted_lsp_types(missing)

            not_dict = temp_dir / "array.json"
            not_dict.write_text("[1, 2, 3]", encoding="utf-8")
            with self.assertRaises(logos_lang.LogosError):
                logos._load_trusted_lsp_types(not_dict)

            bad_json = temp_dir / "bad.json"
            bad_json.write_text("invalid json {", encoding="utf-8")
            with self.assertRaises(logos_lang.LogosError):
                logos._load_trusted_lsp_types(bad_json)

            valid = temp_dir / "valid.json"
            valid.write_text('{"x": "HolyInt", "y": "Text", "invalid": 123}', encoding="utf-8")
            res = logos._load_trusted_lsp_types(valid)
            self.assertEqual(res, {"x": "HolyInt", "y": "Text"})

    def test_default_bytecode_path(self) -> None:
        path = logos._default_bytecode_path("a/b/c.lg")
        self.assertTrue(path.endswith("c.bytecode.json"))

    def test_main_cli_options(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            temp_dir = Path(td)
            script = temp_dir / "script.lg"
            script.write_text("inscribe x = 1; proclaim x;", encoding="utf-8")

            elision_json = temp_dir / "types.json"
            elision_json.write_text('{"x": "HolyInt"}', encoding="utf-8")

            bc_out = temp_dir / "out.json"

            buf = io.StringIO()
            with (
                patch.object(
                    sys,
                    "argv",
                    [
                        "logos.py",
                        str(script),
                        "--allow-lib",
                        "msvcrt",
                        "--allow-unsafe-pointers",
                        "--require-os-sandbox-for-ffi",
                        "--sandbox-attestation-env",
                        "TEST_ENV",
                        "--lsp-type-elision-file",
                        str(elision_json),
                        "--emit-bytecode",
                        str(bc_out),
                    ],
                ),
                redirect_stdout(buf),
            ):
                logos.main()
            self.assertTrue(bc_out.exists())

    def test_main_wasi_target(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            temp_dir = Path(td)
            script = temp_dir / "script.lg"
            script.write_text("proclaim 1;", encoding="utf-8")

            with (
                patch.object(
                    sys,
                    "argv",
                    [
                        "logos.py",
                        str(script),
                        "--execution-target",
                        "wasi",
                        "--wasi-module",
                        str(temp_dir / "fake.wasm"),
                    ],
                ),
                patch("logos.WasiExecutionBridge.execute", return_value=0),
                patch("pathlib.Path.exists", return_value=True),
            ):
                logos.main()

    def test_main_wasi_compiled_program_none_raises(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            temp_dir = Path(td)
            script = temp_dir / "script.lg"
            script.write_text("proclaim 1;", encoding="utf-8")

            with (
                patch.object(
                    sys,
                    "argv",
                    [
                        "logos.py",
                        str(script),
                        "--execution-target",
                        "wasi",
                    ],
                ),
                patch("logos.LogosInterpreter.compile_bytecode", return_value=None),
                patch.object(logos.sys, "exit", side_effect=SystemExit(1)),
            ):
                with self.assertRaises(SystemExit):
                    logos.main()

    def test_main_repl_trigger(self) -> None:
        with patch.object(sys, "argv", ["logos.py"]), patch("logos.run_repl") as mock_repl:
            logos.main()
            mock_repl.assert_called_once()

    def test_main_fatal_error_unicode_encode_error(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            script = Path(td) / "broken.lg"
            script.write_text("amend x = 1;", encoding="utf-8")

            orig_print = print

            def bad_print(*args: Any, **kwargs: Any) -> None:
                if any("☨" in str(arg) for arg in args):
                    raise UnicodeEncodeError("utf-8", "☨", 0, 1, "cannot encode")
                orig_print(*args, **kwargs)

            buf = io.StringIO()
            with (
                patch.object(sys, "argv", ["logos.py", str(script)]),
                patch.object(logos.sys, "exit", side_effect=SystemExit(1)),
                patch("builtins.print", side_effect=bad_print),
                redirect_stdout(buf),
            ):
                with self.assertRaises(SystemExit):
                    logos.main()


if __name__ == "__main__":
    unittest.main(verbosity=2)