from __future__ import annotations

import os
import subprocess
import sys
import textwrap
import unittest


class FFIResilienceTests(unittest.TestCase):
    def _run_subprocess(self, code: str, timeout: float = 10.0) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, "-c", code],
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )

    def test_ffi_worker_isolation_handles_foreign_binding_errors(self) -> None:
        code = textwrap.dedent(
            """
            import logos_lang
            from lark import Lark

            source = 'apocrypha "msvcrt" mystery definitely_missing_symbol() -> HolyInt;'
            parser = Lark(logos_lang.LOGOS_GRAMMAR, parser="lalr")
            sec = logos_lang.SecurityContext(
                allow_ffi=True,
                whitelist={"msvcrt": {"definitely_missing_symbol"}},
                allow_unsafe_pointers=True,
            )
            interp = logos_lang.LogosInterpreter(security=sec)

            try:
                interp.visit(parser.parse(source))
            except logos_lang.LogosError as e:
                print(type(e).__name__)
                raise SystemExit(0)

            raise SystemExit(3)
            """
        )
        result = self._run_subprocess(code)
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        self.assertIn("LogosError", result.stdout)

    def test_destructive_segfault_probe_isolated_subprocess(self) -> None:
        if os.environ.get("LOGOS_ENABLE_DESTRUCTIVE_FFI_TESTS", "") != "1":
            self.skipTest("Set LOGOS_ENABLE_DESTRUCTIVE_FFI_TESTS=1 to run segfault isolation probe")

        code = textwrap.dedent(
            """
            import ctypes
            # Intentional crash probe in isolated process.
            ctypes.string_at(0)
            """
        )
        result = self._run_subprocess(code)
        self.assertNotEqual(result.returncode, 0)

    @unittest.skipUnless(sys.platform.startswith("win"), "Windows-only leak probe")
    def test_memory_growth_probe_for_repeated_ctypes_calls(self) -> None:
        try:
            __import__("psutil")
        except Exception:
            self.skipTest("psutil is required for RSS memory probe")

        code = textwrap.dedent(
            """
            import ctypes
            import gc
            import os
            import psutil

            msvcrt = ctypes.CDLL("msvcrt")
            strlen = msvcrt.strlen
            strlen.argtypes = [ctypes.c_char_p]
            strlen.restype = ctypes.c_size_t

            proc = psutil.Process(os.getpid())
            before = proc.memory_info().rss
            payload = b"pilgrim" * 128

            for _ in range(50000):
                strlen(payload)

            gc.collect()
            after = proc.memory_info().rss
            print(after - before)
            """
        )

        result = self._run_subprocess(code, timeout=20.0)
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        delta = int((result.stdout or "0").strip() or "0")
        # Loose guard to catch obvious runaway leaks while avoiding platform noise.
        self.assertLess(delta, 32 * 1024 * 1024)


if __name__ == "__main__":
    unittest.main(verbosity=2)
