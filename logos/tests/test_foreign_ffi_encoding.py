import os
import struct
import subprocess
import sys
import tempfile
import unittest


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
LOGOS_DIR = os.path.join(REPO_ROOT, "logos")
COMPILER = os.path.join(LOGOS_DIR, "compiler.py")
DISASSEMBLER = os.path.join(LOGOS_DIR, "disassembler.py")


def _compile_lbc(source_path: str, out_lbc: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, COMPILER, source_path, "lbc", "--out", out_lbc],
        cwd=LOGOS_DIR,
        capture_output=True,
        text=True,
    )


def _disassemble(lbc_path: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, DISASSEMBLER, lbc_path],
        cwd=LOGOS_DIR,
        capture_output=True,
        text=True,
    )


def _read_exact(f, n: int) -> bytes:
    b = f.read(n)
    if len(b) != n:
        raise EOFError(f"Expected {n} bytes, got {len(b)}")
    return b


def _skip_constant_pool(f) -> None:
    cp_count = struct.unpack("<I", _read_exact(f, 4))[0]
    for _ in range(cp_count):
        tag = _read_exact(f, 1)[0]
        if tag == 0x01:  # INT
            _read_exact(f, 8)
        elif tag == 0x02:  # STR
            length = struct.unpack("<I", _read_exact(f, 4))[0]
            _read_exact(f, length)
        elif tag == 0x03:  # FLOAT
            _read_exact(f, 8)
        elif tag == 0x04:  # BOOL
            _read_exact(f, 1)
        elif tag == 0x05:  # CHAR
            _read_exact(f, 4)
        elif tag == 0x06:  # BYTE
            _read_exact(f, 1)
        else:
            raise ValueError(f"Unknown constant tag 0x{tag:02X}")


def _read_lbc_code_bytes(lbc_path: str) -> bytes:
    with open(lbc_path, "rb") as f:
        header = _read_exact(f, 5)
        if header != b"LOGOS":
            raise ValueError(f"Unexpected header: {header!r}")
        _read_exact(f, 1)  # version
        _read_exact(f, 32)  # seal

        _skip_constant_pool(f)

        code_len = struct.unpack("<I", _read_exact(f, 4))[0]
        code = _read_exact(f, code_len)
        return code


def _parse_invoke_foreign_payload(code: bytes, start: int):
    """Parse at opcode position `start` (where code[start] == 0xFE)."""
    if code[start] != 0xFE:
        raise ValueError("Not an INVOKE_FOREIGN opcode")

    idx = start + 1
    lib_len = struct.unpack("<I", code[idx : idx + 4])[0]
    idx += 4
    lib = code[idx : idx + lib_len].decode("utf-8", errors="strict")
    idx += lib_len

    fn_len = struct.unpack("<I", code[idx : idx + 4])[0]
    idx += 4
    fn = code[idx : idx + fn_len].decode("utf-8", errors="strict")
    idx += fn_len

    ret_tag = code[idx]
    idx += 1
    argc = code[idx]
    idx += 1

    arg_tags = list(code[idx : idx + argc])
    idx += argc

    return {
        "lib": lib,
        "fn": fn,
        "ret_tag": ret_tag,
        "argc": argc,
        "arg_tags": arg_tags,
        "end": idx,
    }


class TestForeignFFIEncoding(unittest.TestCase):
    def test_foreign_cos_demo_encodes_0xFE_payload(self):
        src = os.path.join(LOGOS_DIR, "foreign_cos_demo.lg")
        self.assertTrue(os.path.isfile(src), "Expected demo source to exist")

        with tempfile.TemporaryDirectory() as td:
            out_lbc = os.path.join(td, "foreign_cos_demo.lbc")

            proc = _compile_lbc(src, out_lbc)
            self.assertEqual(
                proc.returncode,
                0,
                msg=f"Compiler failed:\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}",
            )

            code = _read_lbc_code_bytes(out_lbc)
            try:
                op_index = code.index(bytes([0xFE]))
            except ValueError:
                self.fail("No INVOKE_FOREIGN (0xFE) opcode found in emitted bytecode")

            meta = _parse_invoke_foreign_payload(code, op_index)
            self.assertEqual(meta["lib"], "msvcrt.dll")
            self.assertEqual(meta["fn"], "cos")
            self.assertEqual(meta["ret_tag"], 0x02)  # HolyFloat
            self.assertEqual(meta["argc"], 1)
            self.assertEqual(meta["arg_tags"], [0x02])  # HolyFloat

    def test_disassembler_prints_invoke_foreign(self):
        src = os.path.join(LOGOS_DIR, "foreign_cos_demo.lg")

        with tempfile.TemporaryDirectory() as td:
            out_lbc = os.path.join(td, "foreign_cos_demo.lbc")

            proc = _compile_lbc(src, out_lbc)
            self.assertEqual(proc.returncode, 0, msg=proc.stderr)

            dis = _disassemble(out_lbc)
            self.assertEqual(dis.returncode, 0, msg=dis.stderr)
            self.assertIn("INVOKE_FOREIGN msvcrt.dll::cos", dis.stdout)

    def test_foreign_requires_typed_params(self):
        # Untyped params must fail because the signature requires type tags.
        bad_src = "foreign \"msvcrt.dll\" service cos(x) -> HolyFloat;\nministry main() -> Void { behold 0; } amen\n"

        with tempfile.TemporaryDirectory() as td:
            src_path = os.path.join(td, "bad_foreign.lg")
            out_lbc = os.path.join(td, "bad_foreign.lbc")
            with open(src_path, "w", encoding="utf-8") as f:
                f.write(bad_src)

            proc = subprocess.run(
                [sys.executable, COMPILER, src_path, "lbc", "--out", out_lbc],
                cwd=LOGOS_DIR,
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(proc.returncode, 0)
            combined = (proc.stdout + "\n" + proc.stderr).lower()
            self.assertIn("requires typed params", combined)

    def test_foreign_void_return_encodes_ret_tag_0(self):
        # Even without running the VM, we can validate that Void return is tagged as 0.
        src = "\n".join(
            [
                'foreign "msvcrt.dll" service noop(x: HolyInt) -> Void;',
                'ministry main() -> Void {',
                '  noop(1);',
                '  behold 0;',
                '} amen',
                '',
            ]
        )
        with tempfile.TemporaryDirectory() as td:
            src_path = os.path.join(td, "void_ret.lg")
            out_lbc = os.path.join(td, "void_ret.lbc")
            with open(src_path, "w", encoding="utf-8") as f:
                f.write(src)

            proc = _compile_lbc(src_path, out_lbc)
            self.assertEqual(proc.returncode, 0, msg=proc.stderr)

            code = _read_lbc_code_bytes(out_lbc)
            op_index = code.index(bytes([0xFE]))
            meta = _parse_invoke_foreign_payload(code, op_index)
            self.assertEqual(meta["ret_tag"], 0x00)
            self.assertEqual(meta["arg_tags"], [0x01])

            dis = _disassemble(out_lbc)
            self.assertEqual(dis.returncode, 0, msg=dis.stderr)
            self.assertIn("-> Void", dis.stdout)

    def test_foreign_multi_arg_encoding(self):
        src = "\n".join(
            [
                'foreign "msvcrt.dll" service f(a: HolyInt, b: HolyFloat) -> HolyInt;',
                'ministry main() -> Void {',
                '  gift r: HolyInt = f(1, 2.0);',
                '  behold r;',
                '} amen',
                '',
            ]
        )
        with tempfile.TemporaryDirectory() as td:
            src_path = os.path.join(td, "multi_arg.lg")
            out_lbc = os.path.join(td, "multi_arg.lbc")
            with open(src_path, "w", encoding="utf-8") as f:
                f.write(src)

            proc = _compile_lbc(src_path, out_lbc)
            self.assertEqual(proc.returncode, 0, msg=proc.stderr)

            code = _read_lbc_code_bytes(out_lbc)
            op_index = code.index(bytes([0xFE]))
            meta = _parse_invoke_foreign_payload(code, op_index)
            self.assertEqual(meta["lib"], "msvcrt.dll")
            self.assertEqual(meta["fn"], "f")
            self.assertEqual(meta["ret_tag"], 0x01)  # HolyInt
            self.assertEqual(meta["argc"], 2)
            self.assertEqual(meta["arg_tags"], [0x01, 0x02])

    def test_foreign_arg_count_mismatch_fails(self):
        src = "\n".join(
            [
                'foreign "msvcrt.dll" service f(a: HolyInt, b: HolyFloat) -> HolyInt;',
                'ministry main() -> Void {',
                '  behold f(1);',
                '} amen',
                '',
            ]
        )
        with tempfile.TemporaryDirectory() as td:
            src_path = os.path.join(td, "arg_mismatch.lg")
            out_lbc = os.path.join(td, "arg_mismatch.lbc")
            with open(src_path, "w", encoding="utf-8") as f:
                f.write(src)

            proc = _compile_lbc(src_path, out_lbc)
            self.assertNotEqual(proc.returncode, 0)
            combined = (proc.stdout + "\n" + proc.stderr).lower()
            self.assertIn("expects", combined)
            self.assertIn("but got", combined)

    def test_foreign_declaration_is_compile_time_only(self):
        # A foreign declaration alone should not emit 0xFE (only calls do).
        src = "\n".join(
            [
                'foreign "msvcrt.dll" service cos(x: HolyFloat) -> HolyFloat;',
                'ministry main() -> Void {',
                '  behold 0;',
                '} amen',
                '',
            ]
        )
        with tempfile.TemporaryDirectory() as td:
            src_path = os.path.join(td, "decl_only.lg")
            out_lbc = os.path.join(td, "decl_only.lbc")
            with open(src_path, "w", encoding="utf-8") as f:
                f.write(src)

            proc = _compile_lbc(src_path, out_lbc)
            self.assertEqual(proc.returncode, 0, msg=proc.stderr)

            code = _read_lbc_code_bytes(out_lbc)
            self.assertNotIn(bytes([0xFE]), code)


if __name__ == "__main__":
    unittest.main()
