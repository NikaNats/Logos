import os
import struct
import subprocess
import sys

from compiler import ByteConst, CharConst, LogosCompiler


# Packet types (Catechism protocol)
PKT_DEFINE_CONST = 0x01
PKT_EXECUTE = 0x02
PKT_AMEN = 0x03


class Catechism:
    def __init__(self, svm_path: str | None = None):
        self.compiler = LogosCompiler()
        self.known_symbols: dict[str, str] = {}

        if svm_path is None:
            trinity_root = os.path.normpath(os.path.join(os.path.dirname(__file__), ".."))
            exe = "logos-svm.exe" if sys.platform.startswith("win") else "logos-svm"
            svm_path = os.path.join(trinity_root, "logos-svm", "target", "release", exe)

        if not os.path.isfile(svm_path):
            raise SystemExit(
                f"Catechism Error: SVM binary not found at {svm_path}. "
                "Build it first: (cd logos-svm && cargo build --release)"
            )

        self.svm = subprocess.Popen(
            [svm_path, "--repl"],
            stdin=subprocess.PIPE,
            stdout=None,  # inherit
            stderr=None,
        )

        print("LOGOS Catechism v0.1")
        print("Type 'amen' to exit.\n")

    def _send_packet(self, pkt_type: int, payload: bytes) -> None:
        if self.svm.stdin is None:
            raise RuntimeError("Catechism Error: SVM stdin is not available")
        header = struct.pack("<BI", pkt_type, len(payload))
        self.svm.stdin.write(header)
        if payload:
            self.svm.stdin.write(payload)
        self.svm.stdin.flush()

    def _encode_const(self, val) -> bytes:
        # Payload begins with the constant tag used by the .lbc format.
        # Tags:
        #  0x01 Int(i64)
        #  0x02 Text(u32 len + bytes)
        #  0x03 Float(f64)
        #  0x04 Bool(u8)
        #  0x05 Char(u32 codepoint)
        #  0x06 Byte(u8)
        payload = bytearray()

        if isinstance(val, bool):
            payload.append(0x04)
            payload.append(0x01 if val else 0x00)
            return bytes(payload)

        if isinstance(val, ByteConst):
            payload.append(0x06)
            payload.append(val.value)
            return bytes(payload)

        if isinstance(val, CharConst):
            payload.append(0x05)
            payload.extend(struct.pack("<I", val.codepoint))
            return bytes(payload)

        if isinstance(val, int):
            payload.append(0x01)
            payload.extend(struct.pack("<q", val))
            return bytes(payload)

        if isinstance(val, str):
            payload.append(0x02)
            enc = val.encode("utf-8")
            payload.extend(struct.pack("<I", len(enc)))
            payload.extend(enc)
            return bytes(payload)

        if isinstance(val, float):
            payload.append(0x03)
            payload.extend(struct.pack("<d", val))
            return bytes(payload)

        raise TypeError(f"Catechism Error: Unsupported constant type: {type(val)}")

    def loop(self) -> None:
        while True:
            try:
                line = input(">> ")
            except EOFError:
                line = "amen"

            if line.strip() == "":
                continue

            if line.strip().lower() == "amen":
                self._send_packet(PKT_AMEN, b"")
                try:
                    self.svm.wait(timeout=2)
                except Exception:
                    pass
                return

            try:
                code, new_consts, new_syms = self.compiler.compile_fragment(line, self.known_symbols)
                self.known_symbols.update(new_syms)

                for c in new_consts:
                    self._send_packet(PKT_DEFINE_CONST, self._encode_const(c))

                self._send_packet(PKT_EXECUTE, bytes(code))

            except Exception as e:
                print(f"Heresy: {e}")


def main() -> None:
    Catechism().loop()


if __name__ == "__main__":
    main()
