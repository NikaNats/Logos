from __future__ import annotations

import json
import queue
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from pathlib import Path
from typing import Any, Callable

ROOT = Path(__file__).resolve().parents[1]
LSP_PATH = ROOT / "packages" / "logos-vscode" / "server" / "lsp_server.py"


class _LspProcessClient:
    def __init__(self) -> None:
        self._proc = subprocess.Popen(
            [sys.executable, str(LSP_PATH)],
            cwd=str(ROOT),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        self._messages: "queue.Queue[dict[str, Any]]" = queue.Queue()
        self._reader = threading.Thread(target=self._read_loop, daemon=True)
        self._reader.start()

    def _read_loop(self) -> None:
        assert self._proc.stdout is not None
        stdout = self._proc.stdout

        while True:
            line = stdout.readline()
            if not line:
                return

            headers: dict[str, str] = {}
            while line not in {b"\r\n", b"\n", b""}:
                text = line.decode("ascii", errors="ignore")
                if ":" in text:
                    key, value = text.split(":", 1)
                    headers[key.strip().lower()] = value.strip()
                line = stdout.readline()
                if not line:
                    return

            try:
                length = int(headers.get("content-length", "0"))
            except ValueError:
                continue
            if length <= 0:
                continue

            body = stdout.read(length)
            if not body:
                return
            try:
                payload = json.loads(body.decode("utf-8"))
            except Exception:
                continue
            if isinstance(payload, dict):
                self._messages.put(payload)

    def send(self, payload: dict[str, Any]) -> None:
        assert self._proc.stdin is not None
        body = json.dumps(payload).encode("utf-8")
        header = f"Content-Length: {len(body)}\r\n\r\n".encode("ascii")
        self._proc.stdin.write(header)
        self._proc.stdin.write(body)
        self._proc.stdin.flush()

    def wait_for(
        self,
        predicate: Callable[[dict[str, Any]], bool],
        *,
        timeout: float = 8.0,
    ) -> dict[str, Any]:
        deadline = time.time() + timeout
        observed: list[dict[str, Any]] = []

        while time.time() < deadline:
            if self._proc.poll() is not None:
                break
            try:
                msg = self._messages.get(timeout=0.1)
            except queue.Empty:
                continue
            if predicate(msg):
                return msg
            observed.append(msg)

        stderr_text = ""
        if self._proc.poll() is not None and self._proc.stderr is not None:
            try:
                stderr_text = self._proc.stderr.read().decode("utf-8", errors="ignore")
            except Exception:
                stderr_text = ""
        raise AssertionError(
            "Timed out waiting for expected LSP payload. "
            f"Observed={observed[-3:] if observed else []}; stderr={stderr_text!r}"
        )

    def close(self) -> None:
        try:
            self.send({"jsonrpc": "2.0", "id": 99, "method": "shutdown", "params": None})
        except Exception:
            pass
        try:
            self.send({"jsonrpc": "2.0", "method": "exit", "params": None})
        except Exception:
            pass

        try:
            self._proc.terminate()
            self._proc.wait(timeout=3)
        except Exception:
            self._proc.kill()


class LspJsonRpcIntegrationTests(unittest.TestCase):
    def test_publish_diagnostics_over_jsonrpc_open_and_change(self) -> None:
        client = _LspProcessClient()
        try:
            with tempfile.TemporaryDirectory() as td:
                uri = (Path(td) / "case.lg").as_uri()
                broken = 'mystery main() { inscribe x: HolyInt = "no"; } amen'
                fixed = "mystery main() { inscribe x: HolyInt = 7; } amen"

                client.send(
                    {
                        "jsonrpc": "2.0",
                        "id": 1,
                        "method": "initialize",
                        "params": {
                            "processId": None,
                            "rootUri": ROOT.as_uri(),
                            "capabilities": {},
                        },
                    }
                )
                client.wait_for(lambda m: m.get("id") == 1 and "result" in m)

                client.send({"jsonrpc": "2.0", "method": "initialized", "params": {}})

                client.send(
                    {
                        "jsonrpc": "2.0",
                        "method": "textDocument/didOpen",
                        "params": {
                            "textDocument": {
                                "uri": uri,
                                "languageId": "logos",
                                "version": 1,
                                "text": broken,
                            }
                        },
                    }
                )

                first = client.wait_for(
                    lambda m: m.get("method") == "textDocument/publishDiagnostics"
                    and m.get("params", {}).get("uri") == uri
                )
                diagnostics = first.get("params", {}).get("diagnostics", [])
                self.assertTrue(any("Type mismatch" in d.get("message", "") for d in diagnostics))

                client.send(
                    {
                        "jsonrpc": "2.0",
                        "method": "textDocument/didChange",
                        "params": {
                            "textDocument": {"uri": uri, "version": 2},
                            "contentChanges": [{"text": fixed}],
                        },
                    }
                )

                second = client.wait_for(
                    lambda m: m.get("method") == "textDocument/publishDiagnostics"
                    and m.get("params", {}).get("uri") == uri
                    and isinstance(m.get("params", {}).get("diagnostics"), list)
                )
                self.assertEqual(second.get("params", {}).get("diagnostics"), [])
        finally:
            client.close()


if __name__ == "__main__":
    unittest.main(verbosity=2)
