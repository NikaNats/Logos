import sys
import json
import logging
import re
from urllib.parse import urlparse, unquote

from compiler import LogosCompiler, DiakrisisEngine, SynodValidator


logging.basicConfig(
    filename="confessional.log",
    level=logging.DEBUG,
    filemode="w",
    format="%(asctime)s %(levelname)s %(message)s",
)


def _read_headers(stream) -> dict[str, str] | None:
    headers: dict[str, str] = {}
    while True:
        line = stream.readline()
        if not line:
            return None
        if line in (b"\r\n", b"\n"):
            return headers
        try:
            text = line.decode("ascii", errors="replace").strip()
        except Exception:
            continue
        if not text:
            return headers
        if ":" not in text:
            continue
        k, v = text.split(":", 1)
        headers[k.strip().lower()] = v.strip()


def read_message():
    """Reads a JSON-RPC/LSP message from stdin."""
    try:
        headers = _read_headers(sys.stdin.buffer)
        if headers is None:
            return None
        length = int(headers.get("content-length", "0"))
        if length <= 0:
            return None
        content = sys.stdin.buffer.read(length)
        if not content:
            return None
        return json.loads(content.decode("utf-8"))
    except Exception as e:
        logging.error("Revelation Error (read_message): %s", e)
        return None


def send_message(msg: dict):
    """Writes a JSON-RPC/LSP message to stdout."""
    try:
        content = json.dumps(msg, ensure_ascii=False)
        payload = content.encode("utf-8")
        sys.stdout.buffer.write(f"Content-Length: {len(payload)}\r\n\r\n".encode("ascii"))
        sys.stdout.buffer.write(payload)
        sys.stdout.buffer.flush()
    except Exception as e:
        logging.error("Revelation Error (send_message): %s", e)


def _uri_to_path(uri: str) -> str | None:
    try:
        if uri.startswith("file://"):
            parsed = urlparse(uri)
            return unquote(parsed.path.lstrip("/"))
        return None
    except Exception:
        return None


def _extract_line(msg: str) -> int | None:
    m = re.search(r"\bline\s+(\d+)\b", msg)
    if not m:
        return None
    try:
        return max(1, int(m.group(1)))
    except Exception:
        return None


def validate_text(text: str):
    """Parse + validate the current document text and return LSP diagnostics."""
    diagnostics: list[dict] = []

    compiler = LogosCompiler()

    # 1) SYNTAX CHECK
    try:
        tree = compiler.parser.parse(text)
    except Exception as e:
        line = getattr(e, "line", 1)
        col = getattr(e, "column", 1)
        diagnostics.append(
            {
                "range": {
                    "start": {"line": max(0, int(line) - 1), "character": max(0, int(col) - 1)},
                    "end": {"line": max(0, int(line) - 1), "character": max(0, int(col))},
                },
                "severity": 1,
                "message": f"Syntax Sin: {str(e).splitlines()[0]}",
                "source": "Logos Parser",
            }
        )
        return diagnostics

    # 2) SYNODAL CHECK
    try:
        SynodValidator().visit(tree)
    except Exception as e:
        msg = str(e)
        line = _extract_line(msg) or 1
        diagnostics.append(
            {
                "range": {
                    "start": {"line": line - 1, "character": 0},
                    "end": {"line": line - 1, "character": 200},
                },
                "severity": 1,
                "message": f"Synodal Error: {msg}",
                "source": "Synod",
            }
        )

    # 3) DIAKRISIS (Z3) CHECK
    try:
        engine = DiakrisisEngine()
        engine.visit(tree)
    except Exception as e:
        msg = str(e)
        line = _extract_line(msg) or 1
        severity = 2 if "PASTORAL WARNING" in msg else 1
        diagnostics.append(
            {
                "range": {
                    "start": {"line": line - 1, "character": 0},
                    "end": {"line": line - 1, "character": 200},
                },
                "severity": severity,
                "message": f"Ontological Heresy: {msg}",
                "source": "Diakrisis",
            }
        )

    return diagnostics


def main():
    logging.info("The Confessional is open.")

    documents: dict[str, str] = {}

    while True:
        msg = read_message()
        if msg is None:
            break

        method = msg.get("method")
        msg_id = msg.get("id")

        if method == "initialize":
            send_message(
                {
                    "jsonrpc": "2.0",
                    "id": msg_id,
                    "result": {
                        "capabilities": {
                            "textDocumentSync": {"openClose": True, "change": 1},
                        }
                    },
                }
            )
            continue

        if method == "shutdown":
            send_message({"jsonrpc": "2.0", "id": msg_id, "result": None})
            continue

        if method == "exit":
            break

        if method in ("textDocument/didOpen", "textDocument/didChange"):
            params = msg.get("params") or {}
            td = params.get("textDocument") or {}
            uri = td.get("uri")
            if not uri:
                continue

            if method == "textDocument/didOpen":
                text = td.get("text", "")
            else:
                changes = params.get("contentChanges") or []
                text = (changes[0] or {}).get("text", "") if changes else ""

            documents[uri] = text
            diags = validate_text(text)

            send_message(
                {
                    "jsonrpc": "2.0",
                    "method": "textDocument/publishDiagnostics",
                    "params": {"uri": uri, "diagnostics": diags},
                }
            )


if __name__ == "__main__":
    main()
