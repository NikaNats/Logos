from __future__ import annotations

import os
import sys


def _fatal(msg: str) -> None:
    sys.stderr.write(msg + "\n")
    sys.stderr.flush()


try:
    try:
        # pygls 2.x
        from pygls.lsp.server import LanguageServer
    except Exception:
        # pygls 1.x fallback
        from pygls.server import LanguageServer
    from lsprotocol.types import (
        TEXT_DOCUMENT_DID_CHANGE,
        TEXT_DOCUMENT_DID_OPEN,
        Diagnostic,
        DiagnosticSeverity,
        Position,
        Range,
    )
except Exception as e:
    _fatal(
        "LOGOS Iconostasis: Failed to import LSP dependencies.\n"
        "Install into your chosen interpreter: pip install -r logos-vscode/server/requirements.txt\n"
        f"Details: {e}"
    )
    raise

try:
    from lark import Lark
except Exception as e:
    _fatal(
        "LOGOS Iconostasis: Missing Lark.\n"
        "Install: pip install -r logos-vscode/server/requirements.txt\n"
        f"Details: {e}"
    )
    raise


SERVER = LanguageServer("logos-server", "v0.1")


def _load_trinity_logos_dir() -> str:
    # Extension dev layout: <repo>/logos-vscode/server/lsp_server.py
    # We want <repo>/logos for compiler.py + logos.lark.
    repo_root = os.path.normpath(os.path.join(os.path.dirname(__file__), "..", ".."))
    logos_dir = os.path.join(repo_root, "logos")
    return logos_dir


LOGOS_DIR = _load_trinity_logos_dir()
LARK_PATH = os.path.join(LOGOS_DIR, "logos.lark")

with open(LARK_PATH, "r", encoding="utf-8") as f:
    GRAMMAR = f.read()

PARSER = Lark(GRAMMAR, parser="lalr", propagate_positions=True)

# Import compiler pieces from the Trinity repo.
sys.path.insert(0, LOGOS_DIR)
from compiler import SynodValidator, DiakrisisEngine  # type: ignore  # noqa: E402


def _make_diag(line0: int, col0: int, msg: str) -> Diagnostic:
    start = Position(line=max(line0, 0), character=max(col0, 0))
    end = Position(line=max(line0, 0), character=max(col0, 0) + 10)
    return Diagnostic(
        range=Range(start=start, end=end),
        message=f"Heresy: {msg}",
        severity=DiagnosticSeverity.Error,
        source="LOGOS Diakrisis",
    )


def validate(ls: LanguageServer, uri: str) -> None:
    doc = ls.workspace.get_document(uri)
    source = doc.source
    diagnostics: list[Diagnostic] = []

    try:
        tree = PARSER.parse(source)
        SynodValidator().visit(tree)
        DiakrisisEngine().visit(tree)
    except Exception as e:
        # Best-effort location mapping.
        line0 = getattr(e, "line", getattr(getattr(e, "meta", None), "line", 1)) - 1
        col0 = getattr(e, "column", getattr(getattr(e, "meta", None), "column", 1)) - 1
        msg = str(e).split("\n")[0]
        diagnostics.append(_make_diag(line0, col0, msg))

    ls.publish_diagnostics(uri, diagnostics)


@SERVER.feature(TEXT_DOCUMENT_DID_OPEN)
def did_open(ls: LanguageServer, params):
    validate(ls, params.text_document.uri)


@SERVER.feature(TEXT_DOCUMENT_DID_CHANGE)
def did_change(ls: LanguageServer, params):
    validate(ls, params.text_document.uri)


if __name__ == "__main__":
    SERVER.start_io()
