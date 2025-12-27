from __future__ import annotations

import sys
from pathlib import Path


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


def _load_grammar() -> str:
    # Best practice for VSIX packaging: ship the grammar with the extension itself.
    grammar_path = Path(__file__).with_name("logos.lark")
    try:
        grammar = grammar_path.read_text(encoding="utf-8")
    except FileNotFoundError as e:
        raise RuntimeError(
            "LOGOS Iconostasis: Missing bundled grammar file.\n"
            f"Expected: {grammar_path}\n"
            "If you are developing, ensure `logos-vscode/server/logos.lark` exists and is included in the VSIX."
        ) from e

    if not grammar.strip():
        raise RuntimeError(f"LOGOS Iconostasis: Empty grammar file: {grammar_path}")

    return grammar


PARSER = Lark(_load_grammar(), parser="lalr", propagate_positions=True)


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
