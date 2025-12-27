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
        "Install into your chosen interpreter: pip install -r packages/logos-vscode/server/requirements.txt\n"
        f"Details: {e}"
    )
    raise

try:
    from lark import Lark
    from lark.tree import Tree
    from lark.lexer import Token
except Exception as e:
    _fatal(
        "LOGOS Iconostasis: Missing Lark.\n"
        "Install: pip install -r packages/logos-vscode/server/requirements.txt\n"
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
            "If you are developing, ensure `packages/logos-vscode/server/logos.lark` exists and is included in the VSIX."
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


def _infer_literal_type(expr: object) -> str | None:
    """Infer a simple Logos type name from a literal expression node."""
    if isinstance(expr, Tree):
        rule = expr.data
        if rule == "number":
            s = str(expr.children[0])
            return "HolyFloat" if "." in s else "HolyInt"
        if rule == "string":
            return "Text"
        if rule in ("verily", "nay"):
            return "Bool"
        if rule == "procession":
            return "Procession"
    return None


def _type_compatible(expected: str, actual: str) -> bool:
    if expected in ("HolyFloat", "Float", "Double") and actual in ("HolyInt", "HolyFloat"):
        return True
    return expected == actual


def _diag_from_node(node: Tree, msg: str, severity: DiagnosticSeverity) -> Diagnostic:
    meta = getattr(node, "meta", None)
    line0 = (getattr(meta, "line", 1) - 1) if meta else 0
    col0 = (getattr(meta, "column", 1) - 1) if meta else 0
    d = _make_diag(line0, col0, msg)
    d.severity = severity
    return d


def _collect_icon_schemas(tree: Tree) -> dict[str, dict[str, str]]:
    icons: dict[str, dict[str, str]] = {}

    def walk(node: object) -> None:
        if not isinstance(node, Tree):
            return

        if node.data == "icon_def":
            name = str(node.children[0])
            fields: dict[str, str] = {}
            for child in node.children[1:]:
                if isinstance(child, Tree) and child.data == "field_decl":
                    fields[str(child.children[0])] = str(child.children[1])
            icons[name] = fields

        for c in node.children:
            walk(c)

    walk(tree)
    return icons


def _collect_var_types(tree: Tree) -> dict[str, str]:
    """Collect annotated variable declarations at module level (best-effort)."""
    types: dict[str, str] = {}

    def walk(node: object) -> None:
        if not isinstance(node, Tree):
            return

        if node.data == "inscribe":
            # children: NAME, (optional TYPE NAME), expr
            if len(node.children) == 3:
                var_name = str(node.children[0])
                declared = str(node.children[1])
                types[var_name] = declared

        for c in node.children:
            walk(c)

    walk(tree)
    return types


def _typecheck(tree: Tree) -> list[Diagnostic]:
    diags: list[Diagnostic] = []
    icons = _collect_icon_schemas(tree)
    var_types = _collect_var_types(tree)

    def walk(node: object) -> None:
        if not isinstance(node, Tree):
            return

        # inscribe x: HolyInt = <literal>;
        if node.data == "inscribe" and len(node.children) == 3:
            var_name = str(node.children[0])
            declared = str(node.children[1])
            expr = node.children[2]
            actual = _infer_literal_type(expr)
            if actual and not _type_compatible(declared, actual):
                diags.append(
                    _diag_from_node(
                        node,
                        f"Type mismatch: '{var_name}' declared {declared} but assigned {actual} literal.",
                        DiagnosticSeverity.Error,
                    )
                )

        # amend x = <literal>;  (only when x has a known declared type in this file)
        if node.data == "amend":
            target = node.children[0]
            value_expr = node.children[1]
            actual = _infer_literal_type(value_expr)
            if actual and isinstance(target, Tree) and target.data == "mut_var":
                var_name = str(target.children[0])
                declared = var_types.get(var_name)
                if declared and not _type_compatible(declared, actual):
                    diags.append(
                        _diag_from_node(
                            node,
                            f"Type mismatch: '{var_name}' declared {declared} but amended with {actual} literal.",
                            DiagnosticSeverity.Error,
                        )
                    )

        # write Icon { field=<literal> }
        if node.data == "write_icon":
            icon_name = str(node.children[0])
            schema = icons.get(icon_name, {})
            if len(node.children) > 1:
                assign_list = node.children[1]
                if isinstance(assign_list, Tree) and assign_list.data == "assign_list":
                    for assign in assign_list.children:
                        if not (isinstance(assign, Tree) and assign.data == "assign"):
                            continue
                        field = str(assign.children[0])
                        expr = assign.children[1]
                        expected = schema.get(field)
                        actual = _infer_literal_type(expr)
                        if expected and actual and not _type_compatible(expected, actual):
                            diags.append(
                                _diag_from_node(
                                    assign,
                                    f"Type mismatch: '{icon_name}.{field}' expects {expected} but got {actual} literal.",
                                    DiagnosticSeverity.Error,
                                )
                            )

        for c in node.children:
            walk(c)

    walk(tree)
    return diags


def validate(ls: LanguageServer, uri: str) -> None:
    doc = ls.workspace.get_document(uri)
    source = doc.source
    diagnostics: list[Diagnostic] = []

    try:
        tree = PARSER.parse(source)
        diagnostics.extend(_typecheck(tree))
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
