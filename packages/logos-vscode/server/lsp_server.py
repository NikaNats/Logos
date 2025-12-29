from __future__ import annotations

import os
import sys
from pathlib import Path


def _fatal(msg: str) -> None:
    sys.stderr.write(msg + "\n")
    sys.stderr.flush()


try:
    try:
        from pygls.lsp.server import LanguageServer
    except Exception:
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
    _fatal(f"LOGOS Iconostasis: Failed to import LSP dependencies: {e}")
    raise

try:
    from lark import Lark, Tree
    from lark.lexer import Token
except Exception as e:
    _fatal(f"LOGOS Iconostasis: Missing Lark: {e}")
    raise


SERVER = LanguageServer("logos-server", "v0.2")

# --- PATH SETUP ---
# Ensure logos_lang is importable from ../../../
SERVER_DIR = Path(__file__).resolve().parent
ROOT_DIR = SERVER_DIR.parents[2]
if str(ROOT_DIR) not in sys.path:
    sys.path.append(str(ROOT_DIR))

try:
    # IMPORT FROM NEW PACKAGE
    from logos_lang import TypeCanon, LOGOS_GRAMMAR
except ImportError:
    _fatal(
        "LOGOS Iconostasis: Could not import 'logos_lang'. Ensure repo root is in PYTHONPATH."
    )
    raise

# --- PARSER CACHING ---
_PARSER = None


def get_parser() -> "Lark":
    """Lazily construct and cache the Logos grammar parser using the canonical definition."""
    global _PARSER
    if _PARSER is None:
        # Use the grammar string from the package, not a separate file
        _PARSER = Lark(LOGOS_GRAMMAR, parser="lalr", propagate_positions=True)
    return _PARSER


class _ParserProxy:
    def parse(self, *args, **kwargs):
        return get_parser().parse(*args, **kwargs)


PARSER = _ParserProxy()

# --- DIAGNOSTICS LOGIC ---


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
    types: dict[str, str] = {}

    def walk(node: object) -> None:
        if not isinstance(node, Tree):
            return
        if node.data == "inscribe" and len(node.children) == 3:
            types[str(node.children[0])] = str(node.children[1])
        for c in node.children:
            walk(c)

    walk(tree)
    return types


def _collect_function_sigs(
    tree: Tree,
) -> dict[str, tuple[list[tuple[str, str | None]], str | None]]:
    sigs = {}

    def walk(node: object) -> None:
        if not isinstance(node, Tree):
            return
        if node.data == "mystery_def":
            name = str(node.children[0])
            idx = 1
            params = []
            if (
                idx < len(node.children)
                and isinstance(node.children[idx], Tree)
                and node.children[idx].data == "params"
            ):
                for p in node.children[idx].children:
                    if isinstance(p, Tree) and p.data == "param":
                        p_name = str(p.children[0])
                        p_type = str(p.children[1]) if len(p.children) >= 2 else None
                        params.append((p_name, p_type))
                idx += 1
            ret_type = None
            if (
                idx < len(node.children)
                and isinstance(node.children[idx], Token)
                and node.children[idx].type == "NAME"
            ):
                ret_type = str(node.children[idx])
            sigs[name] = (params, ret_type)
        for c in node.children:
            walk(c)

    walk(tree)
    return sigs


def _infer_expr_type(expr: object, lookup_var_type, func_sigs, diags) -> str | None:
    literal = _infer_literal_type(expr)
    if literal:
        return literal
    if not isinstance(expr, Tree):
        return None
    rule = expr.data

    if rule == "var":
        return lookup_var_type(str(expr.children[0]))
    if rule == "transfigure" and len(expr.children) >= 2:
        return str(expr.children[1])

    if rule in ("add", "sub", "mul", "div", "eq", "ne", "lt", "gt", "le", "ge"):
        l = _infer_expr_type(expr.children[0], lookup_var_type, func_sigs, diags)
        r = _infer_expr_type(expr.children[1], lookup_var_type, func_sigs, diags)
        if not l or not r:
            return None
        res = TypeCanon.resolve_binary_op(rule, l, r)
        if not res:
            diags.append(
                _diag_from_node(
                    expr,
                    f"Type mismatch: cannot {rule} {l} and {r}.",
                    DiagnosticSeverity.Error,
                )
            )
            return None
        return res

    if rule == "neg":
        t = _infer_expr_type(expr.children[0], lookup_var_type, func_sigs, diags)
        if t and t not in TypeCanon.NUMERIC:
            diags.append(
                _diag_from_node(
                    expr,
                    f"Type mismatch: - expects numeric, got {t}.",
                    DiagnosticSeverity.Error,
                )
            )
        return t

    if rule == "call":
        fname = str(expr.children[0])
        args = (
            list(expr.children[1].children)
            if len(expr.children) > 1 and isinstance(expr.children[1], Tree)
            else []
        )
        sig = func_sigs.get(fname)
        if not sig:
            return None
        params, ret = sig
        for i, arg in enumerate(args):
            if i >= len(params):
                break
            expected = params[i][1]
            if not expected:
                continue
            actual = _infer_expr_type(arg, lookup_var_type, func_sigs, diags)
            if actual and not TypeCanon.are_compatible(expected, actual):
                diags.append(
                    _diag_from_node(
                        expr,
                        f"Type mismatch: call '{fname}' arg {i+1} expects {expected} got {actual}.",
                        DiagnosticSeverity.Error,
                    )
                )
        return ret
    return None


def _typecheck(tree: Tree) -> list[Diagnostic]:
    diags = []
    icons = _collect_icon_schemas(tree)
    mod_types = _collect_var_types(tree)
    sigs = _collect_function_sigs(tree)
    scope_stack = []

    def lookup(name):
        for s in reversed(scope_stack):
            if name in s:
                return s[name]
        return mod_types.get(name)

    def walk(node):
        if not isinstance(node, Tree):
            return

        if node.data == "block":
            dead = False
            for stmt in node.children:
                if dead and isinstance(stmt, Tree):
                    diags.append(
                        _diag_from_node(
                            stmt,
                            "Unreachable code after offer.",
                            DiagnosticSeverity.Warning,
                        )
                    )
                if isinstance(stmt, Tree) and stmt.data == "offer":
                    dead = True
                walk(stmt)
            return

        if node.data == "mystery_def":
            local_types = {}
            # (Simplistic param extraction for scope seeding)
            idx = 1
            if (
                idx < len(node.children)
                and isinstance(node.children[idx], Tree)
                and node.children[idx].data == "params"
            ):
                for p in node.children[idx].children:
                    if len(p.children) >= 2:
                        local_types[str(p.children[0])] = str(p.children[1])
            scope_stack.append(local_types)
            for c in node.children:
                walk(c)
            scope_stack.pop()
            return

        if node.data == "inscribe" and len(node.children) == 3:
            var, decl, expr = (
                str(node.children[0]),
                str(node.children[1]),
                node.children[2],
            )
            if scope_stack:
                scope_stack[-1][var] = decl
            actual = _infer_expr_type(expr, lookup, sigs, diags)
            if actual and not TypeCanon.are_compatible(decl, actual):
                diags.append(
                    _diag_from_node(
                        node,
                        f"Type mismatch: declared {decl} but assigned {actual}.",
                        DiagnosticSeverity.Error,
                    )
                )

        if node.data == "amend":
            target, val_node = node.children[0], node.children[1]
            actual = _infer_expr_type(val_node, lookup, sigs, diags)
            if actual and isinstance(target, Tree) and target.data == "mut_var":
                vname = str(target.children[0])
                decl = lookup(vname)
                if decl and not TypeCanon.are_compatible(decl, actual):
                    diags.append(
                        _diag_from_node(
                            node,
                            f"Type mismatch: '{vname}' is {decl} but amended with {actual}.",
                            DiagnosticSeverity.Error,
                        )
                    )

        # Check standalone expressions
        if node.data in (
            "call",
            "add",
            "sub",
            "mul",
            "div",
            "lt",
            "gt",
            "le",
            "ge",
            "neg",
        ):
            _infer_expr_type(node, lookup, sigs, diags)

        for c in node.children:
            walk(c)

    walk(tree)
    return diags


def validate(ls: LanguageServer, uri: str) -> None:
    doc = ls.workspace.get_document(uri)
    try:
        tree = get_parser().parse(doc.source)
        diags = _typecheck(tree)
    except Exception as e:
        line = getattr(e, "line", 1) - 1
        col = getattr(e, "column", 1) - 1
        diags = [_make_diag(line, col, str(e).split("\n")[0])]
    ls.publish_diagnostics(uri, diags)


@SERVER.feature(TEXT_DOCUMENT_DID_OPEN)
def did_open(ls, params):
    validate(ls, params.text_document.uri)


@SERVER.feature(TEXT_DOCUMENT_DID_CHANGE)
def did_change(ls, params):
    validate(ls, params.text_document.uri)


if __name__ == "__main__":
    SERVER.start_io()
