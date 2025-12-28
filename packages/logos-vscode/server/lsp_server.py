from __future__ import annotations

import os
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

# Locate the shared runtime canon (logos.py) from the repo root.
SERVER_DIR = Path(__file__).resolve().parent
ROOT_DIR = SERVER_DIR.parents[2]
if str(ROOT_DIR) not in sys.path:
    sys.path.append(str(ROOT_DIR))

try:
    from logos import TypeCanon
except Exception as e:  # pragma: no cover - tooling bootstrap
    _fatal("LOGOS Iconostasis: Could not locate the Canon (logos.py).")
    raise


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
    """Collect annotated variable declarations (best-effort, flow-insensitive).

    Note: Logos has scoping/shadowing; the LSP does not attempt full scope tracking.
    This is a pragmatic approximation intended for early feedback.
    """
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


def _collect_function_sigs(tree: Tree) -> dict[str, tuple[list[tuple[str, str | None]], str | None]]:
    """Collect mystery function signatures (param types + return type) best-effort."""
    sigs: dict[str, tuple[list[tuple[str, str | None]], str | None]] = {}

    def walk(node: object) -> None:
        if not isinstance(node, Tree):
            return

        if node.data == "mystery_def":
            name = str(node.children[0])
            idx = 1
            params: list[tuple[str, str | None]] = []
            if idx < len(node.children) and isinstance(node.children[idx], Tree) and node.children[idx].data == "params":
                params_node = node.children[idx]
                for p in params_node.children:
                    if not isinstance(p, Tree) or p.data != "param":
                        continue
                    # param: NAME (":" NAME)?
                    param_name = str(p.children[0])
                    if len(p.children) >= 2:
                        params.append((param_name, str(p.children[1])))
                    else:
                        params.append((param_name, None))
                idx += 1

            return_type: str | None = None
            if idx < len(node.children) and isinstance(node.children[idx], Token) and node.children[idx].type == "NAME":
                return_type = str(node.children[idx])

            sigs[name] = (params, return_type)

        for c in node.children:
            walk(c)

    walk(tree)
    return sigs


def _infer_expr_type(
    expr: object,
    lookup_var_type: Callable[[str], str | None],
    func_sigs: dict[str, tuple[list[tuple[str, str | None]], str | None]],
    diags: list[Diagnostic],
) -> str | None:
    """Infer an expression type best-effort; appends diagnostics for obvious incompatibilities."""

    literal = _infer_literal_type(expr)
    if literal is not None:
        return literal

    if not isinstance(expr, Tree):
        return None

    rule = expr.data

    if rule == "var":
        name = str(expr.children[0])
        return lookup_var_type(name)

    if rule == "transfigure":
        # transfigure <expr> into NAME
        if len(expr.children) >= 2:
            return str(expr.children[1])
        return None

    if rule in ("add", "sub", "mul", "div", "eq", "ne", "lt", "gt", "le", "ge"):
        left_t = _infer_expr_type(expr.children[0], lookup_var_type, func_sigs, diags)
        right_t = _infer_expr_type(expr.children[1], lookup_var_type, func_sigs, diags)
        if left_t is None or right_t is None:
            return None

        result_type = TypeCanon.resolve_binary_op(rule, left_t, right_t)
        if result_type is None:
            op_word = {
                "add": "add",
                "sub": "subtract",
                "mul": "multiply",
                "div": "divide",
                "lt": "compare",
                "gt": "compare",
                "le": "compare",
                "ge": "compare",
                "eq": "compare",
                "ne": "compare",
            }.get(rule, "apply")
            diags.append(
                _diag_from_node(
                    expr,
                    f"Type mismatch: cannot {op_word} {left_t} and {right_t}.",
                    DiagnosticSeverity.Error,
                )
            )
            return None

        return result_type

    if rule == "neg":
        inner_t = _infer_expr_type(expr.children[0], lookup_var_type, func_sigs, diags)
        if inner_t and inner_t not in TypeCanon.NUMERIC:
            diags.append(
                _diag_from_node(
                    expr,
                    f"Type mismatch: unary '-' expects numeric, got {inner_t}.",
                    DiagnosticSeverity.Error,
                )
            )
            return None
        return inner_t

    if rule == "call":
        func_name = str(expr.children[0])
        args_node = expr.children[1] if len(expr.children) > 1 else None
        args: list[object] = []
        if isinstance(args_node, Tree) and args_node.data == "args":
            args = list(args_node.children)

        sig = func_sigs.get(func_name)
        if sig is None:
            return None
        params, ret_type = sig

        # Validate args against available param types.
        for i, arg_expr in enumerate(args):
            if i >= len(params):
                break
            expected = params[i][1]
            if not expected:
                continue
            actual = _infer_expr_type(arg_expr, lookup_var_type, func_sigs, diags)
            if actual and not TypeCanon.are_compatible(expected, actual):
                diags.append(
                    _diag_from_node(
                        expr,
                        f"Type mismatch: call '{func_name}' arg {i+1} expects {expected} but got {actual}.",
                        DiagnosticSeverity.Error,
                    )
                )

        return ret_type

    # Unknown/unsupported expression forms
    return None


def _typecheck(tree: Tree) -> list[Diagnostic]:
    diags: list[Diagnostic] = []
    icons = _collect_icon_schemas(tree)
    module_types = _collect_var_types(tree)
    func_sigs = _collect_function_sigs(tree)

    scope_stack: list[dict[str, str]] = []

    def lookup_var_type(name: str) -> str | None:
        for scope in reversed(scope_stack):
            if name in scope:
                return scope[name]
        return module_types.get(name)

    def walk(node: object) -> None:
        if not isinstance(node, Tree):
            return

        # Provide a tiny unreachable-code warning pass at block level.
        if node.data == "block":
            dead = False
            for stmt in node.children:
                if not isinstance(stmt, Tree):
                    continue

                if dead:
                    diags.append(
                        _diag_from_node(
                            stmt,
                            "Unreachable code: statement occurs after 'offer' in the same block.",
                            DiagnosticSeverity.Warning,
                        )
                    )
                    continue

                walk(stmt)
                if stmt.data == "offer":
                    dead = True
            return

        # Enter function scope (lexical-ish) for mystery bodies.
        if node.data == "mystery_def":
            local_types: dict[str, str] = {}

            # Seed param types if annotated.
            idx = 1
            if idx < len(node.children) and isinstance(node.children[idx], Tree) and node.children[idx].data == "params":
                params_node = node.children[idx]
                for p in params_node.children:
                    if not isinstance(p, Tree) or p.data != "param":
                        continue
                    if len(p.children) >= 2:
                        local_types[str(p.children[0])] = str(p.children[1])
                idx += 1

            # Skip optional return type token.
            if idx < len(node.children) and isinstance(node.children[idx], Token) and node.children[idx].type == "NAME":
                idx += 1

            # Body is the next child.
            body = node.children[idx] if idx < len(node.children) else None

            scope_stack.append(local_types)
            try:
                if body is not None:
                    walk(body)
            finally:
                scope_stack.pop()
            return

        # inscribe x: HolyInt = <literal>;
        if node.data == "inscribe" and len(node.children) == 3:
            var_name = str(node.children[0])
            declared = str(node.children[1])
            expr = node.children[2]
            # Record declared type in the current scope when inside a mystery.
            if scope_stack:
                scope_stack[-1][var_name] = declared
            else:
                module_types[var_name] = declared

            actual = _infer_expr_type(expr, lookup_var_type, func_sigs, diags)
            if actual and not TypeCanon.are_compatible(declared, actual):
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
            actual = _infer_expr_type(value_expr, lookup_var_type, func_sigs, diags)
            if actual and isinstance(target, Tree) and target.data == "mut_var":
                var_name = str(target.children[0])
                declared = lookup_var_type(var_name)
                if declared and not TypeCanon.are_compatible(declared, actual):
                    diags.append(
                        _diag_from_node(
                            node,
                            f"Type mismatch: '{var_name}' declared {declared} but amended with {actual}.",
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
                        actual = _infer_expr_type(expr, lookup_var_type, func_sigs, diags)
                        if expected and actual and not TypeCanon.are_compatible(expected, actual):
                            diags.append(
                                _diag_from_node(
                                    assign,
                                    f"Type mismatch: '{icon_name}.{field}' expects {expected} but got {actual}.",
                                    DiagnosticSeverity.Error,
                                )
                            )

        # Validate standalone call expressions when we can infer arg types.
        if node.data == "call":
            _infer_expr_type(node, lookup_var_type, func_sigs, diags)

        # Validate arithmetic/comparison expressions even when not assigned.
        if node.data in ("add", "sub", "mul", "div", "lt", "gt", "le", "ge", "neg"):
            _infer_expr_type(node, lookup_var_type, func_sigs, diags)

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
