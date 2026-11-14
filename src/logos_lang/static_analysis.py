from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Iterable, List

from lark import Tree

from .types import TypeCanon


@dataclass(frozen=True)
class StaticTypeElisionPlan:
    bindings: Dict[str, str]


class StaticTypeAnalyzer:
    """Conservative pre-pass for eliding redundant global type checks.

    The analyzer only elides checks for globally declared variables when all
    observed assignments are statically inferred and type-compatible.

    Block statements open a lexical scope exactly as at runtime: declarations inside a
    block are locals, never global facts, and an ``amend`` resolves to the innermost
    binding. Function bodies are not walked: they always run with a non-empty type
    stack, where the runtime never elides checks.
    """

    def analyze(self, tree: Any) -> StaticTypeElisionPlan:
        if not isinstance(tree, Tree) or tree.data != "start":
            return StaticTypeElisionPlan(bindings={})

        self._declared_global: Dict[str, str] = {}
        self._eligible_global: Dict[str, str] = {}
        # Innermost-last stack of local scopes: name -> declared type (None if untyped).
        self._scopes: List[Dict[str, str | None]] = []

        self._walk_statements(tree.children)
        return StaticTypeElisionPlan(bindings=dict(self._eligible_global))

    def _walk_statements(self, statements: Iterable[Any]) -> None:
        for statement in statements:
            if isinstance(statement, Tree):
                self._walk_statement(statement)

    def _walk_child(self, node: Any) -> None:
        if isinstance(node, Tree):
            self._walk_statement(node)

    def _walk_statement(self, statement: Tree[Any]) -> None:
        rule = statement.data
        children = statement.children

        if rule == "inscribe":
            self._handle_inscribe(statement)
        elif rule == "amend":
            self._handle_amend(statement)
        elif rule == "block":
            self._scopes.append({})
            try:
                self._walk_statements(children)
            finally:
                self._scopes.pop()
        elif rule == "chant":
            self._walk_child(children[1] if len(children) > 1 else None)
        elif rule == "discernment":
            self._walk_child(children[1] if len(children) > 1 else None)
            self._walk_child(children[2] if len(children) > 2 else None)
        elif rule == "vigil":
            self._walk_child(children[0] if children else None)
            self._walk_child(children[2] if len(children) > 2 else None)
        elif rule == "contemplation":
            for clause in children[1:]:
                if isinstance(clause, Tree) and clause.data == "case_clause":
                    # A non-block case body runs in the enclosing scope, so walking it
                    # in the current scope matches runtime behavior.
                    self._walk_child(clause.children[1] if len(clause.children) > 1 else None)

    def _resolve_local(self, name: str) -> tuple[bool, str | None]:
        for scope in reversed(self._scopes):
            if name in scope:
                return True, scope[name]
        return False, None

    def _handle_inscribe(self, statement: Tree[Any]) -> None:
        children = statement.children
        if len(children) not in (2, 3):
            return
        name = str(children[0])
        declared_type = str(children[1]) if len(children) == 3 else None
        expr = children[-1]

        if self._scopes:
            self._scopes[-1][name] = declared_type
            return

        if declared_type is None:
            # Untyped re-inscribe of a typed global is still checked against its type.
            self._check_global_assignment(name, expr)
            return

        self._declared_global[name] = declared_type
        inferred = self._infer_expr_type(expr)
        if inferred is not None and TypeCanon.are_compatible(declared_type, inferred):
            self._eligible_global[name] = declared_type
        else:
            self._eligible_global.pop(name, None)

    def _handle_amend(self, statement: Tree[Any]) -> None:
        if len(statement.children) != 2:
            return

        target, value = statement.children
        if not isinstance(target, Tree) or target.data != "mut_var" or not target.children:
            return

        name = str(target.children[0])
        is_local, _ = self._resolve_local(name)
        if is_local:
            return
        self._check_global_assignment(name, value)

    def _check_global_assignment(self, name: str, value: Any) -> None:
        declared_type = self._declared_global.get(name)
        if not declared_type:
            return
        inferred = self._infer_expr_type(value)
        if inferred is None or not TypeCanon.are_compatible(declared_type, inferred):
            self._eligible_global.pop(name, None)

    def _infer_expr_type(self, node: Any) -> str | None:
        if not isinstance(node, Tree):
            return None

        rule = node.data

        if rule == "number":
            literal = str(node.children[0]) if node.children else "0"
            return "HolyFloat" if "." in literal else "HolyInt"

        if rule == "string":
            return "Text"

        if rule in {"verily", "nay", "eq", "ne", "lt", "gt", "le", "ge"}:
            return "Bool"

        if rule == "procession":
            return "Procession"

        if rule == "var":
            if not node.children:
                return None
            var_name = str(node.children[0])
            is_local, local_type = self._resolve_local(var_name)
            if is_local:
                return local_type
            return self._declared_global.get(var_name)

        if rule == "transfigure":
            if len(node.children) < 2:
                return None
            return str(node.children[1])

        if rule == "neg":
            base = self._infer_expr_type(node.children[0]) if node.children else None
            return base if base in TypeCanon.NUMERIC else None

        if rule in {"add", "sub", "mul", "div"}:
            if len(node.children) < 2:
                return None
            left = self._infer_expr_type(node.children[0])
            right = self._infer_expr_type(node.children[1])
            if left is None or right is None:
                return None
            return TypeCanon.resolve_binary_op(rule, left, right)

        if rule == "call":
            if not node.children:
                return None
            fn_name = str(node.children[0])
            known_return_types = {
                "measure": "HolyInt",
                "passage": "Text",
                "env": "Text",
                "__sys_env": "Text",
                "now": "HolyInt",
                "__sys_time": "HolyInt",
                "extract": None,
            }
            return known_return_types.get(fn_name)

        if rule == "supplicate":
            return "Text"

        if rule == "write_icon":
            if len(node.children) >= 1:
                return str(node.children[0])
            return None

        if rule == "atom":
            if not node.children:
                return None
            return self._infer_expr_type(node.children[0])

        return None
