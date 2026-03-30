from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Iterable

from lark import Tree

from .types import TypeCanon


@dataclass(frozen=True)
class StaticTypeElisionPlan:
    bindings: Dict[str, str]


class StaticTypeAnalyzer:
    """Conservative pre-pass for eliding redundant global type checks.

    The analyzer only elides checks for globally declared variables when all
    observed assignments are statically inferred and type-compatible.
    """

    def analyze(self, tree: Any) -> StaticTypeElisionPlan:
        if not isinstance(tree, Tree) or tree.data != "start":
            return StaticTypeElisionPlan(bindings={})

        self._declared_global: Dict[str, str] = {}
        self._eligible_global: Dict[str, str] = {}

        self._walk_statements(tree.children)
        return StaticTypeElisionPlan(bindings=dict(self._eligible_global))

    def _walk_statements(self, statements: Iterable[Any]) -> None:
        for statement in statements:
            if isinstance(statement, Tree):
                self._walk_statement(statement)

    def _walk_statement(self, statement: Tree[Any]) -> None:
        rule = statement.data

        if rule == "inscribe":
            self._handle_inscribe(statement)
            return

        if rule == "amend":
            self._handle_amend(statement)
            return

        if rule == "block":
            self._walk_statements(statement.children)
            return

        if rule == "chant":
            body = statement.children[1] if len(statement.children) > 1 else None
            if isinstance(body, Tree):
                self._walk_statement(body)
            return

        if rule == "discernment":
            then_branch = statement.children[1] if len(statement.children) > 1 else None
            else_branch = statement.children[2] if len(statement.children) > 2 else None
            if isinstance(then_branch, Tree):
                self._walk_statement(then_branch)
            if isinstance(else_branch, Tree):
                self._walk_statement(else_branch)
            return

        if rule == "vigil":
            try_branch = statement.children[0] if statement.children else None
            catch_branch = statement.children[2] if len(statement.children) > 2 else None
            if isinstance(try_branch, Tree):
                self._walk_statement(try_branch)
            if isinstance(catch_branch, Tree):
                self._walk_statement(catch_branch)
            return

        if rule == "contemplation":
            for clause in statement.children[1:]:
                if isinstance(clause, Tree) and clause.data == "case_clause":
                    body = clause.children[1] if len(clause.children) > 1 else None
                    if isinstance(body, Tree):
                        self._walk_statement(body)
            return

    def _handle_inscribe(self, statement: Tree[Any]) -> None:
        if len(statement.children) != 3:
            return

        name = str(statement.children[0])
        declared_type = str(statement.children[1])
        expr = statement.children[2]

        self._declared_global[name] = declared_type
        inferred = self._infer_expr_type(expr)

        if inferred is not None and TypeCanon.are_compatible(declared_type, inferred):
            self._eligible_global[name] = declared_type
        else:
            self._eligible_global.pop(name, None)

    def _handle_amend(self, statement: Tree[Any]) -> None:
        if len(statement.children) != 2:
            return

        target = statement.children[0]
        value = statement.children[1]

        if not isinstance(target, Tree) or target.data != "mut_var" or not target.children:
            return

        name = str(target.children[0])
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
            return self._declared_global.get(str(node.children[0]))

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
