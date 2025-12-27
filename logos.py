import ctypes
import os
import sys
from dataclasses import dataclass

from lark import Lark
from lark.visitors import Interpreter


GRAMMAR = r"""
    start: statement*

    statement: "behold" expr ";"                                 -> behold
             | "gift" NAME "=" expr ";"                          -> gift
             | "foreign" STRING "service" NAME "(" ")" ";"     -> foreign
             | "cycle" expr block "amen"                           -> cycle
             | "if" "(" expr ")" block "else" block "amen"        -> condition
             | expr ";"                                            -> expr_stmt

    block: "{" statement* "}"                                   -> block

    ?expr: equality

    ?equality: comparison
             | equality "==" comparison -> eq

    ?comparison: sum
               | comparison "<" sum -> lt

    ?sum: term
        | sum "+" term -> add
        | sum "-" term -> sub

    ?term: call

    ?call: NAME "(" args? ")" -> call
         | atom

    args: expr ("," expr)*

    atom: NUMBER  -> number
        | STRING  -> string
        | NAME    -> var
        | "(" expr ")"

    NAME: /[a-zA-Z_]\w*/
    STRING: /"[^"\\n]*"/
    NUMBER: /\d+(\.\d+)?/

    %import common.WS
    %ignore WS
    %ignore /#.*/
"""


@dataclass
class ForeignFunction:
    func: object
    restype: object


class LogosInterpreter(Interpreter):
    def __init__(self):
        self.variables: dict[str, object] = {}
        self._libs: dict[str, ctypes.CDLL] = {}

    def behold(self, tree):
        val = self.visit(tree.children[0])
        print(f"☩ {val}")

    def gift(self, tree):
        name = str(tree.children[0])
        val = self.visit(tree.children[1])
        self.variables[name] = val

    def expr_stmt(self, tree):
        self.visit(tree.children[0])

    def var(self, tree):
        name = str(tree.children[0])
        if name in self.variables:
            return self.variables[name]
        raise Exception(f"Heresy: Unknown spirit '{name}'")

    def number(self, tree):
        text = str(tree.children[0])
        if "." in text:
            return float(text)
        return float(text)

    def string(self, tree):
        return str(tree.children[0])[1:-1]

    def add(self, tree):
        return self.visit(tree.children[0]) + self.visit(tree.children[1])

    def sub(self, tree):
        return self.visit(tree.children[0]) - self.visit(tree.children[1])

    def eq(self, tree):
        return self.visit(tree.children[0]) == self.visit(tree.children[1])

    def lt(self, tree):
        return self.visit(tree.children[0]) < self.visit(tree.children[1])

    def block(self, tree):
        result = None
        for stmt in tree.children:
            result = self.visit(stmt)
        return result

    def condition(self, tree):
        cond_expr = tree.children[0]
        then_block = tree.children[1]
        else_block = tree.children[2]

        if self.visit(cond_expr):
            return self.visit(then_block)
        return self.visit(else_block)

    def cycle(self, tree):
        cond_node = tree.children[0]
        body_block = tree.children[1]

        while self.visit(cond_node):
            self.visit(body_block)

    def _platform_library_filename(self, lib_name: str) -> str:
        # If user passes an explicit filename (e.g. "msvcrt.dll"), respect it.
        if lib_name.lower().endswith((".dll", ".so", ".dylib")):
            return lib_name

        if os.name == "nt":
            return f"{lib_name}.dll"
        if sys.platform == "darwin":
            return f"lib{lib_name}.dylib"
        return f"lib{lib_name}.so"

    def foreign(self, tree):
        lib_name = str(tree.children[0])[1:-1]
        func_name = str(tree.children[1])

        lib_path = self._platform_library_filename(lib_name)

        try:
            lib = self._libs.get(lib_path)
            if lib is None:
                lib = ctypes.CDLL(lib_path)
                self._libs[lib_path] = lib

            func = getattr(lib, func_name)
            func.restype = ctypes.c_double

            self.variables[func_name] = ForeignFunction(func=func, restype=ctypes.c_double)
            print(f"[System] Linked with {lib_path}::{func_name}")
        except Exception as e:
            print(f"[Warning] Could not link {lib_path}: {e}")

    def call(self, tree):
        func_name = str(tree.children[0])
        args_node = tree.children[1] if len(tree.children) > 1 else None

        args: list[object] = []
        if args_node is not None:
            # args is a Tree("args", ...)
            for child in args_node.children:
                args.append(self.visit(child))

        callee = self.variables.get(func_name)
        if isinstance(callee, ForeignFunction):
            c_args: list[object] = []
            for a in args:
                if isinstance(a, (int, float)):
                    c_args.append(ctypes.c_double(float(a)))
                else:
                    raise Exception(f"Heresy: Foreign arguments must be numeric (got {type(a)})")
            return callee.func(*c_args)

        raise Exception(f"Unknown service: {func_name}")


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print("Usage: python logos.py <file.lg>")
        return 2

    with open(argv[1], "r", encoding="utf-8") as f:
        source = f.read()

    parser = Lark(GRAMMAR, parser="lalr")
    tree = parser.parse(source)

    soul = LogosInterpreter()
    soul.visit(tree)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
