import ctypes
import os
import sys
import time
from dataclasses import dataclass

from lark import Lark
from lark.visitors import Interpreter


GRAMMAR = r"""
    start: statement*

    statement: "behold" expr ";"                                          -> behold
             | "gift" NAME (":" NAME)? "=" expr ";"                   -> gift
             | "foreign" STRING "service" NAME "(" ")" ";"            -> foreign
             | "import" STRING ";"                                        -> import_lib
             | "cycle" expr block "amen"                                    -> cycle
             | "if" "(" expr ")" block "else" block "amen"                 -> condition
             | "try" block "repent" NAME block "amen"                        -> try_repent
             | ("service"|"ministry") NAME "(" params? ")" ("->" NAME)? block "amen" -> service_def
             | "structure" NAME "{" field_decl* "}" "amen"                  -> structure_def
             | "inspect" "(" expr ")" "{" case_clause+ "}" "amen"            -> inspect
             | "offer" expr ";"                                           -> offer
             | "pass" ";"                                                  -> pass_stmt
             | expr ";"                                                     -> expr_stmt

    block: "{" statement* "}"                                            -> block

    field_decl: NAME ":" NAME ";"

    params: param ("," param)*
    param: NAME (":" NAME)?

    case_clause: "case" pattern ":" case_body
    ?case_body: block
              | statement
    ?pattern: "_"                                                          -> wildcard
            | expr

    ?expr: equality

    ?equality: comparison
             | equality "==" comparison -> eq
             | equality "!=" comparison -> ne

    ?comparison: sum
               | comparison "<" sum  -> lt
               | comparison ">" sum  -> gt
               | comparison "<=" sum -> le
               | comparison ">=" sum -> ge

    ?sum: product
        | sum "+" product -> add
        | sum "-" product -> sub

    ?product: unary
            | product "*" unary -> mul
            | product "/" unary -> div

        ?unary: call
            | "witness" expr "as" NAME -> witness
          | "listen" expr            -> listen

    ?call: access
         | NAME "(" args? ")" -> call

    ?access: atom
           | access "." NAME -> get_attr

    args: expr ("," expr)*

    atom: NUMBER  -> number
        | STRING  -> string
        | "Verily" -> verily
        | "Nay"    -> nay
        | "new" NAME "{" assign_list? "}" -> new_struct
        | NAME    -> var
        | "(" expr ")"

    assign_list: assign ("," assign)* ","?
    assign: NAME "=" expr

    NAME: /[a-zA-Z_]\w*/
    STRING: /"[^"\n]*"/
    NUMBER: /\d+(\.\d+)?/

    %import common.WS
    %ignore WS
    %ignore /#.*/
    %ignore /\/\/.*/
"""


@dataclass
class ForeignFunction:
    func: object
    restype: object


@dataclass(frozen=True)
class UserFunction:
    name: str
    params: list[str]
    body: object


class _ReturnSignal(Exception):
    def __init__(self, value: object):
        super().__init__("return")
        self.value = value


class LogosInterpreter(Interpreter):
    def __init__(self, base_path: str | None = None):
        self._globals: dict[str, object] = {}
        self._stack: list[dict[str, object]] = []
        self._libs: dict[str, ctypes.CDLL] = {}
        self._imported: set[str] = set()
        self._struct_fields: dict[str, list[str]] = {}
        self._functions: dict[str, UserFunction] = {}

        self.base_path = os.path.abspath(base_path or os.getcwd())

        # --- PRE-ORDAINED SPIRITS (System Intrinsics) ---
        self._fds: dict[int, object] = {}
        self._next_fd = 3

        self._globals["__sys_time"] = lambda: int(time.time() * 1000)
        self._globals["__sys_env"] = lambda k: os.environ.get(str(k), "")
        self._globals["__sys_open"] = self._intrinsic_open
        self._globals["__sys_write"] = self._intrinsic_write
        self._globals["__sys_read"] = self._intrinsic_read
        self._globals["__sys_close"] = self._intrinsic_close
        self._globals["measure"] = lambda x: len(str(x))
        self._globals["passage"] = lambda s, start, l: str(s)[int(start) : int(start) + int(l)]

    def behold(self, tree):
        val = self.visit(tree.children[0])
        if isinstance(val, bool):
            print(f"☩ {'Verily' if val else 'Nay'}")
            return
        print(f"☩ {val}")

    def gift(self, tree):
        name = str(tree.children[0])
        # Optional type annotation is ignored.
        expr_idx = 2 if len(tree.children) == 3 else 1
        val = self.visit(tree.children[expr_idx])
        self._set_var(name, val)
        return val

    def expr_stmt(self, tree):
        return self.visit(tree.children[0])

    def var(self, tree):
        name = str(tree.children[0])
        for frame in reversed(self._stack):
            if name in frame:
                return frame[name]
        if name in self._globals:
            return self._globals[name]
        if name in self._functions:
            return self._functions[name]
        raise Exception(f"Heresy: Unknown spirit '{name}'")

    def number(self, tree):
        text = str(tree.children[0])
        return float(text) if "." in text else int(text)

    def atom(self, tree):
        if not tree.children:
            return None
        return self.visit(tree.children[0])

    def string(self, tree):
        return str(tree.children[0])[1:-1].replace("\\n", "\n")

    def verily(self, tree):
        return True

    def nay(self, tree):
        return False

    def add(self, tree):
        return self.visit(tree.children[0]) + self.visit(tree.children[1])

    def sub(self, tree):
        return self.visit(tree.children[0]) - self.visit(tree.children[1])

    def eq(self, tree):
        return self.visit(tree.children[0]) == self.visit(tree.children[1])

    def ne(self, tree):
        return self.visit(tree.children[0]) != self.visit(tree.children[1])

    def lt(self, tree):
        return self.visit(tree.children[0]) < self.visit(tree.children[1])

    def gt(self, tree):
        return self.visit(tree.children[0]) > self.visit(tree.children[1])

    def le(self, tree):
        return self.visit(tree.children[0]) <= self.visit(tree.children[1])

    def ge(self, tree):
        return self.visit(tree.children[0]) >= self.visit(tree.children[1])

    def mul(self, tree):
        return self.visit(tree.children[0]) * self.visit(tree.children[1])

    def div(self, tree):
        return self.visit(tree.children[0]) / self.visit(tree.children[1])

    def block(self, tree):
        last = None
        for stmt in tree.children:
            last = self.visit(stmt)
        return last

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

    def try_repent(self, tree):
        try_block = tree.children[0]
        err_name = str(tree.children[1])
        repent_block = tree.children[2]

        try:
            return self.visit(try_block)
        except _ReturnSignal:
            raise
        except Exception as e:
            self._set_var(err_name, str(e))
            return self.visit(repent_block)

    def offer(self, tree):
        val = self.visit(tree.children[0])
        raise _ReturnSignal(val)

    def pass_stmt(self, tree):
        return None

    def witness(self, tree):
        val = self.visit(tree.children[0])
        typ = str(tree.children[1])
        if typ in ("HolyInt", "Int"):
            return int(val)
        if typ in ("HolyFloat", "Float"):
            return float(val)
        if typ in ("Text", "String"):
            return str(val)
        return val

    def listen(self, tree):
        prompt = self.visit(tree.children[0])
        return input(str(prompt))

    def get_attr(self, tree):
        obj = self.visit(tree.children[0])
        name = str(tree.children[1])
        if isinstance(obj, dict):
            return obj.get(name)
        return getattr(obj, name)

    def wildcard(self, tree):
        return "__WILDCARD__"

    def inspect(self, tree):
        inspect_val = self.visit(tree.children[0])
        case_nodes = tree.children[1:]

        for case_node in case_nodes:
            # case_clause: pattern, body
            pattern_node = case_node.children[0]
            body_node = case_node.children[1]

            pattern_val = self.visit(pattern_node)
            if pattern_val == "__WILDCARD__" or inspect_val == pattern_val:
                return self.visit(body_node)

        return None

    def case_clause(self, tree):
        # Container node; handled in inspect().
        return tree

    def structure_def(self, tree):
        name = str(tree.children[0])
        fields: list[str] = []
        for child in tree.children[1:]:
            # field_decl: NAME ':' TYPE ';'
            if hasattr(child, "children") and child.children:
                fields.append(str(child.children[0]))
        self._struct_fields[name] = fields
        return None

    def assign(self, tree):
        return (str(tree.children[0]), self.visit(tree.children[1]))

    def assign_list(self, tree):
        return [self.visit(c) for c in tree.children]

    def new_struct(self, tree):
        name = str(tree.children[0])
        assigns = []
        if len(tree.children) > 1:
            assigns = self.visit(tree.children[1])
        obj: dict[str, object] = {"__type__": name}
        for k, v in assigns:
            obj[k] = v
        return obj

    def import_lib(self, tree):
        filename = str(tree.children[0])[1:-1]

        # Resolve relative to the entry file directory.
        path = filename
        if not os.path.isabs(path):
            path = os.path.join(self.base_path, path)
        path = os.path.abspath(path)

        if path in self._imported:
            return None
        self._imported.add(path)

        if not os.path.exists(path):
            raise Exception(f"Import Error: scripture not found: {filename}")

        with open(path, "r", encoding="utf-8") as f:
            source = f.read()

        parser = Lark(GRAMMAR, parser="lalr")
        imported_tree = parser.parse(source)
        return self.visit(imported_tree)

    def service_def(self, tree):
        # statement rule includes ("service"|"ministry") as literals; Lark does not
        # necessarily keep that literal token in the tree children.
        # Children layout (typical):
        # 0: NAME (function name)
        # 1: params? (Tree)
        # 2: return type? (Token NAME)
        # last: block
        name = str(tree.children[0])

        idx = 1
        params: list[str] = []
        if idx < len(tree.children) and getattr(tree.children[idx], "data", None) == "params":
            for p in tree.children[idx].children:
                params.append(str(p.children[0]))
            idx += 1

        # Optional return type is ignored.
        if idx < len(tree.children) and getattr(tree.children[idx], "type", None) == "NAME":
            idx += 1

        body = tree.children[idx]
        self._functions[name] = UserFunction(name=name, params=params, body=body)
        return None

    def _platform_library_filename(self, lib_name: str) -> str:
        # If user passes an explicit filename (e.g. "msvcrt.dll"), respect it.
        if lib_name.lower().endswith((".dll", ".so", ".dylib")):
            return lib_name

        if os.name == "nt":
            return f"{lib_name}.dll"
        if sys.platform == "darwin":
            return f"lib{lib_name}.dylib"
        return f"lib{lib_name}.so"

    def _intrinsic_open(self, path, mode):
        try:
            p = str(path)
            if not os.path.isabs(p):
                p = os.path.join(self.base_path, p)

            m = mode
            if isinstance(m, str):
                mode_int = int(m)
            else:
                mode_int = int(m)
            modes = {0: "r", 1: "w", 2: "a"}
            py_mode = modes.get(mode_int, "r")
            f = open(p, py_mode, encoding="utf-8" if "b" not in py_mode else None)

            fd = self._next_fd
            self._next_fd += 1
            self._fds[fd] = f
            return fd
        except Exception:
            return 0

    def _intrinsic_write(self, fd, content):
        try:
            fd_int = int(fd)
            f = self._fds.get(fd_int)
            if f is None:
                return False
            f.write(str(content))
            f.flush()
            return True
        except Exception:
            return False

    def _intrinsic_read(self, fd, length):
        try:
            fd_int = int(fd)
            f = self._fds.get(fd_int)
            if f is None:
                return ""
            return f.read(int(length))
        except Exception:
            return ""

    def _intrinsic_close(self, fd):
        try:
            fd_int = int(fd)
            f = self._fds.pop(fd_int, None)
            if f is not None:
                f.close()
        except Exception:
            return None

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

            self._globals[func_name] = ForeignFunction(func=func, restype=ctypes.c_double)
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

        callee = self._resolve_name(func_name)

        if isinstance(callee, UserFunction):
            return self._call_user_function(callee, args)

        if callable(callee):
            return callee(*args)

        if isinstance(callee, ForeignFunction):
            c_args: list[object] = []
            for a in args:
                if isinstance(a, (int, float)):
                    c_args.append(ctypes.c_double(float(a)))
                else:
                    raise Exception(f"Heresy: Foreign arguments must be numeric (got {type(a)})")
            return callee.func(*c_args)

        raise Exception(f"Unknown service: {func_name}")

    def _resolve_name(self, name: str) -> object:
        for frame in reversed(self._stack):
            if name in frame:
                return frame[name]
        if name in self._globals:
            return self._globals[name]
        if name in self._functions:
            return self._functions[name]
        raise Exception(f"Heresy: Unknown spirit '{name}'")

    def _set_var(self, name: str, value: object) -> None:
        if self._stack:
            self._stack[-1][name] = value
        else:
            self._globals[name] = value

    def _call_user_function(self, fn: UserFunction, args: list[object]) -> object:
        if len(args) != len(fn.params):
            raise Exception(f"Invocation Error: {fn.name} expects {len(fn.params)} args but got {len(args)}")

        frame: dict[str, object] = {}
        for p, v in zip(fn.params, args, strict=True):
            frame[p] = v

        self._stack.append(frame)
        try:
            try:
                result = self.visit(fn.body)
                return result
            except _ReturnSignal as r:
                return r.value
        finally:
            self._stack.pop()


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print("Usage: python logos.py <file.lg>")
        return 2

    entry_path = os.path.abspath(argv[1])
    base_dir = os.path.dirname(entry_path)

    with open(entry_path, "r", encoding="utf-8") as f:
        source = f.read()

    parser = Lark(GRAMMAR, parser="lalr")
    tree = parser.parse(source)

    soul = LogosInterpreter(base_path=base_dir)
    soul.visit(tree)

    # If an entrypoint exists, run it.
    if "main" in soul._functions:
        soul._call_user_function(soul._functions["main"], [])
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
