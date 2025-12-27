import ctypes
import os
import sys
import time
from dataclasses import dataclass

from lark import Lark
from lark.visitors import Interpreter


GRAMMAR = r"""
    start: statement*

    // --- LITURGY (Statements) ---
    // Creation
    statement: "proclaim" expr ";"                                   -> proclaim
             | "inscribe" NAME (":" NAME)? "=" expr ";"              -> inscribe

             // Mutation (NEW: For lists, objects, and re-assignment)
             | "amend" mutable "=" expr ";"                          -> amend

             // Flow
             | "apocrypha" STRING "mystery" NAME "(" ")" ";"         -> apocrypha
             | "tradition" STRING ";"                                -> tradition
             | "chant" expr block "amen"                             -> chant
             | "discern" "(" expr ")" block "otherwise" block "amen" -> discernment
             | "vigil" block "confess" NAME block "amen"             -> vigil
             | "mystery" NAME "(" params? ")" ("->" NAME)? block "amen" -> mystery_def
             | "icon" NAME "{" field_decl* "}" "amen"                -> icon_def
             | "contemplate" "(" expr ")" "{" case_clause+ "}" "amen" -> contemplation
             | "offer" expr ";"                                      -> offer
             | "silence" ";"                                         -> silence
             | expr ";"                                              -> expr_stmt

    block: "{" statement* "}"                                        -> block

    // --- STRUCTURES ---
    field_decl: NAME ":" NAME ";"
    params: param ("," param)*
    param: NAME (":" NAME)?

    // --- CONTEMPLATION ---
    case_clause: "aspect" pattern ":" case_body
    ?case_body: block | statement
    ?pattern: "_" -> wildcard | expr

    // --- EXPRESSIONS & DOGMA ---
    ?expr: equality

    ?equality: comparison
             | equality "is" comparison               -> eq
             | equality "is" "not" comparison         -> ne

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

    ?unary: "-" unary                          -> neg
          | call
          | "transfigure" expr "into" NAME     -> transfigure
          | "supplicate" expr                  -> supplicate

    ?call: access
         | NAME "(" args? ")" -> call

        // --- ACCESS & MUTATION ---
        // 'access' is for reading (expressions)
        ?access: atom
            | access "." NAME        -> get_attr
            | access "[" expr "]"    -> get_item

        // 'mutable' is for writing (assignments)
        ?mutable: NAME                  -> mut_var
             | mutable "." NAME      -> mut_attr
             | mutable "[" expr "]"  -> mut_item

    args: expr ("," expr)*

    atom: NUMBER  -> number
        | STRING  -> string
        | "Verily" -> verily
        | "Nay"    -> nay
        | "[" expr ("," expr)* "]"          -> procession  // <--- NEW: Lists
        | "write" NAME "{" assign_list? "}" -> write_icon
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
        import re

        self._re_icon_name = re.compile(r"^[A-Z][A-Za-z0-9_]*$")
        self._re_mystery_name = re.compile(r"^[a-z][a-z0-9_]*$")

        self._globals: dict[str, object] = {}
        self._stack: list[dict[str, object]] = []
        self._libs: dict[str, ctypes.CDLL] = {}
        self._imported: set[str] = set()
        self._icon_fields: dict[str, list[str]] = {}
        self._functions: dict[str, UserFunction] = {}

        self.base_path = os.path.abspath(base_path or os.getcwd())

        # --- THE LIMIT OF HUMILITY ---
        self._call_depth = 0
        self._max_depth = 1000

        # --- PRE-ORDAINED SPIRITS (System Intrinsics) ---
        self._fds: dict[int, object] = {}
        self._next_fd = 3

        # Time and Environment
        self._globals["now"] = lambda: int(time.time() * 1000)
        self._globals["env"] = lambda k: os.environ.get(str(k), "")
        # Back-compat names
        self._globals["__sys_time"] = self._globals["now"]
        self._globals["__sys_env"] = self._globals["env"]

        self._globals["__sys_open"] = self._intrinsic_open
        self._globals["__sys_write"] = self._intrinsic_write
        self._globals["__sys_read"] = self._intrinsic_read
        self._globals["__sys_close"] = self._intrinsic_close

        # Measurements / list handling
        self._globals["measure"] = self._intrinsic_measure
        self._globals["append"] = self._intrinsic_append
        self._globals["adorn"] = self._intrinsic_adorn
        self._globals["extract"] = self._intrinsic_extract
        self._globals["purge"] = self._intrinsic_purge
        self._globals["passage"] = lambda s, start, l: str(s)[int(start) : int(start) + int(l)]

        # 1. System Control
        self._globals["__sys_sleep"] = lambda ms: time.sleep(float(ms) / 1000.0)
        self._globals["__sys_exit"] = lambda code: sys.exit(int(code))

        # 2. String/Type Sparks
        self._globals["__sys_ord"] = lambda s: ord(str(s)[0]) if str(s) else 0
        self._globals["__sys_chr"] = lambda n: chr(int(n))
        self._globals["__sys_str"] = lambda x: str(x)

        # Expose raw CLI arguments as a Procession.
        # sys.argv[2:] are arguments after the filename.
        args = sys.argv[2:] if len(sys.argv) > 2 else []
        self._globals["argv"] = list(args)

    def proclaim(self, tree):
        val = self.visit(tree.children[0])
        if isinstance(val, bool):
            print(f"☩ {'Verily' if val else 'Nay'}")
            return
        print(f"☩ {val}")

    def inscribe(self, tree):
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
        if name in ("None", "Void"):
            return None
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
        left = self.visit(tree.children[0])
        right = self.visit(tree.children[1])

        if isinstance(left, str) or isinstance(right, str):
            return str(left) + str(right)
        if isinstance(left, list) and isinstance(right, list):
            return left + right
        return left + right

    def sub(self, tree):
        return self.visit(tree.children[0]) - self.visit(tree.children[1])

    def neg(self, tree):
        return -self.visit(tree.children[0])

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

    def discernment(self, tree):
        cond_expr = tree.children[0]
        then_block = tree.children[1]
        else_block = tree.children[2]

        if self.visit(cond_expr):
            return self.visit(then_block)
        return self.visit(else_block)

    def chant(self, tree):
        cond_node = tree.children[0]
        body_block = tree.children[1]

        while self.visit(cond_node):
            self.visit(body_block)

    def vigil(self, tree):
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

    def silence(self, tree):
        return None

    def transfigure(self, tree):
        val = self.visit(tree.children[0])
        typ = str(tree.children[1])
        if typ in ("HolyInt", "Int"):
            return int(val)
        if typ in ("HolyFloat", "Float"):
            return float(val)
        if typ in ("Text", "String"):
            return str(val)
        return val

    def supplicate(self, tree):
        prompt = self.visit(tree.children[0])
        return input(str(prompt))

    def get_attr(self, tree):
        obj = self.visit(tree.children[0])
        name = str(tree.children[1])
        if isinstance(obj, dict):
            return obj.get(name)
        return getattr(obj, name)

    def procession(self, tree):
        return [self.visit(child) for child in tree.children]

    def get_item(self, tree):
        container = self.visit(tree.children[0])
        idx_val = self.visit(tree.children[1])

        try:
            if isinstance(container, list):
                return container[int(idx_val)]
            if isinstance(container, str):
                return container[int(idx_val)]
            if isinstance(container, dict):
                return container[idx_val]
            if hasattr(container, "__getitem__"):
                return container[idx_val]
        except Exception:
            pass
        raise Exception(f"Anathema: Cannot seek index {idx_val} in {type(container)}")

    def amend(self, tree):
        target_node = tree.children[0]
        value = self.visit(tree.children[1])
        self._perform_mutation(target_node, value)
        return None

    def _eval_mutable(self, node) -> object:
        rule = getattr(node, "data", None)

        if rule == "mut_var":
            name = str(node.children[0])
            return self._resolve_name(name)

        if rule == "mut_item":
            container = self._eval_mutable(node.children[0])
            index = self.visit(node.children[1])
            try:
                if isinstance(container, list):
                    return container[int(index)]
                if isinstance(container, dict):
                    return container[index]
                if isinstance(container, str):
                    return container[int(index)]
                return container[index]
            except Exception as e:
                raise Exception(f"Anathema: Cannot seek index {index} in {type(container)}") from e

        if rule == "mut_attr":
            container = self._eval_mutable(node.children[0])
            name = str(node.children[1])
            if isinstance(container, dict):
                return container.get(name)
            return getattr(container, name)

        # Fallback: if passed an expression accidentally, evaluate it normally.
        return self.visit(node)

    def _perform_mutation(self, node, value) -> None:
        rule = getattr(node, "data", None)

        if rule == "mut_var":
            name = str(node.children[0])
            self._set_var(name, value)
            return

        if rule == "mut_item":
            container = self._eval_mutable(node.children[0])
            index = self.visit(node.children[1])
            if isinstance(container, list):
                container[int(index)] = value
                return
            if isinstance(container, dict):
                container[index] = value
                return
            raise Exception("Heresy: Cannot amend an immutable spirit.")

        if rule == "mut_attr":
            container = self._eval_mutable(node.children[0])
            name = str(node.children[1])
            if isinstance(container, dict):
                container[name] = value
                return
            setattr(container, name, value)
            return

        raise Exception(f"Schism: Cannot amend target of type '{rule}'")

    def wildcard(self, tree):
        return "__WILDCARD__"

    def contemplation(self, tree):
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
        # Container node; handled in contemplation().
        return tree

    def icon_def(self, tree):
        name = str(tree.children[0])
        if not self._re_icon_name.fullmatch(name):
            raise Exception(
                f"Canon Error: Icons must be Capitalized (e.g., Saint). Got '{name}'"
            )
        fields: list[str] = []
        for child in tree.children[1:]:
            # field_decl: NAME ':' TYPE ';'
            if hasattr(child, "children") and child.children:
                fields.append(str(child.children[0]))
        self._icon_fields[name] = fields
        return None

    def assign(self, tree):
        return (str(tree.children[0]), self.visit(tree.children[1]))

    def assign_list(self, tree):
        return [self.visit(c) for c in tree.children]

    def write_icon(self, tree):
        name = str(tree.children[0])
        assigns = []
        if len(tree.children) > 1:
            assigns = self.visit(tree.children[1])
        obj: dict[str, object] = {"__icon__": name}
        for k, v in assigns:
            obj[k] = v
        return obj

    def tradition(self, tree):
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
            raise Exception(f"Schism: Tradition not found: {filename}")

        with open(path, "r", encoding="utf-8") as f:
            source = f.read()

        parser = Lark(GRAMMAR, parser="lalr")
        imported_tree = parser.parse(source)
        return self.visit(imported_tree)

    def mystery_def(self, tree):
        # The grammar defines mysteries; optional param type and return type are ignored.
        # Children layout (typical):
        # 0: NAME (function name)
        # 1: params? (Tree)
        # 2: return type? (Token NAME)
        # last: block
        name = str(tree.children[0])

        if not self._re_mystery_name.fullmatch(name):
            raise Exception(
                f"Canon Error: Mysteries must be snake_case (e.g., main, recursive_chant). Got '{name}'"
            )

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
            n = int(length)
            if n < 0:
                return f.read()
            return f.read(n)
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

    def apocrypha(self, tree):
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
            print(f"[System] Apocrypha bound: {lib_path}::{func_name}")
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
            if self._call_depth >= self._max_depth:
                raise Exception("Pride: Recursion depth exceeded. Humility is required.")
            self._call_depth += 1
            try:
                return callee(*args)
            finally:
                self._call_depth -= 1

        if isinstance(callee, ForeignFunction):
            c_args: list[object] = []
            for a in args:
                if isinstance(a, (int, float)):
                    c_args.append(ctypes.c_double(float(a)))
                else:
                    raise Exception(f"Heresy: Foreign arguments must be numeric (got {type(a)})")
            if self._call_depth >= self._max_depth:
                raise Exception("Pride: Recursion depth exceeded. Humility is required.")
            self._call_depth += 1
            try:
                return callee.func(*c_args)
            finally:
                self._call_depth -= 1

        raise Exception(f"Anathema: Unknown mystery '{func_name}'")

    def _resolve_name(self, name: str) -> object:
        for frame in reversed(self._stack):
            if name in frame:
                return frame[name]
        if name in self._globals:
            return self._globals[name]
        if name in self._functions:
            return self._functions[name]
        raise Exception(f"Anathema: Unknown spirit '{name}'")

    def _set_var(self, name: str, value: object) -> None:
        if self._stack:
            self._stack[-1][name] = value
        else:
            self._globals[name] = value

    def _call_user_function(self, fn: UserFunction, args: list[object]) -> object:
        if len(args) != len(fn.params):
            raise Exception(f"Invocation Error: {fn.name} expects {len(fn.params)} args but got {len(args)}")

        if self._call_depth >= self._max_depth:
            raise Exception("Pride: Recursion depth exceeded. Humility is required.")

        self._call_depth += 1

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
            self._call_depth -= 1

    def _intrinsic_measure(self, x):
        if x is None:
            return 0
        if isinstance(x, (str, list, dict)):
            return len(x)
        return 0

    def _intrinsic_append(self, xs, item):
        if not isinstance(xs, list):
            raise Exception(f"Schism: append expects a Procession (list), got {type(xs)}")
        xs.append(item)
        return xs

    def _intrinsic_adorn(self, lst, item):
        if isinstance(lst, list):
            lst.append(item)
            return None
        raise Exception(f"Schism: adorn expects a Procession (list), got {type(lst)}")

    def _intrinsic_extract(self, lst):
        if isinstance(lst, list) and lst:
            return lst.pop()
        return None

    def _intrinsic_purge(self, lst):
        if isinstance(lst, list):
            lst.clear()
            return None
        raise Exception(f"Schism: purge expects a Procession (list), got {type(lst)}")


def main(argv: list[str]) -> int:
    soul = LogosInterpreter()

    # CASE 1: The Interactive Confessional (No args)
    if len(argv) < 2:
        run_confessional(soul)
        return 0

    # CASE 2: The Liturgy (File execution)
    entry_path = os.path.abspath(argv[1])
    base_dir = os.path.dirname(entry_path)
    soul.base_path = base_dir

    with open(entry_path, "r", encoding="utf-8") as f:
        source = f.read()

    try:
        parser = Lark(GRAMMAR, parser="lalr")
        tree = parser.parse(source)
        soul.visit(tree)

        # If an entrypoint exists, run it.
        if "main" in soul._functions:
            soul._call_user_function(soul._functions["main"], [])
    except Exception as e:
        print(f"☨ FATAL ERROR ☨\nThe liturgy could not be completed: {e}")
        return 1

    return 0


def run_confessional(soul: LogosInterpreter):
    print("☩ Logos Interactive Confessional v1.0 ☩")
    print("☩ Type 'silence;' to sit in quietude, or 'depart(0);' to leave.")

    # Execute one statement at a time.
    repl_parser = Lark(GRAMMAR, parser="lalr", start="statement")

    while True:
        try:
            text = input(">> ")
            if not text.strip():
                continue

            if text.strip() in ("exit", "quit"):
                break

            tree = repl_parser.parse(text)
            result = soul.visit(tree)
            if result is not None:
                print(f"=> {result}")

        except _ReturnSignal as r:
            print(f"=> {r.value}")
        except SystemExit:
            break
        except KeyboardInterrupt:
            break
        except Exception as e:
            print(f"Anathema: {e}")


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
