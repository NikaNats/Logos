import ctypes
import os
import sys
import time
import re
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Set, Union, TextIO

from lark import Lark
from lark.visitors import Interpreter

# ==========================================
# 1. Grammar & Constants
# ==========================================

LOGOS_GRAMMAR = r"""
    start: statement*

    // --- LITURGY (Statements) ---
    statement: "proclaim" expr ";"                                   -> proclaim
             | "inscribe" NAME (":" NAME)? "=" expr ";"              -> inscribe
             | "amend" mutable "=" expr ";"                          -> amend
             | "apocrypha" STRING "mystery" NAME "(" params? ")" ("->" NAME)? ";" -> apocrypha
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

    field_decl: NAME ":" NAME ";"
    params: param ("," param)*
    param: NAME (":" NAME)?

    case_clause: "aspect" pattern ":" case_body
    ?case_body: block | statement
    ?pattern: "_" -> wildcard | expr

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

    ?access: atom
            | access "." NAME        -> get_attr
            | access "[" expr "]"    -> get_item

    ?mutable: NAME                  -> mut_var
             | mutable "." NAME      -> mut_attr
             | mutable "[" expr "]"  -> mut_item

    args: expr ("," expr)*

    atom: NUMBER  -> number
        | STRING  -> string
        | "Verily" -> verily
        | "Nay"    -> nay
        | "[" expr ("," expr)* "]"          -> procession
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

# ==========================================
# 2. Domain Models & Exceptions
# ==========================================

class LogosError(Exception):
    """Base exception for the runtime."""
    pass

class ReturnSignal(Exception):
    """Control flow signal for returning values from functions."""
    def __init__(self, value: Any):
        self.value = value

@dataclass
class ForeignFunction:
    """Represents a bound C-library function."""
    func: Any
    restype: Any
    argtypes: List[Any]

@dataclass(frozen=True)
class UserFunction:
    """Represents a function defined in Logos."""
    name: str
    params: List[str]
    body: Any

# ==========================================
# 3. Component Managers (The "Spirits")
# ==========================================

class ScopeManager:
    """
    Manages variables, globals, and the call stack.
    Implements variable resolution strategy (Local -> Global -> Builtin).
    """
    def __init__(self):
        self.globals: Dict[str, Any] = {}
        self.stack: List[Dict[str, Any]] = []
        
    def push_frame(self, frame: Dict[str, Any]) -> None:
        self.stack.append(frame)

    def pop_frame(self) -> None:
        if self.stack:
            self.stack.pop()

    def get(self, name: str) -> Any:
        # Check Stack (Local scopes)
        for frame in reversed(self.stack):
            if name in frame:
                return frame[name]
        # Check Globals
        if name in self.globals:
            return self.globals[name]
        
        raise LogosError(f"Heresy: Unknown spirit '{name}'")

    def set(self, name: str, value: Any) -> None:
        # Update existing in Stack
        for frame in reversed(self.stack):
            if name in frame:
                frame[name] = value
                return
        # Update existing in Globals
        if name in self.globals:
            self.globals[name] = value
            return
        
        # Define new: if in function, local; otherwise global
        if self.stack:
            self.stack[-1][name] = value
        else:
            self.globals[name] = value

    def register_builtin(self, name: str, value: Any) -> None:
        self.globals[name] = value


class FFIManager:
    """
    Handles loading shared libraries and marshalling types (Apocrypha).
    """
    def __init__(self):
        self.libs: Dict[str, ctypes.CDLL] = {}

    def get_ctype(self, type_name: str) -> Any:
        mapping = {
            "HolyFloat": ctypes.c_double, "Float": ctypes.c_double, "Double": ctypes.c_double,
            "HolyInt": ctypes.c_longlong, "Int": ctypes.c_longlong,
            "Bool": ctypes.c_bool, "Verily": ctypes.c_bool, "Nay": ctypes.c_bool,
            "Text": ctypes.c_char_p, "String": ctypes.c_char_p
        }
        return mapping.get(type_name, ctypes.c_double)

    def load_library(self, lib_name: str) -> str:
        if lib_name.lower().endswith((".dll", ".so", ".dylib")):
            filename = lib_name
        elif os.name == "nt":
            filename = f"{lib_name}.dll"
        elif sys.platform == "darwin":
            filename = f"lib{lib_name}.dylib"
        else:
            filename = f"lib{lib_name}.so"

        if filename not in self.libs:
            try:
                self.libs[filename] = ctypes.CDLL(filename)
            except OSError as e:
                raise LogosError(f"Schism: Could not bind Apocrypha '{filename}': {e}")
        
        return filename

    def bind_function(self, lib_name: str, func_name: str, arg_types: List[str], ret_type: str) -> ForeignFunction:
        lib = self.libs[self.load_library(lib_name)]
        func = getattr(lib, func_name)
        
        c_restype = self.get_ctype(ret_type)
        c_argtypes = [self.get_ctype(t) for t in arg_types]
        
        func.restype = c_restype
        func.argtypes = c_argtypes
        
        return ForeignFunction(func, c_restype, c_argtypes)

    def marshal_args(self, args: List[Any], definition: ForeignFunction) -> List[Any]:
        c_args = []
        for val, c_type in zip(args, definition.argtypes):
            if c_type == ctypes.c_char_p:
                if isinstance(val, (bytes, bytearray)):
                    c_args.append(bytes(val))
                else:
                    c_args.append(str(val).encode("utf-8"))
            elif c_type == ctypes.c_double:
                c_args.append(float(val))
            elif c_type == ctypes.c_longlong:
                c_args.append(int(val))
            else:
                c_args.append(val)
        return c_args

    @staticmethod
    def infer_ctype_from_value(val: Any) -> Any:
        # Heuristic inference when the apocrypha declaration omits arg types.
        # Default numeric values to double, matching common C library signatures.
        if isinstance(val, (bytes, bytearray, str)):
            return ctypes.c_char_p
        if isinstance(val, bool):
            return ctypes.c_bool
        if isinstance(val, (int, float)):
            return ctypes.c_double
        return ctypes.c_double


class StdLib:
    """
    Registry of Standard Library functions (System Intrinsics).
    """
    def __init__(self, base_path: str):
        self.base_path = base_path
        self._fds: Dict[int, TextIO] = {}
        self._next_fd = 3

    def register_into(self, scope: ScopeManager):
        # Time & Env
        scope.register_builtin("now", lambda: int(time.time() * 1000))
        scope.register_builtin("env", lambda k: os.environ.get(str(k), ""))
        
        # System control
        scope.register_builtin("__sys_sleep", lambda ms: time.sleep(float(ms) / 1000.0))
        scope.register_builtin("__sys_exit", lambda c: sys.exit(int(c)))
        
        # IO
        scope.register_builtin("__sys_open", self._open)
        scope.register_builtin("__sys_close", self._close)
        scope.register_builtin("__sys_write", self._write)
        scope.register_builtin("__sys_read", self._read)
        
        # Lists
        scope.register_builtin("measure", self._measure)
        scope.register_builtin("append", self._append)
        scope.register_builtin("extract", self._extract)
        scope.register_builtin("purge", self._purge)
        
        # Types
        scope.register_builtin("__sys_str", str)
        scope.register_builtin("argv", sys.argv[2:] if len(sys.argv) > 2 else [])

    def _open(self, path: str, mode: Union[int, str]) -> int:
        try:
            abs_path = os.path.abspath(os.path.join(self.base_path, str(path)))
            mode_str = {0: "r", 1: "w", 2: "a"}.get(int(mode), "r")
            fd = self._next_fd
            self._fds[fd] = open(abs_path, mode_str, encoding="utf-8")
            self._next_fd += 1
            return fd
        except Exception:
            return 0

    def _close(self, fd: int):
        f = self._fds.pop(int(fd), None)
        if f: f.close()

    def _write(self, fd: int, content: str):
        f = self._fds.get(int(fd))
        if f:
            f.write(str(content))
            f.flush()
            return True
        return False

    def _read(self, fd: int, length: int):
        f = self._fds.get(int(fd))
        if not f: return ""
        return f.read() if int(length) < 0 else f.read(int(length))

    @staticmethod
    def _measure(x: Any) -> int:
        return len(x) if hasattr(x, '__len__') else 0

    @staticmethod
    def _append(lst: List, item: Any):
        if isinstance(lst, list): lst.append(item)
        return lst

    @staticmethod
    def _extract(lst: List):
        return lst.pop() if isinstance(lst, list) and lst else None

    @staticmethod
    def _purge(lst: List):
        if isinstance(lst, list): lst.clear()

# ==========================================
# 4. The Interpreter (AST Visitor)
# ==========================================

class LogosInterpreter(Interpreter):
    def __init__(self, base_path: Optional[str] = None):
        self.base_path = os.path.abspath(base_path or os.getcwd())
        
        # Helpers
        self.scope = ScopeManager()
        self.ffi = FFIManager()
        self.stdlib = StdLib(self.base_path)
        
        # State
        self.stdlib.register_into(self.scope)
        self._imported_files: Set[str] = set()
        self._recursion_depth = 0
        self._max_recursion = 1000

        # Validators
        self._re_icon = re.compile(r"^[A-Z][A-Za-z0-9_]*$")
        self._re_func = re.compile(r"^[a-z][a-z0-9_]*$")

    # --- Root Statements ---
    
    def proclaim(self, tree):
        val = self.visit(tree.children[0])
        prefix = "Verily" if val is True else "Nay" if val is False else str(val)
        print(f"☩ {prefix}")

    def inscribe(self, tree):
        name = str(tree.children[0])
        expr_idx = 2 if len(tree.children) == 3 else 1
        val = self.visit(tree.children[expr_idx])
        self.scope.set(name, val)
        return val

    def amend(self, tree):
        target_node, value_node = tree.children
        value = self.visit(value_node)
        self._perform_mutation(target_node, value)

    def expr_stmt(self, tree):
        return self.visit(tree.children[0])

    # --- Flow Control ---

    def block(self, tree):
        result = None
        for stmt in tree.children:
            result = self.visit(stmt)
        return result

    def discernment(self, tree):
        condition, then_block, else_block = tree.children
        if self.visit(condition):
            return self.visit(then_block)
        return self.visit(else_block)

    def chant(self, tree):
        condition, body = tree.children
        while self.visit(condition):
            self.visit(body)

    def vigil(self, tree):
        try_blk, err_var, catch_blk = tree.children
        try:
            return self.visit(try_blk)
        except ReturnSignal:
            raise
        except Exception as e:
            self.scope.set(str(err_var), str(e))
            return self.visit(catch_blk)

    def offer(self, tree):
        raise ReturnSignal(self.visit(tree.children[0]))

    def silence(self, tree):
        return None

    # --- Functions & Traditions ---

    def tradition(self, tree):
        rel_path = str(tree.children[0])[1:-1]
        path = os.path.abspath(os.path.join(self.base_path, rel_path))
        
        if path in self._imported_files: return
        self._imported_files.add(path)
        
        if not os.path.exists(path):
            raise LogosError(f"Schism: Tradition not found: {path}")

        with open(path, "r", encoding="utf-8") as f:
            tree = Lark(LOGOS_GRAMMAR, parser="lalr").parse(f.read())
            self.visit(tree)

    def mystery_def(self, tree):
        name = str(tree.children[0])
        if not self._re_func.fullmatch(name):
            raise LogosError(f"Canon Error: Mystery name '{name}' must be snake_case.")
        
        # Parse params (index 1 if present)
        idx = 1
        params = []
        if idx < len(tree.children) and getattr(tree.children[idx], "data", "") == "params":
            params = [str(p.children[0]) for p in tree.children[idx].children]
            idx += 1
        
        # Skip return type hint if present
        if idx < len(tree.children) and getattr(tree.children[idx], "type", "") == "NAME":
            idx += 1
            
        body = tree.children[idx]
        self.scope.register_builtin(name, UserFunction(name, params, body))

    def apocrypha(self, tree):
        lib_str = str(tree.children[0])[1:-1]
        func_name = str(tree.children[1])
        
        # Extract arg types
        idx = 2
        arg_types = []
        if idx < len(tree.children) and getattr(tree.children[idx], "data", "") == "params":
            for p in tree.children[idx].children:
                arg_types.append(str(p.children[1]) if len(p.children) > 1 else "Float")
            idx += 1
            
        # Extract return type
        ret_type = "Float"
        if idx < len(tree.children) and getattr(tree.children[idx], "type", "") == "NAME":
            ret_type = str(tree.children[idx])

        func_def = self.ffi.bind_function(lib_str, func_name, arg_types, ret_type)
        self.scope.register_builtin(func_name, func_def)

    def call(self, tree):
        func_name = str(tree.children[0])
        args_node = tree.children[1] if len(tree.children) > 1 else None
        args = [self.visit(c) for c in args_node.children] if args_node else []

        spirit = self.scope.get(func_name)

        if self._recursion_depth > self._max_recursion:
            raise LogosError("Pride: Recursion depth exceeded.")

        self._recursion_depth += 1
        try:
            if isinstance(spirit, UserFunction):
                return self._invoke_user_function(spirit, args)
            elif isinstance(spirit, ForeignFunction):
                return self._invoke_foreign_function(spirit, args)
            elif callable(spirit):
                return spirit(*args)
            else:
                raise LogosError(f"Anathema: '{func_name}' is not callable.")
        finally:
            self._recursion_depth -= 1

    def _invoke_user_function(self, func: UserFunction, args: List[Any]):
        if len(args) != len(func.params):
            raise LogosError(f"Invocation Error: {func.name} expects {len(func.params)} args.")
        
        self.scope.push_frame(dict(zip(func.params, args)))
        try:
            return self.visit(func.body)
        except ReturnSignal as s:
            return s.value
        finally:
            self.scope.pop_frame()

    def _invoke_foreign_function(self, func: ForeignFunction, args: List[Any]):
        # If the apocrypha declaration provided arg types, enforce arity.
        if func.argtypes and len(args) != len(func.argtypes):
            raise LogosError(f"Invocation Error: Foreign function expects {len(func.argtypes)} args.")

        # If arg types were omitted in the declaration, infer them from the call site.
        if not func.argtypes and args:
            inferred_argtypes = [self.ffi.infer_ctype_from_value(a) for a in args]
            func.func.argtypes = inferred_argtypes
            inferred_def = ForeignFunction(func.func, func.restype, inferred_argtypes)
            c_args = self.ffi.marshal_args(args, inferred_def)
            return func.func(*c_args)

        c_args = self.ffi.marshal_args(args, func)
        return func.func(*c_args)

    # --- Structures (Icons) ---

    def icon_def(self, tree):
        name = str(tree.children[0])
        if not self._re_icon.fullmatch(name):
            raise LogosError(f"Canon Error: Icon name '{name}' must be Capitalized.")
        # We don't strictly enforce field definition at runtime in this dynamic implementation,
        # but we could store it in scope if needed for validation.
        pass

    def write_icon(self, tree):
        name = str(tree.children[0])
        assigns = self.visit(tree.children[1]) if len(tree.children) > 1 else []
        obj = {"__icon__": name}
        obj.update(dict(assigns))
        return obj

    def assign_list(self, tree):
        return [self.visit(c) for c in tree.children]
    
    def assign(self, tree):
        return (str(tree.children[0]), self.visit(tree.children[1]))

    # --- Data Access & Mutation ---

    def _perform_mutation(self, node, value):
        rule = getattr(node, "data", None)
        
        if rule == "mut_var":
            self.scope.set(str(node.children[0]), value)
        elif rule == "mut_attr":
            container = self._evaluate_mutable_target(node.children[0])
            name = str(node.children[1])
            if isinstance(container, dict): container[name] = value
            else: setattr(container, name, value)
        elif rule == "mut_item":
            container = self._evaluate_mutable_target(node.children[0])
            idx = self.visit(node.children[1])
            try:
                container[int(idx) if isinstance(container, list) else idx] = value
            except (IndexError, KeyError) as e:
                raise LogosError(f"Anathema: Invalid mutation access: {e}")
        else:
            raise LogosError("Schism: Invalid mutation target.")

    def _evaluate_mutable_target(self, node):
        # Recursively resolve the object being mutated
        rule = getattr(node, "data", None)
        if rule == "mut_var": return self.scope.get(str(node.children[0]))
        if rule == "mut_attr":
            obj = self._evaluate_mutable_target(node.children[0])
            return obj.get(str(node.children[1])) if isinstance(obj, dict) else getattr(obj, str(node.children[1]))
        if rule == "mut_item":
            obj = self._evaluate_mutable_target(node.children[0])
            idx = self.visit(node.children[1])
            return obj[int(idx)] if isinstance(obj, list) else obj[idx]
        return self.visit(node)

    def get_attr(self, tree):
        obj = self.visit(tree.children[0])
        name = str(tree.children[1])
        return obj.get(name) if isinstance(obj, dict) else getattr(obj, name)

    def get_item(self, tree):
        obj = self.visit(tree.children[0])
        idx = self.visit(tree.children[1])
        try:
            return obj[int(idx)] if isinstance(obj, (list, str)) else obj[idx]
        except (IndexError, KeyError):
            raise LogosError(f"Anathema: Index {idx} out of bounds.")

    # --- Expressions & Atoms ---

    def var(self, tree):
        return self.scope.get(str(tree.children[0]))

    def number(self, tree):
        s = str(tree.children[0])
        return float(s) if "." in s else int(s)

    def string(self, tree):
        return str(tree.children[0])[1:-1].replace("\\n", "\n")
    
    def procession(self, tree):
        return [self.visit(c) for c in tree.children]

    def verily(self, _): return True
    def nay(self, _): return False
    
    def add(self, t): return self.visit(t.children[0]) + self.visit(t.children[1])
    def sub(self, t): return self.visit(t.children[0]) - self.visit(t.children[1])
    def mul(self, t): return self.visit(t.children[0]) * self.visit(t.children[1])
    def div(self, t): return self.visit(t.children[0]) / self.visit(t.children[1])
    def neg(self, t): return -self.visit(t.children[0])
    
    def eq(self, t): return self.visit(t.children[0]) == self.visit(t.children[1])
    def ne(self, t): return self.visit(t.children[0]) != self.visit(t.children[1])
    def lt(self, t): return self.visit(t.children[0]) < self.visit(t.children[1])
    def gt(self, t): return self.visit(t.children[0]) > self.visit(t.children[1])
    def le(self, t): return self.visit(t.children[0]) <= self.visit(t.children[1])
    def ge(self, t): return self.visit(t.children[0]) >= self.visit(t.children[1])

    def transfigure(self, tree):
        val = self.visit(tree.children[0])
        target_type = str(tree.children[1])
        if target_type in ("HolyInt", "Int"): return int(val)
        if target_type in ("HolyFloat", "Float"): return float(val)
        if target_type in ("Text", "String"): return str(val)
        return val

    def supplicate(self, tree):
        return input(str(self.visit(tree.children[0])))

    def contemplation(self, tree):
        target = self.visit(tree.children[0])
        for case in tree.children[1:]:
            pattern_node, body_node = case.children
            pattern = self.visit(pattern_node)
            if pattern == "__WILDCARD__" or target == pattern:
                return self.visit(body_node)
        return None

    def wildcard(self, _): return "__WILDCARD__"
    def case_clause(self, tree): return tree # Handled in contemplation
    def atom(self, tree): return self.visit(tree.children[0]) if tree.children else None


# ==========================================
# 5. Entry Point & Interface
# ==========================================

def run_repl(interpreter: LogosInterpreter):
    print("☩ Logos Interactive Confessional v2.0 ☩")
    print("☩ Type 'silence;' to pass, 'exit' to depart.")
    
    parser = Lark(LOGOS_GRAMMAR, parser="lalr", start="statement")
    
    while True:
        try:
            text = input(">> ").strip()
            if not text: continue
            if text in ("exit", "quit", "depart(0);"): break

            tree = parser.parse(text)
            result = interpreter.visit(tree)
            if result is not None:
                print(f"=> {result}")

        except ReturnSignal as r:
            print(f"=> {r.value}")
        except (LogosError, Exception) as e:
            print(f"Anathema: {e}")

def main():
    interpreter = LogosInterpreter()

    if len(sys.argv) < 2:
        run_repl(interpreter)
        return

    entry_path = os.path.abspath(sys.argv[1])
    interpreter.base_path = os.path.dirname(entry_path)
    interpreter.stdlib.base_path = interpreter.base_path # Sync paths

    try:
        with open(entry_path, "r", encoding="utf-8") as f:
            source = f.read()
        
        parser = Lark(LOGOS_GRAMMAR, parser="lalr")
        interpreter.visit(parser.parse(source))

        # Invoke main if defined
        try:
            main_func = interpreter.scope.get("main")
            if isinstance(main_func, UserFunction):
                interpreter._invoke_user_function(main_func, [])
        except LogosError:
            pass # No main, that's fine

    except Exception as e:
        print(f"☨ FATAL ERROR ☨\n{e}")
        sys.exit(1)

if __name__ == "__main__":
    main()