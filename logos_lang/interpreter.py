import os
import re
import sys
from typing import Any, Dict, List, Optional

from lark import Tree
from lark.visitors import Interpreter

from .bytecode import BytecodeCompiler, BytecodeProgram, BytecodeUnsupported, BytecodeVM
from .exceptions import LogosError
from .ffi import FFIManager
from .interfaces import ConsoleIO, IOHandler, _resolve_print
from .models import (
    ForeignFunction,
    ModuleFunction,
    ReturnValue,
    SecurityContext,
    TailCall,
    UserFunction,
)
from .modules import ModuleManager
from .scope import ScopeManager
from .static_analysis import StaticTypeAnalyzer
from .stdlib import StdLib
from .types import TypeCanon


class LogosInterpreter(Interpreter[Any, Any]):
    def __init__(
        self,
        base_path: Optional[str] = None,
        module_manager: Optional[ModuleManager] = None,
        security: Optional[SecurityContext] = None,
        io_handler: Optional[IOHandler] = None,
        execution_engine: Optional[str] = None,
        enable_static_type_elision: bool = True,
        trusted_lsp_types: Optional[Dict[str, str]] = None,
    ):
        self.base_path = os.path.abspath(base_path or os.getcwd())
        self.security = security if security is not None else SecurityContext.strict()
        self.scope = ScopeManager()
        self.ffi = FFIManager(self.security)
        self.stdlib = StdLib(self.base_path)
        self.module_manager = module_manager if module_manager else ModuleManager()
        self.module_manager.security = self.security
        self.io = io_handler if io_handler is not None else ConsoleIO()

        self.stdlib.register_into(self.scope)
        self._builtin_snapshot: Dict[str, Any] = dict(self.scope.globals)
        self._recursion_depth = 0
        self._max_recursion = int(os.environ.get("LOGOS_MAX_RECURSION", "1000"))
        self._current_file = os.path.join(self.base_path, "__main__.lg")

        self._global_types: Dict[str, str] = {}
        self._type_stack: List[Dict[str, str]] = []
        self._icons: Dict[str, Dict[str, str]] = {}

        try:
            sys.setrecursionlimit(max(sys.getrecursionlimit(), self._max_recursion + 200))
        except Exception:
            pass

        self._re_icon = re.compile(r"^[A-Z][A-Za-z0-9_]*$")
        self._re_func = re.compile(r"^[a-z][a-z0-9_]*$")
        self.execution_engine = (
            execution_engine or os.environ.get("LOGOS_EXECUTION_ENGINE", "vm-hybrid")
        ).lower()
        self.enable_static_type_elision = enable_static_type_elision
        self.trusted_lsp_types = dict(trusted_lsp_types or {})
        self._elided_declared_types: Dict[str, str] = {}
        self._bytecode_compiler = BytecodeCompiler()
        self._bytecode_vm = BytecodeVM(self)
        self._last_execution_backend = "visitor"

    def visit(self, tree: Any) -> Any:
        if isinstance(tree, Tree) and tree.data == "start":
            self._prepare_static_type_elision(tree)
            return self._execute_start_tree(tree)
        return super().visit(tree)

    def _execute_start_tree(self, tree: Tree[Any]) -> Any:
        engine = self.execution_engine
        strict_vm = engine in {"vm", "bytecode", "vm-strict", "bytecode-strict"}
        try_vm = engine in {
            "vm",
            "bytecode",
            "vm-strict",
            "bytecode-strict",
            "vm-hybrid",
            "bytecode-hybrid",
        }

        if try_vm:
            try:
                program = self._bytecode_compiler.compile(tree)
            except BytecodeUnsupported as exc:
                if strict_vm:
                    raise LogosError(
                        "Bytecode VM strict mode rejected unsupported construct: "
                        f"{exc}"
                    ) from exc
            else:
                self._last_execution_backend = "vm"
                return self._bytecode_vm.run(program)

        self._last_execution_backend = "visitor"
        return super().visit(tree)

    def compile_bytecode(self, tree: Any) -> BytecodeProgram:
        if not isinstance(tree, Tree):
            raise LogosError("Bytecode compilation requires a parsed syntax tree.")
        return self._bytecode_compiler.compile(tree)

    def _prepare_static_type_elision(self, tree: Tree[Any]) -> None:
        self._elided_declared_types = {}
        if not self.enable_static_type_elision:
            return

        inferred = StaticTypeAnalyzer().analyze(tree)
        self._elided_declared_types.update(inferred.bindings)
        self._elided_declared_types.update(self.trusted_lsp_types)

    # --- Root Statements ---

    def proclaim(self, tree: Any) -> None:
        val = self.visit(tree.children[0])
        prefix = "Verily" if val is True else "Nay" if val is False else str(val)
        self._emit("☩", prefix)

    def _emit(self, symbol: str, message: str) -> None:
        try:
            self.io.emit(symbol, message)
        except Exception:
            try:
                _resolve_print()(f"{symbol} {message}")
            except Exception:
                pass

    def inscribe(self, tree: Any) -> Any:
        name = str(tree.children[0])
        declared_type = str(tree.children[1]) if len(tree.children) == 3 else None
        expr_idx = 2 if declared_type is not None else 1
        val = self.visit(tree.children[expr_idx])
        if declared_type is not None:
            self._declare_type(name, declared_type)
        self._enforce_declared_type(name, val)
        self.scope.declare(name, val)
        return val

    def amend(self, tree: Any) -> None:
        target_node, value_node = tree.children
        value = self.visit(value_node)
        self._perform_mutation(target_node, value)

    def expr_stmt(self, tree: Any) -> Any:
        return self.visit(tree.children[0])

    # --- Flow Control ---

    def block(self, tree: Any) -> Any:
        result = None
        for stmt in tree.children:
            result = self.visit(stmt)
            if isinstance(result, ReturnValue):
                return result
        return result

    def discernment(self, tree: Any) -> Any:
        if self.visit(tree.children[0]):
            return self.visit(tree.children[1])
        return self.visit(tree.children[2])

    def chant(self, tree: Any) -> Any:
        condition, body = tree.children
        while self.visit(condition):
            result = self.visit(body)
            if isinstance(result, ReturnValue):
                return result

    def vigil(self, tree: Any) -> Any:
        try_blk, err_var, catch_blk = tree.children
        try:
            return self.visit(try_blk)
        except Exception as e:
            self.scope.set(str(err_var), str(e))
            return self.visit(catch_blk)

    def offer(self, tree: Any) -> ReturnValue:
        expr = tree.children[0]
        if getattr(expr, "data", None) == "call":
            func_name = str(expr.children[0])
            args_node = expr.children[1] if len(expr.children) > 1 else None
            args = [self.visit(c) for c in args_node.children] if args_node else []
            spirit = self.scope.get(func_name)
            if isinstance(spirit, UserFunction):
                return ReturnValue(TailCall(spirit, args))
        return ReturnValue(self.visit(expr))

    def silence(self, tree: Any) -> None:
        return None

    # --- Functions & Traditions ---

    def tradition(self, tree: Any) -> Dict[str, Any]:
        rel_path = str(tree.children[0])[1:-1]
        alias = str(tree.children[1]) if len(tree.children) > 1 else None
        requestor = getattr(self, "_current_file", os.path.join(self.base_path, "__main__.lg"))
        module = self.module_manager.load_module(requestor_path=requestor, rel_path=rel_path)

        for name, type_name in module.types.items():
            self._declare_type(name, type_name)
        if module.icons:
            self._icons.update(module.icons)

        if alias:
            self.scope.declare(alias, module.exports)
            return module.exports

        for name, value in module.exports.items():
            if name == "__icon__":
                continue
            if isinstance(value, ModuleFunction):
                value = value.func
            self.scope.set(name, value)
        return module.exports

    def mystery_def(self, tree: Any) -> None:
        name = str(tree.children[0])
        if not self._re_func.fullmatch(name):
            raise LogosError(f"Canon Error: Mystery name '{name}' must be snake_case.")
        idx = 1
        params = []
        if idx < len(tree.children) and getattr(tree.children[idx], "data", "") == "params":
            params = [str(p.children[0]) for p in tree.children[idx].children]
            idx += 1
        if idx < len(tree.children) and getattr(tree.children[idx], "type", "") == "NAME":
            idx += 1
        body = tree.children[idx]
        self.scope.register_builtin(name, UserFunction(name, params, body))

    def apocrypha(self, tree: Any) -> None:
        lib_str = str(tree.children[0])[1:-1]
        func_name = str(tree.children[1])
        idx = 2
        arg_types = []
        if idx < len(tree.children) and getattr(tree.children[idx], "data", "") == "params":
            for p in tree.children[idx].children:
                arg_types.append(str(p.children[1]) if len(p.children) > 1 else "Float")
            idx += 1
        ret_type = "Float"
        if idx < len(tree.children) and getattr(tree.children[idx], "type", "") == "NAME":
            ret_type = str(tree.children[idx])
        func_def = self.ffi.bind_function(lib_str, func_name, arg_types, ret_type)
        self.scope.register_builtin(func_name, func_def)

    def call(self, tree: Any) -> Any:
        func_name = str(tree.children[0])
        args_node = tree.children[1] if len(tree.children) > 1 else None
        args = [self.visit(c) for c in args_node.children] if args_node else []
        spirit = self.scope.get(func_name)

        if isinstance(spirit, ModuleFunction):
            sync = {
                k: (v.func if isinstance(v, ModuleFunction) else v)
                for k, v in spirit.exports.items()
                if k != "__icon__"
            }
            spirit.interpreter.scope.globals.update(sync)
            return spirit.interpreter._invoke_user_function(spirit.func, args)

        if self._recursion_depth > self._max_recursion:
            raise LogosError("Pride: Recursion depth exceeded.")

        self._recursion_depth += 1
        try:
            if isinstance(spirit, UserFunction):
                return self._invoke_user_function(spirit, args)
            if isinstance(spirit, ForeignFunction):
                return self._invoke_foreign_function(spirit, args)
            if callable(spirit):
                return spirit(*args)
            raise LogosError(f"Anathema: '{func_name}' is not callable.")
        except RecursionError as e:
            raise LogosError("Pride: Host recursion limit reached.") from e
        finally:
            self._recursion_depth -= 1

    def _invoke_user_function(self, func: UserFunction, args: List[Any]) -> Any:
        current_func, current_args = func, args
        tail_hops = 0
        tail_limit = max(int(os.environ.get("LOGOS_MAX_TCO", "1000000")), self._max_recursion * 100)
        while True:
            if len(current_args) != len(current_func.params):
                raise LogosError(
                    f"Invocation Error: {current_func.name} expects {len(current_func.params)} args."
                )
            if tail_hops > tail_limit:
                raise LogosError("Pride: Tail-call loop exceeded recursion policy.")

            self.scope.push_frame(dict(zip(current_func.params, current_args)))
            self._type_stack.append({})
            try:
                result = self.visit(current_func.body)
                if isinstance(result, ReturnValue):
                    if isinstance(result.value, TailCall):
                        current_func = result.value.func
                        current_args = result.value.args
                        tail_hops += 1
                        continue
                    return result.value
                return result
            finally:
                self._type_stack.pop()
                self.scope.pop_frame()

    def _invoke_foreign_function(self, func: ForeignFunction, args: List[Any]) -> Any:
        if func.argtypes and len(args) != len(func.argtypes):
            raise LogosError(
                f"Invocation Error: Foreign function expects {len(func.argtypes)} args."
            )
        if not func.argtypes and args:
            if not self.security.allow_inferred_ffi_signatures:
                raise LogosError(
                    "Security Violation: Inferred Apocrypha signatures are disabled. "
                    "Declare explicit parameter types or enable inferred signatures explicitly."
                )
            inferred_argtypes = [self.ffi.infer_ctype_from_value(a) for a in args]
            func.func.argtypes = inferred_argtypes
            inferred_def = ForeignFunction(func.func, func.restype, inferred_argtypes)
            c_args = self.ffi.marshal_args(args, inferred_def)
            return func.func(*c_args)
        c_args = self.ffi.marshal_args(args, func)
        return func.func(*c_args)

    # --- Structures (Icons) ---

    def icon_def(self, tree: Any) -> None:
        name = str(tree.children[0])
        if not self._re_icon.fullmatch(name):
            raise LogosError(f"Canon Error: Icon name '{name}' must be Capitalized.")
        fields: Dict[str, str] = {}
        for decl in tree.children[1:]:
            if getattr(decl, "data", None) == "field_decl":
                fields[str(decl.children[0])] = str(decl.children[1])
        self._icons[name] = fields

    def write_icon(self, tree: Any) -> Dict[str, Any]:
        name = str(tree.children[0])
        assigns = self.visit(tree.children[1]) if len(tree.children) > 1 else []
        obj = {"__icon__": name}
        values = dict(assigns)
        schema = self._icons.get(name)
        if schema:
            for field_name, field_type in schema.items():
                if field_name in values:
                    self._enforce_value_type(
                        values[field_name], field_type, context=f"{name}.{field_name}"
                    )
        obj.update(values)
        return obj

    def assign_list(self, tree: Any) -> List[tuple[str, Any]]:
        return [self.visit(c) for c in tree.children]

    def assign(self, tree: Any) -> tuple[str, Any]:
        return (str(tree.children[0]), self.visit(tree.children[1]))

    # --- Data Access & Mutation ---

    def _perform_mutation(self, node: Any, value: Any) -> None:
        rule = getattr(node, "data", None)
        if rule == "mut_var":
            name = str(node.children[0])
            self._enforce_declared_type(name, value)
            self.scope.mutate(name, value)
        elif rule == "mut_attr":
            container = self._evaluate_mutable_target(node.children[0])
            name = str(node.children[1])
            if isinstance(container, dict):
                self._enforce_icon_field_type(container, name, value)
                container[name] = value
            else:
                setattr(container, name, value)
        elif rule == "mut_item":
            container = self._evaluate_mutable_target(node.children[0])
            idx = self.visit(node.children[1])
            try:
                container[int(idx) if isinstance(container, list) else idx] = value
            except (IndexError, KeyError) as e:
                raise LogosError(f"Anathema: Invalid mutation access: {e}")
        else:
            raise LogosError("Schism: Invalid mutation target.")

    # --- Type Enforcement ---

    def _declare_type(self, name: str, type_name: str) -> None:
        target = self._type_stack[-1] if self._type_stack else self._global_types
        existing = target.get(name)
        if existing is not None and existing != type_name:
            raise LogosError(
                f"Canon Error: '{name}' was already declared as {existing}, cannot redeclare as {type_name}."
            )
        target[name] = type_name

    def _lookup_declared_type(self, name: str) -> Optional[str]:
        for frame in reversed(self._type_stack):
            if name in frame:
                return frame[name]
        return self._global_types.get(name)

    def _enforce_declared_type(self, name: str, value: Any) -> None:
        declared = self._lookup_declared_type(name)
        if declared:
            if not self._type_stack and self._elided_declared_types.get(name) == declared:
                return
            self._enforce_value_type(value, declared, context=name)

    def _enforce_icon_field_type(
        self, container: Dict[str, Any], field_name: str, value: Any
    ) -> None:
        icon_name = container.get("__icon__")
        if icon_name:
            schema = self._icons.get(str(icon_name))
            if schema and (field_type := schema.get(field_name)):
                self._enforce_value_type(value, field_type, context=f"{icon_name}.{field_name}")

    def _enforce_value_type(self, value: Any, type_name: str, context: str) -> None:
        actual_type = TypeCanon.get_type_of_value(value)
        known_decl = (
            TypeCanon.NUMERIC | TypeCanon.TEXT | TypeCanon.BOOL | TypeCanon.LIST | TypeCanon.VOID
        )
        if actual_type == "Mystery":
            if type_name in known_decl:
                raise LogosError(
                    f"Canon Error: Type mismatch for '{context}': expected {type_name}, got unknown type ({value})."
                )
            return
        if not TypeCanon.are_compatible(type_name, actual_type):
            raise LogosError(
                f"Canon Error: Type mismatch for '{context}': expected {type_name}, got {actual_type} ({value})."
            )

    def _evaluate_mutable_target(self, node: Any) -> Any:
        rule = getattr(node, "data", None)
        if rule == "mut_var":
            return self.scope.get(str(node.children[0]))
        if rule == "mut_attr":
            obj = self._evaluate_mutable_target(node.children[0])
            return (
                obj.get(str(node.children[1]))
                if isinstance(obj, dict)
                else getattr(obj, str(node.children[1]))
            )
        if rule == "mut_item":
            obj = self._evaluate_mutable_target(node.children[0])
            idx = self.visit(node.children[1])
            return obj[int(idx)] if isinstance(obj, list) else obj[idx]
        return self.visit(node)

    def get_attr(self, tree: Any) -> Any:
        obj = self.visit(tree.children[0])
        name = str(tree.children[1])
        if isinstance(obj, (ModuleFunction, ScopeManager, LogosInterpreter)) or name.startswith(
            "_"
        ):
            raise LogosError("Anathema: Attribute access forbidden on this spirit.")
        return obj.get(name) if isinstance(obj, dict) else getattr(obj, name)

    def get_item(self, tree: Any) -> Any:
        obj = self.visit(tree.children[0])
        idx = self.visit(tree.children[1])
        try:
            return obj[int(idx)] if isinstance(obj, (list, str)) else obj[idx]
        except (IndexError, KeyError):
            raise LogosError(f"Anathema: Index {idx} out of bounds.")

    # --- Expressions & Atoms ---

    def var(self, tree: Any) -> Any:
        return self.scope.get(str(tree.children[0]))

    def number(self, tree: Any) -> int | float:
        s = str(tree.children[0])
        return float(s) if "." in s else int(s)

    def string(self, tree: Any) -> str:
        return str(tree.children[0])[1:-1].replace("\\n", "\n")

    def procession(self, tree: Any) -> List[Any]:
        return [self.visit(c) for c in tree.children]

    def verily(self, _: Any) -> bool:
        return True

    def nay(self, _: Any) -> bool:
        return False

    def wildcard(self, _: Any) -> str:
        return "__WILDCARD__"

    def atom(self, tree: Any) -> Any:
        return self.visit(tree.children[0]) if tree.children else None

    def add(self, t: Any) -> Any:
        return self.visit(t.children[0]) + self.visit(t.children[1])

    def sub(self, t: Any) -> Any:
        return self.visit(t.children[0]) - self.visit(t.children[1])

    def mul(self, t: Any) -> Any:
        return self.visit(t.children[0]) * self.visit(t.children[1])

    def div(self, t: Any) -> Any:
        return self.visit(t.children[0]) / self.visit(t.children[1])

    def neg(self, t: Any) -> Any:
        return -self.visit(t.children[0])

    def eq(self, t: Any) -> bool:
        return bool(self.visit(t.children[0]) == self.visit(t.children[1]))

    def ne(self, t: Any) -> bool:
        return bool(self.visit(t.children[0]) != self.visit(t.children[1]))

    def lt(self, t: Any) -> bool:
        return bool(self.visit(t.children[0]) < self.visit(t.children[1]))

    def gt(self, t: Any) -> bool:
        return bool(self.visit(t.children[0]) > self.visit(t.children[1]))

    def le(self, t: Any) -> bool:
        return bool(self.visit(t.children[0]) <= self.visit(t.children[1]))

    def ge(self, t: Any) -> bool:
        return bool(self.visit(t.children[0]) >= self.visit(t.children[1]))

    def transfigure(self, tree: Any) -> Any:
        val = self.visit(tree.children[0])
        target = str(tree.children[1])
        if target in ("HolyInt", "Int"):
            return int(val)
        if target in ("HolyFloat", "Float"):
            return float(val)
        if target in ("Text", "String"):
            return str(val)
        return val

    def supplicate(self, tree: Any) -> str:
        prompt = str(self.visit(tree.children[0]))
        try:
            return self.io.read_input(prompt)
        except Exception:
            return input(prompt)

    def contemplation(self, tree: Any) -> Any:
        target = self.visit(tree.children[0])
        for case in tree.children[1:]:
            pattern = self.visit(case.children[0])
            if pattern == "__WILDCARD__" or target == pattern:
                return self.visit(case.children[1])
        return None

    def case_clause(self, tree: Any) -> Any:
        return tree
