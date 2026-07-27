import os
import sys
from typing import TYPE_CHECKING, Any, Dict, Optional, Set

from lark import Lark

from .exceptions import LogosError, SecurityError
from .grammar import LOGOS_GRAMMAR
from .models import ModuleFunction, SecurityContext, UserFunction

if TYPE_CHECKING:
    from .interpreter import LogosInterpreter


class Module:
    def __init__(
        self,
        path: str,
        exports: Dict[str, Any],
        types: Optional[Dict[str, str]] = None,
        icons: Optional[Dict[str, Dict[str, str]]] = None,
        interpreter: Optional["LogosInterpreter"] = None,
    ) -> None:
        self.path = path
        self.exports = exports
        self.types = types or {}
        self.icons = icons or {}
        self.interpreter = interpreter
        self.exports["__icon__"] = "Module"

    def sync_exports(self) -> None:
        if not self.interpreter:
            return
        for k, v in self.interpreter.scope.globals.items():
            if (
                k in self.interpreter._builtin_snapshot
                and v is self.interpreter._builtin_snapshot[k]
            ):
                continue
            if isinstance(v, UserFunction):
                if k not in self.exports or not isinstance(self.exports[k], ModuleFunction):
                    self.exports[k] = ModuleFunction(v, self.interpreter, self.exports)
            else:
                self.exports[k] = v

    def __getitem__(self, key: str) -> Any:
        return self.exports[key]

    def get(self, key: str, default: Any = None) -> Any:
        return self.exports.get(key, default)


class ModuleManager:
    def __init__(self) -> None:
        self._modules: Dict[str, Module] = {}
        self._loading: Set[str] = set()
        self.security: Optional[SecurityContext] = None

    def load_module(
        self,
        requestor_path: str,
        rel_path: str,
        parent_interp: Optional["LogosInterpreter"] = None,
    ) -> Module:
        # Avoid circular import at top-level
        from .interpreter import LogosInterpreter

        base_dir = os.path.dirname(requestor_path)
        abs_path = os.path.abspath(os.path.join(base_dir, rel_path))
        resolved_path = os.path.realpath(abs_path)

        root_base = os.path.realpath(
            parent_interp.base_path
            if parent_interp and parent_interp.base_path
            else os.getcwd()
        )
        try:
            if os.path.commonpath([root_base, resolved_path]) != root_base:
                raise SecurityError(
                    f"Security Violation: Tradition path traversal blocked for '{rel_path}'."
                )
        except ValueError:
            raise SecurityError(
                f"Security Violation: Tradition path traversal blocked for '{rel_path}'."
            )

        if resolved_path in self._modules:
            return self._modules[resolved_path]
        if resolved_path in self._loading:
            sys.stderr.write(f"☩ Cycle detected importing {rel_path}. Returning partial spirit.\n")
            return Module(resolved_path, {})
        if not os.path.exists(resolved_path):
            raise LogosError(f"Schism: Tradition not found: {rel_path}")

        self._loading.add(resolved_path)
        try:
            with open(resolved_path, "r", encoding="utf-8") as f:
                source = f.read()

            security = self.security or (
                parent_interp.security if parent_interp else SecurityContext.strict()
            )
            io_handler = parent_interp.io if parent_interp else None
            execution_engine = parent_interp.execution_engine if parent_interp else None
            enable_static_type_elision = (
                parent_interp.enable_static_type_elision if parent_interp else True
            )
            trusted_lsp_types = parent_interp.trusted_lsp_types if parent_interp else None

            child_interp = LogosInterpreter(
                base_path=root_base,
                module_manager=self,
                security=security,
                io_handler=io_handler,
                execution_engine=execution_engine,
                enable_static_type_elision=enable_static_type_elision,
                trusted_lsp_types=trusted_lsp_types,
            )
            child_interp._current_file = resolved_path
            tree = Lark(LOGOS_GRAMMAR, parser="lalr").parse(source)
            child_interp.visit(tree)

            exports: Dict[str, Any] = {}
            for k, v in child_interp.scope.globals.items():
                if k not in child_interp._builtin_snapshot:
                    exports[k] = v
                    continue
                if v is not child_interp._builtin_snapshot[k]:
                    exports[k] = v
            for name, value in list(exports.items()):
                if isinstance(value, UserFunction):
                    exports[name] = ModuleFunction(value, child_interp, exports)

            module = Module(
                resolved_path,
                exports,
                types=dict(child_interp._global_types),
                icons=dict(child_interp._icons),
                interpreter=child_interp,
            )
            self._modules[resolved_path] = module
            return module
        finally:
            self._loading.discard(resolved_path)