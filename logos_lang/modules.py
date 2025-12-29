import os
from typing import Any, Dict, Optional, Set, TYPE_CHECKING

from lark import Lark

from .exceptions import LogosError
from .models import SecurityContext, ModuleFunction, UserFunction
from .grammar import LOGOS_GRAMMAR

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
    ):
        self.path = path
        self.exports = exports
        self.types = types or {}
        self.icons = icons or {}
        self.interpreter = interpreter
        self.exports["__icon__"] = "Module"

    def __getitem__(self, key: str) -> Any:
        return self.exports[key]

    def get(self, key: str, default: Any = None) -> Any:
        return self.exports.get(key, default)


class ModuleManager:
    def __init__(self):
        self._modules: Dict[str, Module] = {}
        self._loading: Set[str] = set()
        self.security: Optional[SecurityContext] = None

    def load_module(self, requestor_path: str, rel_path: str) -> Module:
        # Avoid circular import at top-level
        from .interpreter import LogosInterpreter

        base_dir = os.path.dirname(requestor_path)
        abs_path = os.path.abspath(os.path.join(base_dir, rel_path))

        if abs_path in self._modules:
            return self._modules[abs_path]
        if abs_path in self._loading:
            print(f"☩ Cycle detected importing {rel_path}. Returning partial spirit.")
            return Module(abs_path, {})
        if not os.path.exists(abs_path):
            raise LogosError(f"Schism: Tradition not found: {abs_path}")

        self._loading.add(abs_path)
        try:
            with open(abs_path, "r", encoding="utf-8") as f:
                source = f.read()

            security = self.security or SecurityContext.strict()
            child_interp = LogosInterpreter(
                base_path=os.path.dirname(abs_path),
                module_manager=self,
                security=security,
            )
            child_interp._current_file = abs_path
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
                abs_path,
                exports,
                types=dict(child_interp._global_types),
                icons=dict(child_interp._icons),
                interpreter=child_interp,
            )
            self._modules[abs_path] = module
            return module
        finally:
            self._loading.discard(abs_path)
