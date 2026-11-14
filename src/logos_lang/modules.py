import os
import re
import sys
from typing import TYPE_CHECKING, Any, Dict, List, Optional

from .exceptions import LogosError, SecurityError
from .grammar import create_parser
from .models import ModuleFunction, SecurityContext, UserFunction

if TYPE_CHECKING:
    from .interpreter import LogosInterpreter


# The bundled canon ships inside the package (src/logos_lang/lib/*.lg), so it resolves the
# same way in a source checkout, an editable install and an installed wheel.
BUNDLED_LIB_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "lib")

# `tradition "std:genesis";` names a book of the bundled canon independent of file layout.
STD_PREFIX = "std:"
_STD_NAME = re.compile(r"[a-z][a-z0-9_]*")


def _resolve_import_path(base_dir: str, rel_path: str) -> str:
    if rel_path.startswith(STD_PREFIX):
        name = rel_path[len(STD_PREFIX) :]
        if not _STD_NAME.fullmatch(name):
            raise LogosError(f"Schism: Invalid canon name '{rel_path}'; expected e.g. 'std:genesis'.")
        return os.path.join(BUNDLED_LIB_DIR, f"{name}.lg")
    return os.path.abspath(os.path.join(base_dir, rel_path))


def _import_roots(
    parent_interp: Optional["LogosInterpreter"], base_dir: str, security: SecurityContext
) -> List[str]:
    """Directories a `tradition` may resolve into: the program root, the bundled canon,
    and any roots granted explicitly via ``SecurityContext.import_roots``."""
    program_root = parent_interp.base_path if parent_interp and parent_interp.base_path else base_dir
    roots = [program_root, BUNDLED_LIB_DIR, *security.import_roots]
    return [os.path.normcase(os.path.realpath(r)) for r in roots]


def _is_within(root: str, path: str) -> bool:
    try:
        return os.path.commonpath([root, path]) == root
    except ValueError:  # different drives on Windows
        return False


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
        # Modules currently executing. A cyclic import receives this same (still filling)
        # Module object, so its exports become visible once the cycle unwinds.
        self._loading: Dict[str, Module] = {}
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
        abs_path = _resolve_import_path(base_dir, rel_path)
        resolved_path = os.path.normcase(os.path.realpath(abs_path))

        security = self.security or (
            parent_interp.security if parent_interp else SecurityContext.strict()
        )
        roots = _import_roots(parent_interp, base_dir, security)
        if not any(_is_within(root, resolved_path) for root in roots):
            raise SecurityError(
                f"Security Violation: Tradition path traversal blocked for '{rel_path}'."
            )

        if resolved_path in self._modules:
            return self._modules[resolved_path]
        if resolved_path in self._loading:
            sys.stderr.write(f"☩ Cycle detected importing {rel_path}. Returning partial spirit.\n")
            return self._loading[resolved_path]
        if not os.path.exists(resolved_path):
            raise LogosError(f"Schism: Tradition not found: {rel_path}")

        module = Module(resolved_path, {})
        self._loading[resolved_path] = module
        try:
            with open(resolved_path, "r", encoding="utf-8") as f:
                source = f.read()

            io_handler = parent_interp.io if parent_interp else None
            execution_engine = parent_interp.execution_engine if parent_interp else None
            enable_static_type_elision = (
                parent_interp.enable_static_type_elision if parent_interp else True
            )
            trusted_lsp_types = parent_interp.trusted_lsp_types if parent_interp else None

            child_interp = LogosInterpreter(
                base_path=parent_interp.base_path if parent_interp else os.path.dirname(resolved_path),
                module_manager=self,
                security=security,
                io_handler=io_handler,
                execution_engine=execution_engine,
                enable_static_type_elision=enable_static_type_elision,
                trusted_lsp_types=trusted_lsp_types,
            )
            child_interp._current_file = resolved_path
            module.interpreter = child_interp
            tree = create_parser().parse(source)
            child_interp.visit(tree)

            # Fill the Module object handed out to any cyclic importer, in place.
            exports = module.exports
            for k, v in child_interp.scope.globals.items():
                if k in child_interp._builtin_snapshot and v is child_interp._builtin_snapshot[k]:
                    continue
                exports[k] = ModuleFunction(v, child_interp, exports) if isinstance(
                    v, UserFunction
                ) else v
            module.types = dict(child_interp._global_types)
            module.icons = dict(child_interp._icons)
            self._modules[resolved_path] = module
            return module
        finally:
            self._loading.pop(resolved_path, None)