from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, TYPE_CHECKING

if TYPE_CHECKING:
    from .interpreter import LogosInterpreter


@dataclass
class SecurityContext:
    allow_ffi: bool = False
    whitelist: Dict[str, Set[str]] = field(default_factory=dict)
    allow_unsafe_pointers: bool = False

    @classmethod
    def strict(cls) -> "SecurityContext":
        return cls(allow_ffi=False)

    @classmethod
    def permissive(cls) -> "SecurityContext":
        math_funcs = {"cos", "sin", "tan", "sqrt", "pow", "abs", "floor", "ceil"}
        return cls(
            allow_ffi=True,
            whitelist={
                "m": math_funcs,
                "libm": math_funcs,
                "libc": math_funcs,
                "c": math_funcs,
                "msvcrt": math_funcs | {"puts"},
            },
            allow_unsafe_pointers=False,
        )


@dataclass(frozen=True)
class UserFunction:
    name: str
    params: List[str]
    body: Any


@dataclass(frozen=True)
class ModuleFunction:
    func: UserFunction
    interpreter: "LogosInterpreter"
    exports: Dict[str, Any]


@dataclass(frozen=True)
class TailCall:
    func: UserFunction
    args: List[Any]


@dataclass(frozen=True)
class ReturnValue:
    value: Any


@dataclass
class ForeignFunction:
    func: Any
    restype: Any
    argtypes: List[Any]
