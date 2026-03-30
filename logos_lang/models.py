from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any, Dict, List, Literal, Set

FFI_BACKEND_CTYPES: Literal["ctypes"] = "ctypes"
FFI_BACKEND_RUST: Literal["rust"] = "rust"
FFI_BACKEND_WASM: Literal["wasm"] = "wasm"
FFI_BACKEND = Literal["ctypes", "rust", "wasm"]

if TYPE_CHECKING:
    from .interpreter import LogosInterpreter


@dataclass
class SecurityContext:
    allow_ffi: bool = False
    whitelist: Dict[str, Set[str]] = field(default_factory=dict)
    allow_unsafe_pointers: bool = False
    allow_inferred_ffi_signatures: bool = False
    ffi_backend: FFI_BACKEND = FFI_BACKEND_CTYPES
    require_os_sandbox_for_ffi: bool = False
    sandbox_attestation_env: str = "LOGOS_OS_SANDBOX"
    denylisted_ffi_symbols: Set[str] = field(
        default_factory=lambda: {
            "system",
            "popen",
            "fork",
            "vfork",
            "execv",
            "execve",
            "execl",
            "execlp",
            "execvp",
            "execvpe",
            "dlopen",
            "dlsym",
            "mprotect",
            "virtualprotect",
            "winexec",
            "shellexecutea",
            "shellexecutew",
            "createprocessa",
            "createprocessw",
            "loadlibrarya",
            "loadlibraryw",
        }
    )

    @classmethod
    def strict(cls) -> "SecurityContext":
        return cls(
            allow_ffi=False,
            allow_unsafe_pointers=False,
            allow_inferred_ffi_signatures=False,
            ffi_backend=FFI_BACKEND_CTYPES,
            require_os_sandbox_for_ffi=False,
        )

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
            allow_inferred_ffi_signatures=False,
            ffi_backend=FFI_BACKEND_CTYPES,
            require_os_sandbox_for_ffi=False,
        )

    @classmethod
    def hardened(cls) -> "SecurityContext":
        return cls(
            allow_ffi=False,
            allow_unsafe_pointers=False,
            allow_inferred_ffi_signatures=False,
            ffi_backend=FFI_BACKEND_WASM,
            require_os_sandbox_for_ffi=True,
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
