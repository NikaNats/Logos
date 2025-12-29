import ctypes
import os
import sys
from typing import Any, Dict, List

from .exceptions import LogosError, SecurityError
from .models import SecurityContext, ForeignFunction


class FFIManager:
    def __init__(self, security: SecurityContext):
        self.security = security
        self.libs: Dict[str, ctypes.CDLL] = {}

    def _clean_lib_name(self, lib_name: str) -> str:
        base = lib_name.split(".")[0]
        if base.startswith("lib"):
            return base[3:]
        return base

    def get_ctype(self, type_name: str) -> Any:
        unsafe_types = {"Text", "String", "void_p", "char_p"}
        if not self.security.allow_unsafe_pointers and type_name in unsafe_types:
            raise SecurityError(
                f"Security Violation: Type '{type_name}' involves raw pointers and is forbidden in safe mode."
            )
        mapping = {
            "HolyFloat": ctypes.c_double,
            "Float": ctypes.c_double,
            "Double": ctypes.c_double,
            "HolyInt": ctypes.c_longlong,
            "Int": ctypes.c_longlong,
            "Bool": ctypes.c_bool,
            "Verily": ctypes.c_bool,
            "Nay": ctypes.c_bool,
            "Text": ctypes.c_char_p,
            "String": ctypes.c_char_p,
        }
        return mapping.get(type_name, ctypes.c_double)

    def load_library(self, lib_name: str) -> str:
        if not self.security.allow_ffi:
            raise SecurityError("Apocrypha (FFI) is disabled by system dogma.")

        clean = self._clean_lib_name(lib_name)
        if (
            lib_name not in self.security.whitelist
            and clean not in self.security.whitelist
        ):
            raise SecurityError(
                f"Security Violation: Library '{lib_name}' is not permitted."
            )

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

    def bind_function(
        self, lib_name: str, func_name: str, arg_types: List[str], ret_type: str
    ) -> ForeignFunction:
        clean = self._clean_lib_name(lib_name)
        allowed_funcs = (
            self.security.whitelist.get(lib_name)
            or self.security.whitelist.get(clean)
            or set()
        )
        if func_name not in allowed_funcs:
            raise SecurityError(
                f"Security Violation: Function '{func_name}' in '{lib_name}' is forbidden."
            )

        filename = self.load_library(lib_name)
        lib = self.libs[filename]
        try:
            func = getattr(lib, func_name)
        except AttributeError:
            raise LogosError(f"Schism: Symbol '{func_name}' not found in '{filename}'.")

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
        if isinstance(val, (bytes, bytearray, str)):
            return ctypes.c_char_p
        if isinstance(val, bool):
            return ctypes.c_bool
        if isinstance(val, (int, float)):
            return ctypes.c_double
        return ctypes.c_double
