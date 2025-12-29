"""Logos entrypoint module exposing the public API and CLI."""

import argparse
import ctypes
import os
import sys

from lark import Lark

from logos_lang import (
    LOGOS_GRAMMAR,
    ConsoleIO,
    FFIManager,
    IOHandler,
    LogosError,
    LogosInterpreter,
    Module,
    ModuleFunction,
    ModuleManager,
    ReturnValue,
    ScopeManager,
    SecurityContext,
    SecurityError,
    StdLib,
    TailCall,
    TypeCanon,
    UserFunction,
    ForeignFunction,
)

__all__ = [
    "LOGOS_GRAMMAR",
    "LogosError",
    "SecurityError",
    "IOHandler",
    "ConsoleIO",
    "SecurityContext",
    "UserFunction",
    "ModuleFunction",
    "TailCall",
    "ReturnValue",
    "ForeignFunction",
    "ScopeManager",
    "FFIManager",
    "StdLib",
    "Module",
    "ModuleManager",
    "TypeCanon",
    "LogosInterpreter",
    "run_repl",
    "main",
    "Lark",
    "os",
    "sys",
    "ctypes",
]


def run_repl(interpreter: LogosInterpreter):  # pragma: no cover
    print("☩ Logos Interactive Confessional v2.0 ☩")
    print("☩ Type 'silence;' to pass, 'exit' to depart.")
    parser = Lark(LOGOS_GRAMMAR, parser="lalr", start="statement")
    while True:
        try:
            text = interpreter.io.read_input(">> ").strip()
            if not text:
                continue
            if text in ("exit", "quit", "depart(0);"):
                break
            tree = parser.parse(text)
            result = interpreter.visit(tree)
            if isinstance(result, ReturnValue):
                result = result.value
            if result is not None:
                interpreter.io.emit("=>", str(result))
        except (LogosError, Exception) as e:
            interpreter.io.emit("Anathema:", str(e))


def main():
    parser = argparse.ArgumentParser(description="Logos Liturgical Interpreter")
    parser.add_argument("script", nargs="?", help="Path to the liturgy file")
    parser.add_argument(
        "--unsafe-ffi", action="store_true", help="Enable permissive FFI bindings"
    )
    parser.add_argument(
        "--allow-lib", action="append", default=[], help="Whitelist library for FFI"
    )
    parser.add_argument(
        "--allow-unsafe-pointers",
        action="store_true",
        help="Allow pointer-like FFI types such as Text/String",
    )
    args = parser.parse_args()

    security = (
        SecurityContext.permissive() if args.unsafe_ffi else SecurityContext.strict()
    )

    if args.allow_lib:
        security.allow_ffi = True
        for lib in args.allow_lib:
            if lib not in security.whitelist:
                security.whitelist[lib] = set()
        if any(len(security.whitelist.get(lib, set())) == 0 for lib in args.allow_lib):
            print("☩ Warning: Library allowed via CLI but no functions whitelisted.")

    if args.allow_unsafe_pointers:
        security.allow_unsafe_pointers = True

    interpreter = LogosInterpreter(security=security, io_handler=ConsoleIO())

    if not args.script:
        run_repl(interpreter)
        return

    entry_path = os.path.abspath(args.script)
    interpreter.base_path = os.path.dirname(entry_path)
    interpreter.stdlib.base_path = interpreter.base_path
    interpreter._current_file = entry_path

    try:
        with open(entry_path, "r", encoding="utf-8") as f:
            source = f.read()
        parser = Lark(LOGOS_GRAMMAR, parser="lalr")
        interpreter.visit(parser.parse(source))
        try:
            main_func = interpreter.scope.get("main")
        except LogosError:
            main_func = None
        if isinstance(main_func, UserFunction):
            interpreter._invoke_user_function(main_func, [])
    except Exception as e:
        try:
            print(f"☨ FATAL ERROR ☨\n{e}")
        except UnicodeEncodeError:
            print(f"FATAL ERROR\n{e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
