"""Logos entrypoint module exposing the public API and CLI."""

import argparse
import ctypes
import json
import os
import sys
from pathlib import Path

from lark import Lark

from logos_lang import (
    LOGOS_GRAMMAR,
    ConsoleIO,
    FFIManager,
    ForeignFunction,
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
    WasiArtifact,
    WasiExecutionBridge,
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


def _load_trusted_lsp_types(path: str | None) -> dict[str, str]:
    if not path:
        return {}

    file_path = Path(path)
    if not file_path.exists():
        raise LogosError(f"LSP type-elision file not found: {file_path}")

    payload = json.loads(file_path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise LogosError("LSP type-elision file must be a JSON object of {name: type}.")

    out: dict[str, str] = {}
    for key, value in payload.items():
        if isinstance(key, str) and isinstance(value, str):
            out[key] = value
    return out


def _default_bytecode_path(entry_path: str) -> str:
    source = Path(entry_path)
    out_dir = source.parent / ".logos"
    out_dir.mkdir(parents=True, exist_ok=True)
    return str(out_dir / f"{source.stem}.bytecode.json")


def main():
    parser = argparse.ArgumentParser(description="Logos Liturgical Interpreter")
    parser.add_argument("script", nargs="?", help="Path to the liturgy file")
    parser.add_argument("--unsafe-ffi", action="store_true", help="Enable permissive FFI bindings")
    parser.add_argument(
        "--allow-lib", action="append", default=[], help="Whitelist library for FFI"
    )
    parser.add_argument(
        "--allow-unsafe-pointers",
        action="store_true",
        help="Allow pointer-like FFI types such as Text/String",
    )
    parser.add_argument(
        "--ffi-backend",
        choices=["ctypes", "rust", "wasm"],
        default="ctypes",
        help="Select Apocrypha backend policy. Non-ctypes backends require external bridge integration.",
    )
    parser.add_argument(
        "--allow-inferred-ffi-signatures",
        action="store_true",
        help="Allow runtime inference of Apocrypha arg types when no signature is declared.",
    )
    parser.add_argument(
        "--require-os-sandbox-for-ffi",
        action="store_true",
        help="Require OS-level sandbox attestation before any Apocrypha library can load.",
    )
    parser.add_argument(
        "--sandbox-attestation-env",
        default="LOGOS_OS_SANDBOX",
        help="Environment variable used to attest OS-level sandboxing when required.",
    )
    parser.add_argument(
        "--execution-engine",
        choices=["visitor", "vm-hybrid", "vm", "vm-strict"],
        default="vm-hybrid",
        help="Execution engine: classic AST visitor, hybrid VM fallback, or strict VM-only mode.",
    )
    parser.add_argument(
        "--disable-static-type-elision",
        action="store_true",
        help="Disable static pre-pass that elides provably safe global type checks.",
    )
    parser.add_argument(
        "--lsp-type-elision-file",
        default="",
        help="JSON map of trusted {variable: type} facts from LSP validation.",
    )
    parser.add_argument(
        "--emit-bytecode",
        default="",
        help="Optional output path to write lowered Logos bytecode JSON.",
    )
    parser.add_argument(
        "--execution-target",
        choices=["python", "wasi"],
        default="python",
        help="Execution target backend. 'wasi' emits bytecode and invokes an external WASI runtime.",
    )
    parser.add_argument(
        "--wasi-module",
        default="",
        help="Path to WASI runtime module (.wasm) used when --execution-target wasi.",
    )
    args = parser.parse_args()

    security = SecurityContext.permissive() if args.unsafe_ffi else SecurityContext.strict()

    if args.allow_lib:
        security.allow_ffi = True
        for lib in args.allow_lib:
            if lib not in security.whitelist:
                security.whitelist[lib] = set()
        if any(len(security.whitelist.get(lib, set())) == 0 for lib in args.allow_lib):
            print("☩ Warning: Library allowed via CLI but no functions whitelisted.")

    if args.allow_unsafe_pointers:
        security.allow_unsafe_pointers = True

    security.ffi_backend = args.ffi_backend
    security.allow_inferred_ffi_signatures = args.allow_inferred_ffi_signatures
    security.require_os_sandbox_for_ffi = args.require_os_sandbox_for_ffi
    security.sandbox_attestation_env = args.sandbox_attestation_env

    trusted_lsp_types = _load_trusted_lsp_types(args.lsp_type_elision_file)

    interpreter = LogosInterpreter(
        security=security,
        io_handler=ConsoleIO(),
        execution_engine=args.execution_engine,
        enable_static_type_elision=not args.disable_static_type_elision,
        trusted_lsp_types=trusted_lsp_types,
    )

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
        tree = parser.parse(source)

        bytecode_output_path = args.emit_bytecode or ""
        compiled_program = None
        if bytecode_output_path or args.execution_target == "wasi":
            compiled_program = interpreter.compile_bytecode(tree)
            if not bytecode_output_path:
                bytecode_output_path = _default_bytecode_path(entry_path)
            WasiExecutionBridge.emit_bytecode(compiled_program, bytecode_output_path)

        if args.execution_target == "wasi":
            if compiled_program is None:
                raise LogosError("WASI execution requires a compiled bytecode program.")
            bridge = WasiExecutionBridge(module_path=args.wasi_module or None)
            artifact = WasiArtifact(
                bytecode_path=bytecode_output_path,
                module_path=bridge.module_path,
            )
            bridge.execute(artifact, entry_path)
            return

        interpreter.visit(tree)
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
