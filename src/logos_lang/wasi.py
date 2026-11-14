from __future__ import annotations

import json
import os
import subprocess
from dataclasses import dataclass
from pathlib import Path

from .bytecode import BytecodeProgram
from .exceptions import LogosError


@dataclass(frozen=True)
class WasiArtifact:
    bytecode_path: str
    module_path: str


class WasiExecutionBridge:
    """Bridge for WASI-hosted execution of Logos bytecode.

    This bridge writes bytecode artifacts in a stable JSON contract and can
    invoke an external WASI runtime module when one is provided.
    """

    def __init__(self, module_path: str | None = None, wasmtime_bin: str | None = None) -> None:
        self.module_path = module_path or os.environ.get("LOGOS_WASI_MODULE", "")
        self.wasmtime_bin = wasmtime_bin or os.environ.get("LOGOS_WASMTIME_BIN", "wasmtime")

    @staticmethod
    def emit_bytecode(program: BytecodeProgram, output_path: str) -> str:
        path = Path(output_path)
        path.parent.mkdir(parents=True, exist_ok=True)
        payload = json.dumps(program.to_dict(), indent=2)
        path.write_text(payload, encoding="utf-8")
        return str(path)

    def execute(self, artifact: WasiArtifact, script_path: str) -> int:
        if not artifact.module_path:
            raise LogosError(
                "WASI target requested but no WASI module path was configured. "
                "Set LOGOS_WASI_MODULE or pass --wasi-module."
            )

        module = Path(artifact.module_path)
        if not module.exists():
            raise LogosError(f"WASI module not found: {module}")

        command = [
            self.wasmtime_bin,
            str(module),
            artifact.bytecode_path,
            script_path,
        ]
        try:
            completed = subprocess.run(command, check=False, text=True, capture_output=True)
        except FileNotFoundError as exc:
            raise LogosError(
                "WASI execution requested but wasmtime was not found. "
                "Install wasmtime or set LOGOS_WASMTIME_BIN."
            ) from exc

        if completed.stdout:
            print(completed.stdout, end="")
        if completed.stderr:
            print(completed.stderr, end="")

        if completed.returncode != 0:
            raise LogosError(f"WASI runtime failed with exit code {completed.returncode}.")
        return completed.returncode
