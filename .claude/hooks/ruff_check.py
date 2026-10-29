"""PostToolUse hook: report ruff violations *introduced* by Claude's edit to a .py file.

Diagnostics already present in the HEAD version of the file are ignored, so pre-existing
lint never pushes Claude into unrelated edits (constitution: minimal, scoped diffs).

Exit codes: 2 = new violations (fed back to Claude), 1 = hook/tool failure (shown to the
user, non-blocking), 0 = clean or not applicable.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Any


def _ruff_cmd() -> list[str] | None:
    if shutil.which("uv"):
        return ["uv", "run", "--no-sync", "--quiet", "ruff"]
    if shutil.which("ruff"):
        return ["ruff"]
    return None


def _ruff_json(
    ruff: list[str], root: Path, rel: str, stdin: str | None = None
) -> list[dict[str, Any]]:
    args = [*ruff, "check", "--output-format", "json", "--no-cache"]
    args += ["--stdin-filename", rel, "-"] if stdin is not None else [rel]
    result = subprocess.run(
        args, cwd=root, input=stdin, capture_output=True, text=True, encoding="utf-8"
    )
    if result.returncode not in (0, 1):
        raise RuntimeError(
            f"ruff exited {result.returncode}: {(result.stderr or result.stdout).strip()}"
        )
    return json.loads(result.stdout or "[]")


def _head_source(root: Path, rel: str) -> str | None:
    result = subprocess.run(
        ["git", "show", f"HEAD:{rel}"],
        cwd=root, capture_output=True, text=True, encoding="utf-8",
    )
    return result.stdout if result.returncode == 0 else None


def main() -> int:
    try:
        payload = json.load(sys.stdin)
    except json.JSONDecodeError:
        return 0

    file_path = (payload.get("tool_input") or {}).get("file_path") or ""
    if not file_path.endswith(".py"):
        return 0

    root = Path(os.environ.get("CLAUDE_PROJECT_DIR") or Path(__file__).resolve().parents[2])
    path = Path(file_path)
    if not path.is_absolute():
        path = Path(payload.get("cwd") or root) / path
    try:
        rel = path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return 0
    if not path.exists():
        return 0

    ruff = _ruff_cmd()
    if ruff is None:
        return 0

    try:
        current = _ruff_json(ruff, root, rel)
        head = _head_source(root, rel)
        baseline = _ruff_json(ruff, root, rel, stdin=head) if head is not None else []
    except (RuntimeError, json.JSONDecodeError, OSError) as exc:
        sys.stderr.write(f"ruff hook could not lint {rel}: {exc}\n")
        return 1

    allowance = Counter((d["code"], d["message"]) for d in baseline)
    new: list[dict[str, Any]] = []
    for diag in current:
        key = (diag["code"], diag["message"])
        if allowance[key] > 0:
            allowance[key] -= 1
        else:
            new.append(diag)

    if not new:
        return 0
    lines = [
        f"{rel}:{d['location']['row']}:{d['location']['column']}: {d['code']} {d['message']}"
        for d in new
    ]
    sys.stderr.write("ruff: your edit introduced new violations:\n" + "\n".join(lines) + "\n")
    return 2


if __name__ == "__main__":
    sys.exit(main())
