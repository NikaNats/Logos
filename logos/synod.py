import argparse
import os
import shutil
import subprocess
import sys
import tomllib
from dataclasses import dataclass


SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
TRINITY_ROOT = os.path.normpath(os.path.join(SCRIPT_DIR, ".."))


@dataclass(frozen=True)
class DependencySpec:
    name: str
    git: str | None = None
    path: str | None = None
    rev: str | None = None  # branch/tag/commit-ish


def _read_manifest(project_root: str) -> dict:
    manifest_path = os.path.join(project_root, "synod.toml")
    if not os.path.isfile(manifest_path):
        raise SystemExit(f"Synodal Error: synod.toml not found in {project_root}")
    with open(manifest_path, "rb") as f:
        return tomllib.load(f)


def _get_entry_file(project_root: str, manifest: dict) -> str:
    package = manifest.get("package", {}) if isinstance(manifest.get("package"), dict) else {}
    entry = package.get("entry")
    if isinstance(entry, str) and entry.strip():
        entry_path = entry
    else:
        # Convention-first.
        entry_path = "src/main.lg" if os.path.isfile(os.path.join(project_root, "src", "main.lg")) else "main.lg"

    entry_abs = os.path.normpath(os.path.join(project_root, entry_path))
    if not os.path.isfile(entry_abs):
        raise SystemExit(f"Synodal Error: entry file not found: {entry_abs}")
    return entry_abs


def _parse_dependencies(manifest: dict) -> list[DependencySpec]:
    deps = manifest.get("dependencies", {})
    if deps is None:
        return []
    if not isinstance(deps, dict):
        raise SystemExit("Synodal Error: [dependencies] must be a table")

    results: list[DependencySpec] = []
    for name, spec in deps.items():
        if isinstance(spec, str):
            # Shorthand: foo = "https://..."
            results.append(DependencySpec(name=name, git=spec))
            continue
        if not isinstance(spec, dict):
            raise SystemExit(f"Synodal Error: dependency '{name}' must be a string or inline table")

        git = spec.get("git")
        path = spec.get("path")
        rev = spec.get("rev") or spec.get("tag") or spec.get("branch")

        if git is not None and not isinstance(git, str):
            raise SystemExit(f"Synodal Error: dependency '{name}'.git must be a string")
        if path is not None and not isinstance(path, str):
            raise SystemExit(f"Synodal Error: dependency '{name}'.path must be a string")
        if rev is not None and not isinstance(rev, str):
            raise SystemExit(f"Synodal Error: dependency '{name}'.rev must be a string")

        if (git is None) == (path is None):
            raise SystemExit(f"Synodal Error: dependency '{name}' must specify exactly one of git or path")

        results.append(DependencySpec(name=name, git=git, path=path, rev=rev))

    return results


def _run(cmd: list[str], cwd: str) -> None:
    proc = subprocess.run(cmd, cwd=cwd, text=True)
    if proc.returncode != 0:
        raise SystemExit(f"Synodal Error: command failed ({proc.returncode}): {' '.join(cmd)}")


def _ensure_empty_dir(path: str) -> None:
    if os.path.isdir(path):
        shutil.rmtree(path)
    os.makedirs(path, exist_ok=True)


def _sync_git_dep(dep: DependencySpec, lib_root: str, project_root: str, update: bool) -> None:
    assert dep.git is not None
    dst = os.path.join(lib_root, dep.name)

    if not os.path.isdir(dst):
        os.makedirs(lib_root, exist_ok=True)
        _run(["git", "clone", dep.git, dst], cwd=project_root)
    else:
        # Existing repo; pull updates if requested.
        if update and os.path.isdir(os.path.join(dst, ".git")):
            _run(["git", "fetch", "--all", "--tags"], cwd=dst)

    if dep.rev:
        # Checkout rev (branch/tag/commit-ish) deterministically.
        _run(["git", "checkout", dep.rev], cwd=dst)

    if update and os.path.isdir(os.path.join(dst, ".git")):
        # Pull after checkout to keep branch fresh.
        _run(["git", "pull"], cwd=dst)


def _sync_path_dep(dep: DependencySpec, lib_root: str, project_root: str) -> None:
    assert dep.path is not None
    src = dep.path
    if not os.path.isabs(src):
        src = os.path.join(project_root, src)
    src = os.path.normpath(os.path.abspath(src))

    if not os.path.isdir(src):
        raise SystemExit(f"Synodal Error: dependency '{dep.name}' path not found: {src}")

    dst = os.path.join(lib_root, dep.name)
    _ensure_empty_dir(dst)

    # Copy everything (simple, deterministic) into lib/<name>
    for item in os.listdir(src):
        if item in {"target", "__pycache__"}:
            continue
        s = os.path.join(src, item)
        d = os.path.join(dst, item)
        if os.path.isdir(s):
            shutil.copytree(s, d)
        else:
            shutil.copy2(s, d)


def _resolve_dependencies(project_root: str, update: bool) -> str:
    manifest = _read_manifest(project_root)
    deps = _parse_dependencies(manifest)

    lib_root = os.path.join(project_root, "lib")
    os.makedirs(lib_root, exist_ok=True)

    for dep in deps:
        print(f"[synod] resolving {dep.name}...")
        if dep.git:
            _sync_git_dep(dep, lib_root, project_root, update=update)
        else:
            _sync_path_dep(dep, lib_root, project_root)

    return lib_root


def _compile(project_root: str) -> str:
    # Import the compiler from Trinity regardless of current working directory.
    sys.path.insert(0, SCRIPT_DIR)
    import compiler as logos_compiler  # type: ignore

    manifest = _read_manifest(project_root)
    entry = _get_entry_file(project_root, manifest)

    target_dir = os.path.join(project_root, "target")
    os.makedirs(target_dir, exist_ok=True)
    out_lbc = os.path.join(target_dir, "main.lbc")

    lib_root = _resolve_dependencies(project_root, update=False)
    os.environ["LOGOS_LIB_PATH"] = lib_root

    print(f"[synod] build: {os.path.relpath(entry, project_root)} -> target/main.lbc")
    logos_compiler.compile_and_run(entry, target="lbc", out_path=out_lbc)

    return out_lbc


def cmd_new(args: argparse.Namespace) -> None:
    project_root = os.path.abspath(args.name)
    package_name = os.path.basename(os.path.normpath(project_root))
    if os.path.exists(project_root) and os.listdir(project_root):
        raise SystemExit(f"Synodal Error: destination not empty: {project_root}")

    os.makedirs(project_root, exist_ok=True)
    os.makedirs(os.path.join(project_root, "src"), exist_ok=True)
    os.makedirs(os.path.join(project_root, "lib"), exist_ok=True)
    os.makedirs(os.path.join(project_root, "target"), exist_ok=True)

    manifest_path = os.path.join(project_root, "synod.toml")
    if not os.path.exists(manifest_path):
        with open(manifest_path, "w", encoding="utf-8") as f:
            f.write(
                "[package]\n"
                f"name = \"{package_name}\"\n"
                "version = \"0.1.0\"\n"
                "entry = \"src/main.lg\"\n\n"
                "[dependencies]\n"
            )

    main_path = os.path.join(project_root, "src", "main.lg")
    if not os.path.exists(main_path):
        with open(main_path, "w", encoding="utf-8") as f:
            f.write(
                "ministry main() -> Void {\n"
                "    behold \"Peace.\";\n"
                "} amen\n"
            )

    print(f"[synod] created: {project_root}")


def cmd_build(args: argparse.Namespace) -> None:
    project_root = os.path.abspath(args.project)
    _compile(project_root)


def cmd_run(args: argparse.Namespace) -> None:
    project_root = os.path.abspath(args.project)
    out_lbc = _compile(project_root)

    # Prefer SVM if present.
    svm = os.path.join(TRINITY_ROOT, "logos-svm", "target", "release", "logos-svm")
    if sys.platform.startswith("win"):
        svm += ".exe"

    if os.path.isfile(svm):
        print("[synod] running via SVM...")
        _run([svm, out_lbc], cwd=project_root)
        return

    # Fallback: run via Python transpilation (exec main()).
    print("[synod] SVM binary not found; running via Python transpilation...")
    sys.path.insert(0, SCRIPT_DIR)
    import compiler as logos_compiler  # type: ignore

    manifest = _read_manifest(project_root)
    entry = _get_entry_file(project_root, manifest)
    lib_root = _resolve_dependencies(project_root, update=False)
    os.environ["LOGOS_LIB_PATH"] = lib_root
    logos_compiler.compile_and_run(entry, target="python")


def cmd_update(args: argparse.Namespace) -> None:
    project_root = os.path.abspath(args.project)
    _resolve_dependencies(project_root, update=True)


def main() -> None:
    parser = argparse.ArgumentParser(prog="synod", description="Synodal Archive (LOGOS package manager)")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_new = sub.add_parser("new", help="Create a new synod project")
    p_new.add_argument("name", help="Project directory name")
    p_new.set_defaults(func=cmd_new)

    p_build = sub.add_parser("build", help="Resolve deps and compile to target/main.lbc")
    p_build.add_argument("project", nargs="?", default=os.getcwd(), help="Project root (default: cwd)")
    p_build.set_defaults(func=cmd_build)

    p_run = sub.add_parser("run", help="Build and run (SVM if available; else Python)")
    p_run.add_argument("project", nargs="?", default=os.getcwd(), help="Project root (default: cwd)")
    p_run.set_defaults(func=cmd_run)

    p_update = sub.add_parser("update", help="Update dependency checkouts")
    p_update.add_argument("project", nargs="?", default=os.getcwd(), help="Project root (default: cwd)")
    p_update.set_defaults(func=cmd_update)

    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
