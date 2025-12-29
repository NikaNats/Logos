import os
import sys
import time
from typing import Any, Dict, List, TextIO, Union, TYPE_CHECKING

from .exceptions import LogosError

if TYPE_CHECKING:
    from .scope import ScopeManager


class StdLib:
    def __init__(self, base_path: str):
        self.base_path = base_path
        self._fds: Dict[int, TextIO] = {}
        self._next_fd = 3

    def register_into(self, scope: "ScopeManager"):
        scope.register_builtin("now", lambda: int(time.time() * 1000))
        scope.register_builtin("env", lambda k: os.environ.get(str(k), ""))
        scope.register_builtin("__sys_sleep", lambda ms: time.sleep(float(ms) / 1000.0))
        scope.register_builtin("__sys_exit", lambda c: sys.exit(int(c)))
        scope.register_builtin("__sys_open", self._open)
        scope.register_builtin("__sys_close", self._close)
        scope.register_builtin("__sys_write", self._write)
        scope.register_builtin("__sys_read", self._read)
        scope.register_builtin("measure", self._measure)
        scope.register_builtin("append", self._append)
        scope.register_builtin("extract", self._extract)
        scope.register_builtin("purge", self._purge)
        scope.register_builtin("__sys_str", str)
        scope.register_builtin("argv", sys.argv[2:] if len(sys.argv) > 2 else [])

    def _open(self, path: str, mode: Union[int, str]) -> int:
        try:
            base = os.path.abspath(self.base_path)
            abs_path = os.path.abspath(os.path.join(base, str(path)))
            if os.path.commonpath([base, abs_path]) != base:
                raise LogosError("Path traversal blocked")
            mode_str = {0: "r", 1: "w", 2: "a"}.get(int(mode), "r")
            fd = self._next_fd
            self._fds[fd] = open(abs_path, mode_str, encoding="utf-8")
            self._next_fd += 1
            return fd
        except Exception:
            return 0

    def _close(self, fd: int):
        f = self._fds.pop(int(fd), None)
        if f:
            f.close()

    def _write(self, fd: int, content: str):
        f = self._fds.get(int(fd))
        if f:
            f.write(str(content))
            f.flush()
            return True
        return False

    def _read(self, fd: int, length: int):
        f = self._fds.get(int(fd))
        if not f:
            return ""
        return f.read() if int(length) < 0 else f.read(int(length))

    @staticmethod
    def _measure(x: Any) -> int:
        return len(x) if hasattr(x, "__len__") else 0

    @staticmethod
    def _append(lst: List, item: Any):
        if isinstance(lst, list):
            lst.append(item)
        return lst

    @staticmethod
    def _extract(lst: List):
        return lst.pop() if isinstance(lst, list) and lst else None

    @staticmethod
    def _purge(lst: List):
        if isinstance(lst, list):
            lst.clear()
