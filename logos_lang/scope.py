from typing import Any, Dict, List

from .exceptions import LogosError


class ScopeManager:
    def __init__(self):
        self.globals: Dict[str, Any] = {}
        self.stack: List[Dict[str, Any]] = []

    def push_frame(self, frame: Dict[str, Any]) -> None:
        self.stack.append(frame)

    def pop_frame(self) -> None:
        if self.stack:
            self.stack.pop()

    def get(self, name: str) -> Any:
        for frame in reversed(self.stack):
            if name in frame:
                return frame[name]
        if name in self.globals:
            return self.globals[name]
        raise LogosError(f"Heresy: Unknown spirit '{name}'")

    def set(self, name: str, value: Any) -> None:
        for frame in reversed(self.stack):
            if name in frame:
                frame[name] = value
                return
        if name in self.globals:
            self.globals[name] = value
            return
        if self.stack:
            self.stack[-1][name] = value
        else:
            self.globals[name] = value

    def mutate(self, name: str, value: Any) -> None:
        for frame in reversed(self.stack):
            if name in frame:
                frame[name] = value
                return
        if name in self.globals:
            self.globals[name] = value
            return
        raise LogosError(f"Heresy: Unknown spirit '{name}' for amendment")

    def declare(self, name: str, value: Any) -> None:
        if self.stack:
            self.stack[-1][name] = value
        else:
            self.globals[name] = value

    def register_builtin(self, name: str, value: Any) -> None:
        self.globals[name] = value
