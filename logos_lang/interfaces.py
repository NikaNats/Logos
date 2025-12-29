import sys
from abc import ABC, abstractmethod


def _resolve_print():
    logos_mod = sys.modules.get("logos")
    return getattr(logos_mod, "print", print)


class IOHandler(ABC):
    """Abstracts I/O so interpreters can be hosted in different frontends."""

    @abstractmethod
    def emit(self, symbol: str, message: str) -> None: ...

    @abstractmethod
    def read_input(self, prompt: str) -> str: ...


class ConsoleIO(IOHandler):
    """Console-backed I/O used by the CLI and REPL."""

    def emit(self, symbol: str, message: str) -> None:
        line = f"{symbol} {message}"
        try:
            _resolve_print()(line)
        except UnicodeEncodeError:
            fallback = "+" if symbol.strip() else ""
            _resolve_print()(f"{fallback} {message}".strip())

    def read_input(self, prompt: str) -> str:
        try:
            return input(prompt)
        except EOFError:
            return ""
