from __future__ import annotations


class LogosError(Exception):
    """Base exception for the Logos runtime."""

    def __init__(
        self,
        message: str,
        category: str = "RuntimeError",
        line: int | None = None,
        column: int | None = None,
        source_file: str | None = None,
    ) -> None:
        super().__init__(message)
        self.message = message
        self.category = category
        self.line = line
        self.column = column
        self.source_file = source_file


class SecurityError(LogosError):
    """Raised when a program attempts a forbidden action."""

    def __init__(
        self,
        message: str,
        line: int | None = None,
        column: int | None = None,
        source_file: str | None = None,
    ) -> None:
        super().__init__(
            message,
            category="SecurityError",
            line=line,
            column=column,
            source_file=source_file,
        )