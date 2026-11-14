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

    def attach_location(
        self, line: int | None, column: int | None, source_file: str | None
    ) -> None:
        """Record where the error surfaced, keeping the innermost location if already set."""
        if self.line is None and line is not None:
            self.line = line
            self.column = column
        if self.source_file is None and source_file is not None:
            self.source_file = source_file

    def describe(self, display_file: str | None = None) -> str:
        """Render ``file:line:col: message`` using whatever location is known."""
        file_part = display_file if display_file is not None else self.source_file
        parts = [p for p in (file_part, self.line, self.column) if p is not None]
        prefix = ":".join(str(p) for p in parts)
        return f"{prefix}: {self.message}" if prefix else self.message


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