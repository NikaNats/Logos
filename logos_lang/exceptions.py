class LogosError(Exception):
    """Base exception for the runtime."""

    pass


class SecurityError(LogosError):
    """Raised when a program attempts a forbidden action."""

    pass
