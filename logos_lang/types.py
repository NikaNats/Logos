from typing import Any, Optional


class TypeCanon:
    NUMERIC = {"HolyInt", "Int", "HolyFloat", "Float", "Double"}
    TEXT = {"Text", "String"}
    BOOL = {"Bool", "Verily", "Nay"}
    LIST = {"Procession"}
    VOID = {"Void", "None"}

    @classmethod
    def get_type_of_value(cls, value: Any) -> str:
        if isinstance(value, bool):
            return "Bool"
        if isinstance(value, int):
            return "HolyInt"
        if isinstance(value, float):
            return "HolyFloat"
        if isinstance(value, str):
            return "Text"
        if isinstance(value, list):
            return "Procession"
        if value is None:
            return "Void"
        return "Mystery"

    @classmethod
    def are_compatible(cls, declared: str, actual: str) -> bool:
        if declared == actual:
            return True
        if declared in ("HolyFloat", "Float", "Double") and actual in (
            "HolyInt",
            "Int",
        ):
            return True
        if declared in cls.TEXT and actual in cls.TEXT:
            return True
        if declared in cls.BOOL and actual in cls.BOOL:
            return True
        if declared in cls.NUMERIC and actual in cls.NUMERIC:
            if declared in ("HolyInt", "Int") and actual in (
                "HolyFloat",
                "Float",
                "Double",
            ):
                return False
            return True
        return False

    @classmethod
    def resolve_binary_op(cls, op: str, left_t: str, right_t: str) -> Optional[str]:
        if op in ("add", "sub", "mul", "div", "+", "-", "*", "/"):
            if left_t in cls.TEXT and right_t in cls.TEXT and op in ("add", "+"):
                return "Text"
            if left_t in cls.NUMERIC and right_t in cls.NUMERIC:
                if op in ("div", "/"):
                    return "HolyFloat"
                if "HolyFloat" in (left_t, right_t) or "Float" in (left_t, right_t):
                    return "HolyFloat"
                return "HolyInt"
            return None

        if op in ("lt", "gt", "le", "ge", "eq", "ne", "<", ">", "<=", ">=", "is"):
            if op in ("lt", "gt", "le", "ge", "<", ">", "<=", ">="):
                if left_t in cls.NUMERIC and right_t in cls.NUMERIC:
                    return "Bool"
                return None
            return "Bool"

        return None
