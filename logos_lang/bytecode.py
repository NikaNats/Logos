from __future__ import annotations

from dataclasses import dataclass
from enum import Enum, auto
from typing import TYPE_CHECKING, Any, List, cast

from lark import Tree

from .exceptions import LogosError
from .models import ForeignFunction, ModuleFunction, UserFunction

if TYPE_CHECKING:
    from .interpreter import LogosInterpreter


class BytecodeUnsupported(LogosError):
    """Raised when the compiler encounters a construct outside VM coverage."""


class OpCode(Enum):
    PUSH_CONST = auto()
    LOAD_VAR = auto()
    INSCRIBE = auto()
    AMEND = auto()
    PROCLAIM = auto()
    POP = auto()

    ADD = auto()
    SUB = auto()
    MUL = auto()
    DIV = auto()
    NEG = auto()

    EQ = auto()
    NE = auto()
    LT = auto()
    GT = auto()
    LE = auto()
    GE = auto()

    CALL = auto()
    BUILD_LIST = auto()
    CAST = auto()
    INPUT = auto()

    JUMP = auto()
    JUMP_IF_FALSE = auto()
    HALT = auto()


@dataclass
class Instruction:
    opcode: OpCode
    arg: Any = None


@dataclass(frozen=True)
class BytecodeProgram:
    instructions: List[Instruction]

    def to_dict(self) -> dict[str, Any]:
        return {
            "instructions": [
                {
                    "op": instruction.opcode.name,
                    "arg": instruction.arg,
                }
                for instruction in self.instructions
            ]
        }


class BytecodeCompiler:
    """Lower a supported Logos AST subset into linear bytecode."""

    def compile(self, tree: Any) -> BytecodeProgram:
        if not isinstance(tree, Tree) or tree.data != "start":
            raise BytecodeUnsupported("Bytecode compilation requires a 'start' tree.")

        self._instructions: List[Instruction] = []

        for statement in tree.children:
            if not isinstance(statement, Tree):
                raise BytecodeUnsupported("Unexpected token in statement stream.")
            self._compile_statement(statement)

        self._emit(OpCode.HALT)
        return BytecodeProgram(instructions=list(self._instructions))

    def _emit(self, opcode: OpCode, arg: Any = None) -> int:
        self._instructions.append(Instruction(opcode=opcode, arg=arg))
        return len(self._instructions) - 1

    def _patch(self, index: int, arg: Any) -> None:
        self._instructions[index].arg = arg

    def _compile_statement(self, node: Tree[Any]) -> None:
        rule = node.data

        if rule == "proclaim":
            self._compile_expr(self._require_tree_child(node, 0))
            self._emit(OpCode.PROCLAIM)
            return

        if rule == "inscribe":
            self._compile_inscribe(node)
            return

        if rule == "amend":
            self._compile_amend(node)
            return

        if rule == "expr_stmt":
            self._compile_expr(self._require_tree_child(node, 0))
            self._emit(OpCode.POP)
            return

        if rule == "silence":
            return

        if rule == "block":
            for statement in node.children:
                if not isinstance(statement, Tree):
                    raise BytecodeUnsupported("Invalid token in block.")
                self._compile_statement(statement)
            return

        if rule == "discernment":
            self._compile_discernment(node)
            return

        if rule == "chant":
            self._compile_chant(node)
            return

        raise BytecodeUnsupported(f"Statement '{rule}' is not yet supported by VM lowering.")

    def _compile_inscribe(self, node: Tree[Any]) -> None:
        if len(node.children) not in {2, 3}:
            raise BytecodeUnsupported("Malformed inscribe statement.")

        name = str(node.children[0])
        declared_type = str(node.children[1]) if len(node.children) == 3 else None
        expr_index = 2 if declared_type is not None else 1

        expr_node = self._require_tree_child(node, expr_index)
        self._compile_expr(expr_node)
        self._emit(OpCode.INSCRIBE, (name, declared_type))

    def _compile_amend(self, node: Tree[Any]) -> None:
        if len(node.children) != 2:
            raise BytecodeUnsupported("Malformed amend statement.")

        target = self._require_tree_child(node, 0)
        if target.data != "mut_var" or not target.children:
            raise BytecodeUnsupported("VM currently supports amend only for direct variables.")

        name = str(target.children[0])
        self._compile_expr(self._require_tree_child(node, 1))
        self._emit(OpCode.AMEND, name)

    def _compile_discernment(self, node: Tree[Any]) -> None:
        if len(node.children) != 3:
            raise BytecodeUnsupported("Malformed discernment statement.")

        condition = self._require_tree_child(node, 0)
        then_block = self._require_tree_child(node, 1)
        else_block = self._require_tree_child(node, 2)

        self._compile_expr(condition)
        jump_false_idx = self._emit(OpCode.JUMP_IF_FALSE, -1)
        self._compile_statement(then_block)
        jump_end_idx = self._emit(OpCode.JUMP, -1)

        else_start = len(self._instructions)
        self._patch(jump_false_idx, else_start)
        self._compile_statement(else_block)

        end = len(self._instructions)
        self._patch(jump_end_idx, end)

    def _compile_chant(self, node: Tree[Any]) -> None:
        if len(node.children) != 2:
            raise BytecodeUnsupported("Malformed chant statement.")

        condition = self._require_tree_child(node, 0)
        body = self._require_tree_child(node, 1)

        loop_start = len(self._instructions)
        self._compile_expr(condition)
        jump_end_idx = self._emit(OpCode.JUMP_IF_FALSE, -1)
        self._compile_statement(body)
        self._emit(OpCode.JUMP, loop_start)

        loop_end = len(self._instructions)
        self._patch(jump_end_idx, loop_end)

    def _compile_expr(self, node: Tree[Any]) -> None:
        rule = node.data

        if rule == "number":
            literal = str(node.children[0]) if node.children else "0"
            value: int | float = float(literal) if "." in literal else int(literal)
            self._emit(OpCode.PUSH_CONST, value)
            return

        if rule == "string":
            raw = str(node.children[0]) if node.children else '""'
            self._emit(OpCode.PUSH_CONST, raw[1:-1].replace("\\n", "\n"))
            return

        if rule == "verily":
            self._emit(OpCode.PUSH_CONST, True)
            return

        if rule == "nay":
            self._emit(OpCode.PUSH_CONST, False)
            return

        if rule == "var":
            if not node.children:
                raise BytecodeUnsupported("Malformed var expression.")
            self._emit(OpCode.LOAD_VAR, str(node.children[0]))
            return

        if rule in {"add", "sub", "mul", "div", "eq", "ne", "lt", "gt", "le", "ge"}:
            self._compile_expr(self._require_tree_child(node, 0))
            self._compile_expr(self._require_tree_child(node, 1))
            op_map = {
                "add": OpCode.ADD,
                "sub": OpCode.SUB,
                "mul": OpCode.MUL,
                "div": OpCode.DIV,
                "eq": OpCode.EQ,
                "ne": OpCode.NE,
                "lt": OpCode.LT,
                "gt": OpCode.GT,
                "le": OpCode.LE,
                "ge": OpCode.GE,
            }
            self._emit(op_map[rule])
            return

        if rule == "neg":
            self._compile_expr(self._require_tree_child(node, 0))
            self._emit(OpCode.NEG)
            return

        if rule == "call":
            self._compile_call(node)
            return

        if rule == "procession":
            for child in node.children:
                if not isinstance(child, Tree):
                    raise BytecodeUnsupported("Invalid procession element.")
                self._compile_expr(child)
            self._emit(OpCode.BUILD_LIST, len(node.children))
            return

        if rule == "transfigure":
            self._compile_expr(self._require_tree_child(node, 0))
            target = str(node.children[1]) if len(node.children) > 1 else ""
            self._emit(OpCode.CAST, target)
            return

        if rule == "supplicate":
            self._compile_expr(self._require_tree_child(node, 0))
            self._emit(OpCode.INPUT)
            return

        if rule == "atom":
            self._compile_expr(self._require_tree_child(node, 0))
            return

        raise BytecodeUnsupported(f"Expression '{rule}' is not yet supported by VM lowering.")

    def _compile_call(self, node: Tree[Any]) -> None:
        if not node.children:
            raise BytecodeUnsupported("Malformed call expression.")

        func_name = str(node.children[0])
        arg_count = 0

        if len(node.children) > 1:
            args_tree = self._require_tree_child(node, 1)
            if args_tree.data != "args":
                raise BytecodeUnsupported("Malformed call argument list.")
            for arg in args_tree.children:
                if not isinstance(arg, Tree):
                    raise BytecodeUnsupported("Invalid call argument token.")
                self._compile_expr(arg)
                arg_count += 1

        self._emit(OpCode.CALL, (func_name, arg_count))

    @staticmethod
    def _require_tree_child(node: Tree[Any], index: int) -> Tree[Any]:
        try:
            child = node.children[index]
        except IndexError as exc:
            raise BytecodeUnsupported("Malformed AST shape during bytecode lowering.") from exc

        if not isinstance(child, Tree):
            raise BytecodeUnsupported("Unexpected token where tree node was required.")
        return child


class BytecodeVM:
    """Stack VM for executing Logos bytecode programs."""

    def __init__(self, interpreter: "LogosInterpreter"):
        self._interpreter = interpreter

    def run(self, program: BytecodeProgram) -> Any:
        stack: List[Any] = []
        ip = 0
        instructions = program.instructions

        while ip < len(instructions):
            instruction = instructions[ip]
            opcode = instruction.opcode

            if opcode == OpCode.PUSH_CONST:
                stack.append(instruction.arg)
                ip += 1
                continue

            if opcode == OpCode.LOAD_VAR:
                stack.append(self._interpreter.scope.get(cast(str, instruction.arg)))
                ip += 1
                continue

            if opcode == OpCode.INSCRIBE:
                name, declared_type = cast(tuple[str, str | None], instruction.arg)
                value = self._pop(stack, opcode)
                if declared_type is not None:
                    self._interpreter._declare_type(name, declared_type)
                self._interpreter._enforce_declared_type(name, value)
                self._interpreter.scope.declare(name, value)
                ip += 1
                continue

            if opcode == OpCode.AMEND:
                name = cast(str, instruction.arg)
                value = self._pop(stack, opcode)
                self._interpreter._enforce_declared_type(name, value)
                self._interpreter.scope.mutate(name, value)
                ip += 1
                continue

            if opcode == OpCode.PROCLAIM:
                value = self._pop(stack, opcode)
                prefix = "Verily" if value is True else "Nay" if value is False else str(value)
                self._interpreter._emit("☩", prefix)
                ip += 1
                continue

            if opcode == OpCode.POP:
                self._pop(stack, opcode)
                ip += 1
                continue

            if opcode == OpCode.ADD:
                right, left = self._pop2(stack, opcode)
                stack.append(left + right)
                ip += 1
                continue

            if opcode == OpCode.SUB:
                right, left = self._pop2(stack, opcode)
                stack.append(left - right)
                ip += 1
                continue

            if opcode == OpCode.MUL:
                right, left = self._pop2(stack, opcode)
                stack.append(left * right)
                ip += 1
                continue

            if opcode == OpCode.DIV:
                right, left = self._pop2(stack, opcode)
                stack.append(left / right)
                ip += 1
                continue

            if opcode == OpCode.NEG:
                stack.append(-self._pop(stack, opcode))
                ip += 1
                continue

            if opcode == OpCode.EQ:
                right, left = self._pop2(stack, opcode)
                stack.append(bool(left == right))
                ip += 1
                continue

            if opcode == OpCode.NE:
                right, left = self._pop2(stack, opcode)
                stack.append(bool(left != right))
                ip += 1
                continue

            if opcode == OpCode.LT:
                right, left = self._pop2(stack, opcode)
                stack.append(bool(left < right))
                ip += 1
                continue

            if opcode == OpCode.GT:
                right, left = self._pop2(stack, opcode)
                stack.append(bool(left > right))
                ip += 1
                continue

            if opcode == OpCode.LE:
                right, left = self._pop2(stack, opcode)
                stack.append(bool(left <= right))
                ip += 1
                continue

            if opcode == OpCode.GE:
                right, left = self._pop2(stack, opcode)
                stack.append(bool(left >= right))
                ip += 1
                continue

            if opcode == OpCode.CALL:
                func_name, arg_count = cast(tuple[str, int], instruction.arg)
                args = self._pop_n(stack, arg_count, opcode)
                stack.append(self._invoke_callable(func_name, args))
                ip += 1
                continue

            if opcode == OpCode.BUILD_LIST:
                count = cast(int, instruction.arg)
                stack.append(self._pop_n(stack, count, opcode))
                ip += 1
                continue

            if opcode == OpCode.CAST:
                target = cast(str, instruction.arg)
                value = self._pop(stack, opcode)
                stack.append(self._cast_value(value, target))
                ip += 1
                continue

            if opcode == OpCode.INPUT:
                prompt = str(self._pop(stack, opcode))
                try:
                    stack.append(self._interpreter.io.read_input(prompt))
                except Exception:
                    stack.append(input(prompt))
                ip += 1
                continue

            if opcode == OpCode.JUMP:
                ip = cast(int, instruction.arg)
                continue

            if opcode == OpCode.JUMP_IF_FALSE:
                condition = self._pop(stack, opcode)
                if not condition:
                    ip = cast(int, instruction.arg)
                    continue
                ip += 1
                continue

            if opcode == OpCode.HALT:
                return stack[-1] if stack else None

            raise LogosError(f"Schism: Unknown VM opcode '{opcode}'.")

        return stack[-1] if stack else None

    def _invoke_callable(self, func_name: str, args: List[Any]) -> Any:
        spirit = self._interpreter.scope.get(func_name)

        if isinstance(spirit, ModuleFunction):
            sync = {
                k: (v.func if isinstance(v, ModuleFunction) else v)
                for k, v in spirit.exports.items()
                if k != "__icon__"
            }
            spirit.interpreter.scope.globals.update(sync)
            return spirit.interpreter._invoke_user_function(spirit.func, args)

        if self._interpreter._recursion_depth > self._interpreter._max_recursion:
            raise LogosError("Pride: Recursion depth exceeded.")

        self._interpreter._recursion_depth += 1
        try:
            if isinstance(spirit, UserFunction):
                return self._interpreter._invoke_user_function(spirit, args)
            if isinstance(spirit, ForeignFunction):
                return self._interpreter._invoke_foreign_function(spirit, args)
            if callable(spirit):
                return spirit(*args)
            raise LogosError(f"Anathema: '{func_name}' is not callable.")
        except RecursionError as exc:
            raise LogosError("Pride: Host recursion limit reached.") from exc
        finally:
            self._interpreter._recursion_depth -= 1

    @staticmethod
    def _cast_value(value: Any, target: str) -> Any:
        if target in ("HolyInt", "Int"):
            return int(value)
        if target in ("HolyFloat", "Float"):
            return float(value)
        if target in ("Text", "String"):
            return str(value)
        return value

    @staticmethod
    def _pop(stack: List[Any], opcode: OpCode) -> Any:
        if not stack:
            raise LogosError(f"Schism: VM stack underflow during {opcode.name}.")
        return stack.pop()

    @classmethod
    def _pop2(cls, stack: List[Any], opcode: OpCode) -> tuple[Any, Any]:
        right = cls._pop(stack, opcode)
        left = cls._pop(stack, opcode)
        return right, left

    @classmethod
    def _pop_n(cls, stack: List[Any], count: int, opcode: OpCode) -> List[Any]:
        if count < 0:
            raise LogosError("Schism: VM requested negative pop count.")
        values = [cls._pop(stack, opcode) for _ in range(count)]
        values.reverse()
        return values
