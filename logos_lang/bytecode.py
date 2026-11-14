from __future__ import annotations

from dataclasses import dataclass
from enum import Enum, auto
from typing import TYPE_CHECKING, Any, List, cast

from lark import Tree

from .exceptions import LogosError
from .types import TypeCanon

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
    MOD = auto()
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

    PUSH_SCOPE = auto()
    POP_SCOPE = auto()


@dataclass
class Instruction:
    opcode: OpCode
    arg: Any = None
    line: int | None = None
    column: int | None = None


@dataclass(frozen=True)
class BytecodeProgram:
    instructions: List[Instruction]

    def to_dict(self) -> dict[str, Any]:
        return {
            "instructions": [
                {
                    "op": instruction.opcode.name,
                    "arg": instruction.arg,
                    "line": instruction.line,
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
        self._position: tuple[int | None, int | None] = (None, None)

        for statement in tree.children:
            if not isinstance(statement, Tree):
                raise BytecodeUnsupported("Unexpected token in statement stream.")
            self._compile_statement(statement)

        self._emit(OpCode.HALT)
        return BytecodeProgram(instructions=list(self._instructions))

    def _emit(self, opcode: OpCode, arg: Any = None) -> int:
        line, column = self._position
        self._instructions.append(Instruction(opcode=opcode, arg=arg, line=line, column=column))
        return len(self._instructions) - 1

    def _patch(self, index: int, arg: Any) -> None:
        self._instructions[index].arg = arg

    def _compile_statement(self, node: Tree[Any]) -> None:
        meta = getattr(node, "meta", None)
        if meta is not None and not getattr(meta, "empty", True):
            self._position = (meta.line, meta.column)
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
            self._emit(OpCode.PUSH_SCOPE)
            for statement in node.children:
                if not isinstance(statement, Tree):
                    raise BytecodeUnsupported("Invalid token in block.")
                self._compile_statement(statement)
            self._emit(OpCode.POP_SCOPE)
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
            from .types import unescape_string
            raw = str(node.children[0]) if node.children else '""'
            self._emit(OpCode.PUSH_CONST, unescape_string(raw[1:-1]))
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

        if rule in {"add", "sub", "mul", "div", "mod", "eq", "ne", "lt", "gt", "le", "ge"}:
            self._compile_expr(self._require_tree_child(node, 0))
            self._compile_expr(self._require_tree_child(node, 1))
            op_map = {
                "add": OpCode.ADD,
                "sub": OpCode.SUB,
                "mul": OpCode.MUL,
                "div": OpCode.DIV,
                "mod": OpCode.MOD,
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
    """Stack VM for executing Logos bytecode programs.

    Language semantics (operators, equality, casts, calls, type enforcement, output
    formatting) are delegated to the owning ``LogosInterpreter`` so both engines share one
    implementation; the VM only owns control flow and the operand stack.
    """

    _BINARY_OPS = {
        OpCode.ADD: "add",
        OpCode.SUB: "sub",
        OpCode.MUL: "mul",
        OpCode.DIV: "div",
        OpCode.MOD: "mod",
        OpCode.LT: "lt",
        OpCode.GT: "gt",
        OpCode.LE: "le",
        OpCode.GE: "ge",
    }

    def __init__(self, interpreter: "LogosInterpreter"):
        self._interpreter = interpreter

    def run(self, program: BytecodeProgram) -> Any:
        interp = self._interpreter
        scope_depth = len(interp.scope.stack)
        type_depth = len(interp._type_stack)
        self._current: Instruction | None = None
        try:
            return self._execute(program)
        except LogosError as exc:
            if self._current is not None:
                exc.attach_location(
                    self._current.line, self._current.column, interp._current_file
                )
            raise
        finally:
            # Leave no dangling block frames behind if execution aborted mid-block.
            del interp.scope.stack[scope_depth:]
            del interp._type_stack[type_depth:]

    def _execute(self, program: BytecodeProgram) -> Any:
        interp = self._interpreter
        stack: List[Any] = []
        ip = 0
        instructions = program.instructions

        while ip < len(instructions):
            instruction = instructions[ip]
            self._current = instruction
            opcode = instruction.opcode

            if opcode == OpCode.PUSH_CONST:
                stack.append(instruction.arg)
                ip += 1
                continue

            if opcode == OpCode.LOAD_VAR:
                stack.append(interp.scope.get(cast(str, instruction.arg)))
                ip += 1
                continue

            if opcode == OpCode.INSCRIBE:
                name, declared_type = cast(tuple[str, str | None], instruction.arg)
                value = self._pop(stack, opcode)
                if declared_type is not None:
                    interp._declare_type(name, declared_type)
                interp._enforce_declared_type(name, value)
                interp.scope.declare(name, value)
                ip += 1
                continue

            if opcode == OpCode.AMEND:
                name = cast(str, instruction.arg)
                value = self._pop(stack, opcode)
                interp._enforce_declared_type(name, value)
                interp.scope.mutate(name, value)
                ip += 1
                continue

            if opcode == OpCode.PROCLAIM:
                interp._emit("☩", interp._format_value(self._pop(stack, opcode)))
                ip += 1
                continue

            if opcode == OpCode.POP:
                self._pop(stack, opcode)
                ip += 1
                continue

            binary_op = self._BINARY_OPS.get(opcode)
            if binary_op is not None:
                right, left = self._pop2(stack, opcode)
                stack.append(interp._eval_binary_op(binary_op, left, right))
                ip += 1
                continue

            if opcode == OpCode.NEG:
                val = self._pop(stack, opcode)
                val_t = TypeCanon.get_type_of_value(val)
                if val_t not in TypeCanon.NUMERIC:
                    raise LogosError(f"Canon Error: Unary '-' expects numeric type, got {val_t}.")
                stack.append(-val)
                ip += 1
                continue

            if opcode in (OpCode.EQ, OpCode.NE):
                right, left = self._pop2(stack, opcode)
                equal = TypeCanon.values_equal(left, right)
                stack.append(equal if opcode == OpCode.EQ else not equal)
                ip += 1
                continue

            if opcode == OpCode.CALL:
                func_name, arg_count = cast(tuple[str, int], instruction.arg)
                args = self._pop_n(stack, arg_count, opcode)
                stack.append(interp._call_by_name(func_name, args))
                ip += 1
                continue

            if opcode == OpCode.BUILD_LIST:
                count = cast(int, instruction.arg)
                stack.append(self._pop_n(stack, count, opcode))
                ip += 1
                continue

            if opcode == OpCode.CAST:
                target = cast(str, instruction.arg)
                stack.append(interp._cast_value(self._pop(stack, opcode), target))
                ip += 1
                continue

            if opcode == OpCode.INPUT:
                prompt = str(self._pop(stack, opcode))
                try:
                    stack.append(interp.io.read_input(prompt))
                except Exception:
                    stack.append(input(prompt))
                ip += 1
                continue

            if opcode == OpCode.JUMP:
                ip = cast(int, instruction.arg)
                continue

            if opcode == OpCode.JUMP_IF_FALSE:
                condition = self._pop(stack, opcode)
                interp._enforce_value_type(condition, "Bool", context="jump condition")
                if not condition:
                    ip = cast(int, instruction.arg)
                    continue
                ip += 1
                continue

            if opcode == OpCode.PUSH_SCOPE:
                interp._push_block_scope()
                ip += 1
                continue

            if opcode == OpCode.POP_SCOPE:
                interp._pop_block_scope()
                ip += 1
                continue

            if opcode == OpCode.HALT:
                return stack[-1] if stack else None

            raise LogosError(f"Schism: Unknown VM opcode '{opcode}'.")

        return stack[-1] if stack else None

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
