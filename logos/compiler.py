import sys, os, struct, hashlib
import z3
import re
from lark import Lark, Transformer, Token, Tree
from lark.visitors import Interpreter


class CharConst:
    __slots__ = ("codepoint",)

    def __init__(self, codepoint: int):
        self.codepoint = int(codepoint)

    def __repr__(self) -> str:
        try:
            ch = chr(self.codepoint)
        except ValueError:
            ch = "?"
        return f"Char({ch!r})"

    def __eq__(self, other):
        return isinstance(other, CharConst) and self.codepoint == other.codepoint

    def __hash__(self):
        return hash(("CharConst", self.codepoint))


class ByteConst:
    __slots__ = ("value",)

    def __init__(self, value: int):
        v = int(value)
        if v < 0 or v > 255:
            raise ValueError("Byte must be in range 0..255")
        self.value = v

    def __repr__(self) -> str:
        return f"Byte(0x{self.value:02X})"

    def __eq__(self, other):
        return isinstance(other, ByteConst) and self.value == other.value

    def __hash__(self):
        return hash(("ByteConst", self.value))

CANON_TYPES = {
    "HolyInt": ["isinstance({name}, int)", "{name} >= 0"],
    "Text": ["isinstance({name}, str)"],
    "Void": [],
    "Synod": []
}

def indent(text, spaces=4):
    if not text: return ""
    return "\n".join(" " * spaces + line for line in text.split('\n'))

class SynodValidator(Interpreter):
    def __init__(self):
        self.registry = {}
        self.service_stack = [] 
        self.in_try_block = 0

    @property
    def in_service(self): return self.service_stack[-1][0] if self.service_stack else False
    @property
    def in_ministry(self): return self.service_stack[-1][1] if self.service_stack else False

    def service_def(self, tree):
        self.service_stack.append((True, False))
        self.visit_children(tree)
        self.service_stack.pop()

    def ministry_def(self, tree):
        self.service_stack.append((True, True))
        self.visit_children(tree)
        self.service_stack.pop()

    def intercessor_def(self, tree):
        self.service_stack.append((True, True))
        self.visit_children(tree)
        self.service_stack.pop()

    def essence_decl(self, tree):
        name = str(tree.children[0])
        typ = str(tree.children[1])
        if not self.in_service and typ != "Synod": 
            raise Exception("Pride Error: Global essence forbidden.")
        self._register(name, tree.children[0].line, True)
        self.visit_children(tree)

    def behold_stmt(self, tree):
        if not self.in_service:
            raise Exception(f"Sanctity Error: 'behold' forbidden outside of service/ministry at line {tree.meta.line}.")

    def import_stmt(self, tree):
        # Static linking is handled before parsing.
        return

    def absolve_stmt(self, tree):
        return

    def witness_expr(self, tree):
        if self.in_try_block == 0:
            raise Exception(f"Watchfulness Error: 'witness' requires 'try' block at line {tree.meta.line}.")

    def try_repent_stmt(self, tree):
        self.in_try_block += 1
        self.visit(tree.children[0])
        self.in_try_block -= 1
        self.visit(tree.children[2])

    def _register(self, name, line, is_essence):
        if name in self.registry: raise Exception(f"Duplicity Error: '{name}' reused at line {line}.")
        self.registry[name] = {"line": line, "used": False, "is_essence": is_essence}

    def validate_asceticism(self):
        for name, meta in self.registry.items():
            if not meta['used'] and name != 'main':
                print(f"PASTORAL WARNING: '{name}' (line {meta['line']}) is an Idle Word.")

class DiakrisisEngine(Interpreter):
    def __init__(self):
        self.solver = z3.Solver()
        self.symbols = {}
        self.symbol_types = {}
        self.custom_types = {}

    def type_def(self, tree):
        # type_def: "type" NAME "=" "essence" "{" constraint+ "}" "amen"
        # Children: [NAME, constraint, constraint, ...]
        name = str(tree.children[0])
        constraints = []
        for c in tree.children:
            if isinstance(c, Tree) and c.data == 'constraint':
                # constraint: "not" constraint_expr ";"
                # constraint_expr: bin_op | implied_bin_op
                expr_node = c.children[0]

                # Shorthand: implied_bin_op: OPERATOR expr   (implicit left = val)
                if isinstance(expr_node, Tree) and expr_node.data == 'implied_bin_op':
                    op = str(expr_node.children[0])
                    right_val = expr_node.children[1]
                    constraints.append((op, right_val))
                    continue

                # Full form: bin_op: expr OPERATOR expr
                if isinstance(expr_node, Tree) and expr_node.data == 'bin_op':
                    left = expr_node.children[0]
                    op = str(expr_node.children[1])
                    right = expr_node.children[2]

                    # Determine which side is the variable and which is the limit
                    def get_val(node):
                        curr = node
                        while isinstance(curr, Tree) and curr.data in ('expr', 'atom'):
                            if not curr.children:
                                break
                            curr = curr.children[0]
                        return curr

                    left_val = get_val(left)
                    right_val = get_val(right)

                    if isinstance(left_val, Token) and left_val.type == 'NAME':
                        constraints.append((op, right_val))
                    elif isinstance(right_val, Token) and right_val.type == 'NAME':
                        inv_op = {"<": ">", ">": "<", "==": "==", "!=": "!=", "<=": ">=", ">=": "<="}.get(op, op)
                        constraints.append((inv_op, left_val))
        self.custom_types[name] = constraints

    def import_stmt(self, tree):
        return

    def absolve_stmt(self, tree):
        # Absolution affects runtime references, not static typing.
        return

    def essence_decl(self, tree):
        # essence_decl: "essence" NAME ":" TYPE "=" expr ";"
        # Children: [NAME, TYPE, expr]
        name = str(tree.children[0])
        typ = str(tree.children[1])
        expr = tree.children[2]
        self._verify_assignment(name, typ, expr, tree.meta.line)

    def gift_decl(self, tree):
        # gift_decl: "gift" NAME (":" TYPE)? "=" expr ";"
        # Children: [NAME, expr] or [NAME, TYPE, expr]
        name = str(tree.children[0])
        if len(tree.children) == 2:
            expr = tree.children[1]
            inferred = self.infer_type(expr)
            if inferred is None:
                raise Exception(f"Diakrisis Error: Could not infer type for '{name}' at line {tree.meta.line}.")
            self._verify_assignment(name, inferred, expr, tree.meta.line)
        else:
            typ = str(tree.children[1])
            expr = tree.children[2]
            inferred = self.infer_type(expr)
            if inferred is not None and typ not in ("Synod", "Void") and typ != inferred:
                raise Exception(
                    f"Diakrisis Error: Gift '{name}' declared as '{typ}' but expression is '{inferred}' at line {tree.meta.line}."
                )
            self._verify_assignment(name, typ, expr, tree.meta.line)

    def assign_stmt(self, tree):
        # assign_stmt: assignable "=" expr ";"
        target = tree.children[0]
        expr = tree.children[1]

        # Only model plain variable assignments in Diakrisis for now.
        if isinstance(target, Token) and target.type == 'NAME':
            name = str(target)
            inferred = self.infer_type(expr)
            if inferred is not None:
                prev = self.symbol_types.get(name)
                if prev is not None and prev != inferred:
                    raise Exception(
                        f"Diakrisis Error: '{name}' was '{prev}' but assigned '{inferred}' at line {tree.meta.line}."
                    )
                if prev is None:
                    self.symbol_types[name] = inferred

            # Only model numeric (HolyInt + custom constraints) assignments in Z3.
            if name in self.symbols:
                val = self.symbols[name]
                z3_expr = self._to_z3(expr)
                self.solver.add(val == z3_expr)

    def _verify_assignment(self, name, typ, expr, line):
        # Track declared/inferred type for later inference.
        if typ is not None:
            self.symbol_types[name] = typ

        if typ == "HolyInt" or typ in self.custom_types:
            if name not in self.symbols:
                self.symbols[name] = z3.Real(name)
            
            val = self.symbols[name]
            z3_expr = self._to_z3(expr)
            
            constraints = self._get_constraints(typ)
            for op, c_expr in constraints:
                limit = self._to_z3(c_expr)
                
                # The nature is the opposite of the apophatic constraint
                if op == "<": nature = val >= limit
                elif op == ">": nature = val <= limit
                elif op == "==": nature = val != limit
                elif op == "!=": nature = val == limit
                elif op == ">=": nature = val < limit
                elif op == "<=": nature = val > limit
                else: nature = None
                
                if nature is not None:
                    self.solver.push()
                    self.solver.add(val == z3_expr)
                    self.solver.add(z3.Not(nature))
                    if self.solver.check() == z3.sat:
                        model = self.solver.model()
                        self.solver.pop()
                        raise Exception(f"Diakrisis Error: Essence '{name}' violates nature '{typ}' at line {line}. "
                                        f"Counter-example: {model}")
                    self.solver.pop()
                    self.solver.add(nature)
            
            # Add the assignment permanently to the solver's knowledge base
            self.solver.add(val == z3_expr)

        # For other primitives (Text, HolyFloat, Bool, Char, Byte) we only
        # enforce type consistency via inference (above). No Z3 constraints yet.

    def infer_type(self, expr):
        # Returns one of: HolyInt, HolyFloat, Text, Bool, Char, Byte, Synod, a structure name, or None.
        node = expr
        while isinstance(node, Tree) and node.data in ("expr", "atom") and node.children:
            # atom wraps literals and grouped exprs; expr wraps alternatives.
            node = node.children[0]

        if isinstance(node, Token):
            if node.type == "NUMBER":
                s = str(node)
                return "HolyFloat" if "." in s else "HolyInt"
            if node.type == "STRING":
                return "Text"
            if node.type == "BOOL":
                return "Bool"
            if node.type == "CHAR":
                return "Char"
            if node.type == "BYTE":
                return "Byte"
            if node.type == "NAME":
                return self.symbol_types.get(str(node))
            return None

        if isinstance(node, Tree):
            if node.data == "array_literal":
                return "Synod"
            if node.data == "struct_literal":
                # struct_literal: "new" NAME "{" field_inits? "}"
                if node.children and isinstance(node.children[0], Token):
                    return str(node.children[0])
                return None
            if node.data == "bool_literal":
                return "Bool"
            if node.data == "char_literal":
                return "Char"
            if node.data == "byte_literal":
                return "Byte"
            if node.data == "listen_expr":
                return "Text"
            if node.data == "call_expr":
                fn = str(node.children[0]) if node.children else ""
                if fn == "measure":
                    return "HolyInt"
                if fn == "passage":
                    return "Text"
                return None
            if node.data == "bin_op":
                left, op_token, right = node.children[0], str(node.children[1]), node.children[2]
                if op_token in ("==", "!=", "<", ">", "<=", ">="):
                    return "Bool"
                lt = self.infer_type(left)
                rt = self.infer_type(right)
                if op_token == "+" and lt == "Text" and rt == "Text":
                    return "Text"
                if lt in ("HolyInt", "HolyFloat") and rt in ("HolyInt", "HolyFloat"):
                    return "HolyFloat" if (lt == "HolyFloat" or rt == "HolyFloat") else "HolyInt"
                return None

        return None

    def _get_constraints(self, typ):
        if typ == "HolyInt":
            return [("<", Token('NUMBER', '0'))]
        return self.custom_types.get(typ, [])

    def _to_z3(self, tree):
        if isinstance(tree, Token):
            if tree.type == 'NUMBER': 
                try:
                    return int(tree)
                except ValueError:
                    return float(tree)
            if tree.type == 'NAME': return self.symbols.get(str(tree), 0)
            return 0
        if tree.data == 'bin_op':
            left = self._to_z3(tree.children[0])
            op = str(tree.children[1])
            right = self._to_z3(tree.children[2])
            if op == "+": return left + right
            if op == "-": return left - right
            if op == "*": return left * right
            if op == "/": return left / right
        if tree.data in ('atom', 'expr'):
            return self._to_z3(tree.children[0])
        return 0

class LogosToPython(Transformer):
    def statements(self, items): return items

    def start(self, items):
        philokalia = [
            "import asyncio, time",
            "class OntologicalError(Exception): pass",
            "class AsyncRLock:",
            "    def __init__(self):",
            "        self._lock = asyncio.Lock()",
            "        self._owner = None",
            "        self._count = 0",
            "    async def acquire(self):",
            "        me = asyncio.current_task()",
            "        if self._owner == me:",
            "            self._count += 1",
            "            return",
            "        await self._lock.acquire()",
            "        self._owner = me",
            "        self._count = 1",
            "    def release(self):",
            "        if self._owner != asyncio.current_task(): raise RuntimeError('Not owner')",
            "        self._count -= 1",
            "        if self._count == 0:",
            "            self._owner = None",
            "            self._lock.release()",
            "    def locked(self): return self._lock.locked()",
            "    async def __aenter__(self): await self.acquire(); return self",
            "    async def __aexit__(self, t, v, b): self.release()",
            "def sanctify(val): return tuple(val) if isinstance(val, list) else val",
            "class SynodalState:",
            "    def __init__(self, **kwargs):",
            "        self._data = kwargs",
            "        self._lock = asyncio.Condition(AsyncRLock())",
            "    async def petition(self, k, v, c=None):",
            "        async with self._lock:",
            "            self._data[k] = v",
            "            self._lock.notify_all()",
            "    def read(self, k): return self._data.get(k)",
            "    async def wait_for_kairos(self, p, t=None):",
            "        try:",
            "            async with self._lock:",
            "                return await asyncio.wait_for(self._lock.wait_for(p), timeout=t)",
            "        except: return False",
            "def create_synod(**kwargs): return SynodalState(**kwargs)"
        ]
        return "\n".join(philokalia) + "\n\n" + "\n".join(items[0])

    def statements(self, items): return items
    def statement(self, items): return items[0]

    def service_def(self, items):
        # service_def: "service" NAME "(" params? ")" ("->" NAME)? "{" statements "}" "amen"
        name = items[0]
        params = ""
        for it in items[1:-1]:
            if isinstance(it, str):
                # could be params string OR return type; params string contains commas or is empty
                params = it if "(" not in it else params
        if len(items) >= 3 and isinstance(items[1], str) and "," in items[1]:
            params = items[1]
        body = items[-1]
        prefix = "async "
        return f"{prefix}def {name}({params}):\n{indent_body(body)}"

    def ministry_def(self, items): return self.service_def(items)
    def intercessor_def(self, items): return self.service_def(items)

    def struct_def(self, items):
        return ""  # Archetypes are ignored in Python backend for now

    def import_stmt(self, items):
        return ""  # Static linking handled by loader

    def field_decl(self, items):
        return ""

    def params(self, items): return ", ".join(map(str, items))
    def param(self, items):
        # param: NAME (":" NAME)?
        return str(items[0])

    def args(self, items): return ", ".join(map(str, items))
    def arg(self, items):
        if len(items) == 2: return f"{items[0]}={items[1]}"
        return str(items[0])

    def essence_decl(self, items):
        name, typ, expr = str(items[0]), str(items[1]), items[2]
        expr_str = str(expr)
        if "create_synod" in expr_str:
            # Remove await if it was accidentally added by a sub-rule
            expr_str = expr_str.replace("await ", "")
            return f"global {name}\n{name} = {expr_str}"
        return f"global {name}\n{name} = {expr_str}"

    def gift_decl(self, items):
        # gift_decl: "gift" NAME (":" TYPE)? "=" expr ";"
        # items: [NAME, expr] or [NAME, TYPE, expr]
        if len(items) == 2:
            name, expr = str(items[0]), items[1]
            return f"global {name}\n{name} = {expr}"
        name, typ, expr = str(items[0]), str(items[1]), items[2]
        return f"global {name}\n{name} = {expr}"

    def assign_stmt(self, items):
        target = items[0]
        expr = items[1]
        return f"{target} = {expr}"

    def cycle_stmt(self, items):
        # cycle expr ("limit" NUMBER)? "{" statements "}" "amen"
        expr = items[0]
        limit = None
        body = None
        if len(items) == 3:
            limit = items[1]
            body = items[2]
        else:
            body = items[1]
        loop = f"while {expr}:\n{indent_body(body)}"
        return f"__lim__={limit}\n{loop}" if limit else loop


    def kairos_stmt(self, items):
        # kairos expr ("timeout" NUMBER)? "{" statements "}" ("repent" "{" statements "}")? "amen"
        expr = items[0]
        timeout = "None"
        body = None
        repent_body = None
        
        idx = 1
        if idx < len(items) and not isinstance(items[idx], list):
            timeout = items[idx]
            idx += 1
        
        if idx < len(items):
            body = items[idx]
            idx += 1
        
        if idx < len(items):
            repent_body = items[idx]
            
        # Ensure lambda doesn't have await
        lambda_expr = str(expr).replace("await ", "")
        
        # Try to find a Synod object in the expression (e.g., t.read or brotherhood.read)
        import re
        match = re.search(r'(\w+)\.read', lambda_expr)
        synod_obj = match.group(1) if match else "brotherhood"
        
        res = f"if await {synod_obj}.wait_for_kairos(lambda: {lambda_expr}, {timeout}):\n{indent_body(body)}"
        if repent_body:
            res += f"\nelse:\n{indent_body(repent_body)}"
        return res

    def wait_kairos_stmt(self, items):
        # Backward-compat: `wait until kairos ...` behaves like `kairos ...`
        return self.kairos_stmt(items)

    def try_repent_stmt(self, items):
        try_body, error_name, repent_body = items[0], items[1], items[2]
        return f"try:\n{indent_body(try_body)}\nexcept Exception as {error_name}:\n{indent_body(repent_body)}"

    def call_stmt(self, items): return items[0]
    def await_expr(self, items):
        val = str(items[0])
        if val.startswith("await "): return val
        return f"await {val}"

    def gather_expr(self, items):
        # gather needs coroutines, so we strip the auto-added 'await' from call_expr
        args = str(items[0]).replace("await ", "")
        return f"await asyncio.gather({args})"

    def fast_stmt(self, items): return f"await asyncio.sleep(float({items[0]}) / 1000.0)"
    def council_target(self, items):
        return str(items[0])

    def council_stmt(self, items):
        return f"async with {items[0]}._lock:\n{indent_body(items[-1])}"
    def behold_stmt(self, items): return f"print({items[0]})"
    def offer_stmt(self, items): return f"return {items[0]}"
    def absolve_stmt(self, items):
        # Manual nullification (best-effort in python backend)
        name = str(items[0])
        return f"{name} = None"
    def expr_stmt(self, items): return f"{items[0]}"
    def bin_op(self, items): return f"({items[0]} {items[1]} {items[2]})"

    def call_suffix(self, items):
        # call_suffix: "(" args? ")"
        return items[0] if items else ""

    def call_expr(self, items):
        # call_expr: NAME call_suffix
        name = items[0]
        args = items[1] if len(items) > 1 else ""
        return f"{name}({args})"

    def dot_access(self, items):
        # dot_access: atom "." NAME call_suffix?
        if len(items) == 2:
            return f"{items[0]}.{items[1]}"
        return f"{items[0]}.{items[1]}({items[2]})"
    def witness_expr(self, items):
        expr, typ = items[0], str(items[1])
        if typ == "HolyInt": return f"int({expr})"
        if typ == "Text": return f"str({expr})"
        if typ == "HolyFloat": return f"float({expr})"
        return f"({expr})"

    def listen_expr(self, items):
        # listen expr  -> input(prompt)
        return f"input({items[0]})"

    def bool_literal(self, items):
        # Verily/Nay -> True/False
        return "True" if str(items[0]) == "Verily" else "False"

    def char_literal(self, items):
        # Keep as 1-char Python string
        return str(items[0])

    def byte_literal(self, items):
        # 0xFF -> 255 (as int)
        return str(int(str(items[0]), 16))
    def await_expr(self, items): return f"await {items[0]}"
    def gather_expr(self, items): return f"await asyncio.gather({items[0]})"
    def expr(self, items): return items[0]
    def atom(self, items):
        if len(items) == 3: return f"({items[1]})"
        return str(items[0])

    def array_literal(self, items):
        # items: [args?]
        if not items:
            return "[]"
        return f"[{items[0]}]"

    def struct_literal(self, items):
        # new Name { field_inits }
        # Represent as dict for python backend.
        fields = items[1] if len(items) > 1 else []
        kv = ", ".join([f"{k}: {v}" for (k, v) in fields])
        return f"{{{kv}}}"

    def field_inits(self, items):
        return items

    def field_init(self, items):
        return (repr(str(items[0])), str(items[1]))

    def index_access(self, items):
        return f"{items[0]}[{items[1]}]"

    def member_assignable(self, items):
        return f"{items[0]}.{items[1]}"

    def index_assignable(self, items):
        return f"{items[0]}[{items[1]}]"
    def type_def(self, items): return ""
    def constraint(self, items): return ""
    def NAME(self, t): return str(t)
    def NUMBER(self, t): return str(t)
    def STRING(self, t): return str(t)

class LogosToBytecode(Transformer):
    def __init__(self):
        self.constants = []
        self.function_bodies = {}  # name -> raw bytearray body (may contain CALL markers)

    # --- Constants ---

    def _add_const(self, val):
        if val in self.constants:
            return self.constants.index(val)
        self.constants.append(val)
        return len(self.constants) - 1

    # --- Linker / Packaging ---
    def _package_binary(self, code: bytearray) -> bytearray:
        # Header: 'LOGOS' + Version 1 + Seal of Purity (32 bytes)
        header = b"LOGOS\x01"
        seal = hashlib.sha256(code).digest()

        cp = bytearray()
        cp.extend(struct.pack("<I", len(self.constants)))
        for c in self.constants:
            # NOTE: bool is a subclass of int in Python; check bool before int.
            if isinstance(c, bool):
                cp.append(0x04)
                cp.append(0x01 if c else 0x00)
            elif isinstance(c, ByteConst):
                cp.append(0x06)
                cp.append(c.value)
            elif isinstance(c, CharConst):
                cp.append(0x05)
                cp.extend(struct.pack("<I", c.codepoint))
            elif isinstance(c, int):
                cp.append(0x01)
                cp.extend(struct.pack("<q", c))
            elif isinstance(c, str):
                cp.append(0x02)
                encoded = c.encode('utf-8')
                cp.extend(struct.pack("<I", len(encoded)))
                cp.extend(encoded)
            elif isinstance(c, float):
                cp.append(0x03)
                cp.extend(struct.pack("<d", c))

        full_binary = bytearray()
        full_binary.extend(header)
        full_binary.extend(seal)
        full_binary.extend(cp)
        full_binary.extend(struct.pack("<I", len(code)))
        full_binary.extend(code)
        return full_binary

    def _calculate_cleaned_length(self, body: bytearray) -> int:
        # CALL marker encoding:
        #   0x90 + 4 bytes 0xFFFFFFFF + utf8(name) + 0x00
        # Cleaned form keeps: 0x90 + 4-byte resolved address
        length = 0
        i = 0
        while i < len(body):
            if body[i] == 0x90 and i + 4 < len(body) and body[i+1:i+5] == b"\xFF\xFF\xFF\xFF":
                length += 5
                i += 5
                while i < len(body) and body[i] != 0:
                    i += 1
                i += 1  # skip null
            else:
                length += 1
                i += 1
        return length

    def _clean_and_patch(self, body: bytearray, symbol_table: dict) -> bytearray:
        res = bytearray()
        i = 0
        while i < len(body):
            if body[i] == 0x90 and i + 4 < len(body) and body[i+1:i+5] == b"\xFF\xFF\xFF\xFF":
                res.append(0x90)
                i += 5
                name_chars = bytearray()
                while i < len(body) and body[i] != 0:
                    name_chars.append(body[i])
                    i += 1
                i += 1  # skip null
                target_name = name_chars.decode('utf-8')
                if target_name not in symbol_table:
                    raise Exception(f"Ontological Error: Calling unknown spirit '{target_name}'")
                res.extend(struct.pack("<I", symbol_table[target_name]))
            else:
                res.append(body[i])
                i += 1
        return res

    def start(self, items):
        has_main = "main" in self.function_bodies

        # Bootstrap:
        # - Programs: CALL main; HALT
        # - Libraries/modules: HALT only (still packages function bodies)
        bootstrap_len = 6 if has_main else 1

        # Determine function addresses (first pass)
        symbol_table = {}
        current_addr = bootstrap_len
        func_order = list(self.function_bodies.keys())
        for name in func_order:
            symbol_table[name] = current_addr
            current_addr += self._calculate_cleaned_length(self.function_bodies[name])

        # Build final code with patched calls (second pass)
        code = bytearray()
        if has_main:
            code.append(0x90)
            code.extend(struct.pack("<I", symbol_table["main"]))
            code.append(0x01)
        else:
            code.append(0x01)

        for name in func_order:
            cleaned = self._clean_and_patch(self.function_bodies[name], symbol_table)
            code.extend(cleaned)

        return self._package_binary(code)

    def statements(self, items):
        res = bytearray()
        for item in items:
            if isinstance(item, bytearray):
                res.extend(item)
        return res

    def statement(self, items): return items[0]

    def import_stmt(self, items):
        # Static linking is done before parsing.
        return bytearray()

    def wait_kairos_stmt(self, items):
        # Backward-compat: compile same as kairos (currently a stub in LBC)
        return self.kairos_stmt(items)

    def council_target(self, items):
        # Keep target name available for other backends; LBC ignores locking.
        return str(items[0])

    def council_stmt(self, items):
        # LBC doesn't implement locking, so we emit just the body.
        return items[-1]

    # --- Iconography of Data (no-op type info for bytecode) ---
    def struct_def(self, items):
        return bytearray()

    def field_decl(self, items):
        return bytearray()

    def params(self, items):
        return [str(i) for i in items]

    def param(self, items):
        # param: NAME (":" NAME)?
        return str(items[0])

    def _capture_function(self, items):
        name = str(items[0])
        body = items[-1]
        params = []
        for it in items[1:-1]:
            if isinstance(it, list):
                params = it

        # Prologue: bind params from stack -> synod (reverse order)
        prologue = bytearray()
        for p in reversed(params):
            const_idx = self._add_const(str(p))
            prologue.append(0x20)  # PETITION <u32_idx>
            prologue.extend(struct.pack("<I", const_idx))

        fn_body = bytearray()
        fn_body.extend(prologue)
        fn_body.extend(body)
        fn_body.append(0x91)  # RET (Dismissal)

        self.function_bodies[name] = fn_body
        return bytearray()  # Do not emit into main stream

    def service_def(self, items):
        return self._capture_function(items)

    def ministry_def(self, items):
        return self._capture_function(items)

    def intercessor_def(self, items):
        return self._capture_function(items)

    def behold_stmt(self, items):
        res = bytearray()
        res.extend(items[0])
        res.append(0x40) 
        return res

    def offer_stmt(self, items):
        # offer expr;  -> evaluate expr (push value), then RET
        res = bytearray()
        res.extend(items[0])
        res.append(0x91)
        return res

    def absolve_stmt(self, items):
        # ABSOLVE <u32_name_idx>
        name = str(items[0])
        idx = self._add_const(name)
        res = bytearray()
        res.append(0xE0)
        res.extend(struct.pack("<I", idx))
        return res

    def essence_decl(self, items):
        name, typ, expr = str(items[0]), str(items[1]), items[2]
        if not isinstance(expr, (bytearray, bytes)):
            raise TypeError(f"Expected bytearray for expr, got {type(expr)}: {expr}")
        const_idx = self._add_const(name)
        res = bytearray()
        res.extend(expr)
        res.append(0x20) 
        res.extend(struct.pack("<I", const_idx))
        return res

    def gift_decl(self, items):
        # gift_decl: "gift" NAME (":" TYPE)? "=" expr ";"
        # Bytecode doesn't encode the type, so accept both forms.
        if len(items) == 2:
            name, expr = str(items[0]), items[1]
            const_idx = self._add_const(name)
            res = bytearray()
            res.extend(expr)
            res.append(0x20)
            res.extend(struct.pack("<I", const_idx))
            return res
        return self.essence_decl(items)

    def assign_stmt(self, items):
        # assign_stmt: assignable "=" expr ";"
        target = items[0]
        expr = items[1]

        res = bytearray()

        # Case A: Simple Variable (NAME)
        if isinstance(target, str):
            const_idx = self._add_const(target)
            res.extend(expr)
            res.append(0x20)  # PETITION
            res.extend(struct.pack("<I", const_idx))
            return res

        # Case B: Array index assignment: name[index]
        if isinstance(target, tuple) and target and target[0] == "INDEX_LVALUE":
            _, arr_name, idx_code = target
            arr_const_idx = self._add_const(arr_name)
            res.append(0x11)  # LOAD_ESS
            res.extend(struct.pack("<I", arr_const_idx))
            res.extend(idx_code)
            res.extend(expr)
            res.append(0xA2)  # INSCRIBE
            return res

        # Case C: Icon field assignment: name.field
        if isinstance(target, tuple) and target and target[0] == "MEMBER_LVALUE":
            _, obj_name, field_name = target
            obj_const_idx = self._add_const(obj_name)
            field_idx = self._add_const(field_name)
            res.append(0x11)  # LOAD_ESS
            res.extend(struct.pack("<I", obj_const_idx))
            res.extend(expr)
            res.append(0xB2)  # CONSECRATE
            res.extend(struct.pack("<I", field_idx))
            return res

        raise Exception(f"Ontological Error: Unsupported assignment target: {target}")

    def try_repent_stmt(self, items):
        # try { try_body } repent NAME { repent_body } amen
        # Bytecode:
        #   ENTER_TRY <i32_offset_to_catch>
        #   try_body
        #   EXIT_TRY
        #   JMP <i32_offset_to_end>
        # catch:
        #   PETITION <error_name_const>
        #   repent_body
        # end:
        try_body = items[0]
        error_name = str(items[1])
        repent_body = items[2]

        res = bytearray()

        enter_pos = len(res)
        res.append(0xD0)  # ENTER_TRY
        res.extend(b"\x00\x00\x00\x00")  # placeholder i32

        res.extend(try_body)

        res.append(0xD1)  # EXIT_TRY

        jmp_pos = len(res)
        res.append(0x80)  # JMP
        res.extend(b"\x00\x00\x00\x00")

        catch_pos = len(res)

        # Bind error message (string) to repent variable
        name_idx = self._add_const(error_name)
        res.append(0x20)  # PETITION
        res.extend(struct.pack("<I", name_idx))

        res.extend(repent_body)

        end_pos = len(res)

        # Patch ENTER_TRY offset (relative to PC after reading the offset)
        # VM computes catch_addr = (pc_after_operand) + offset
        enter_after = enter_pos + 5
        res[enter_pos+1:enter_pos+5] = struct.pack("<i", catch_pos - enter_after)

        # Patch JMP-to-end offset
        jmp_after = jmp_pos + 5
        res[jmp_pos+1:jmp_pos+5] = struct.pack("<i", end_pos - jmp_after)

        return res

    def cycle_stmt(self, items):
        # cycle expr ("limit" NUMBER)? "{" statements "}" "amen"
        expr = items[0]
        body = items[-1]
        
        res = bytearray()
        start_pos = 0 # Relative to this block
        
        # 1. Evaluate expr
        res.extend(expr)
        
        # 2. JZ to end
        jz_placeholder_pos = len(res)
        res.append(0x81)
        res.extend(b"\x00\x00\x00\x00")
        
        # 3. Body
        res.extend(body)
        
        # 4. JMP to start
        current_pos = len(res)
        jmp_offset = 0 - (current_pos + 5)
        res.append(0x80)
        res.extend(struct.pack("<i", jmp_offset))
        
        # 5. Backpatch JZ
        end_pos = len(res)
        jz_offset = end_pos - (jz_placeholder_pos + 5)
        res[jz_placeholder_pos+1:jz_placeholder_pos+5] = struct.pack("<i", jz_offset)
        
        return res

    def kairos_stmt(self, items):
        # For now, LBC doesn't support full Kairos, so we treat it as a simple if
        expr = items[0]
        body = items[1] if not isinstance(items[1], list) else items[1] # Simplified
        # This is complex to implement in LBC without labels. 
        # Let's just return the body for now to avoid breaking compilation.
        return body

    def fast_stmt(self, items):
        res = bytearray()
        res.extend(items[0])
        res.append(0x60)
        return res

    def bin_op(self, items):
        left, op, right = items[0], str(items[1]), items[2]
        res = bytearray()
        if not isinstance(left, (bytearray, bytes)):
            left = self.atom([left])
        if not isinstance(right, (bytearray, bytes)):
            right = self.atom([right])
        res.extend(left)
        res.extend(right)
        op_map = {
            "+": 0x70, "-": 0x71, "*": 0x72, "/": 0x73,
            "==": 0x74, "!=": 0x75, "<": 0x76, ">": 0x77, "<=": 0x78, ">=": 0x79
        }
        res.append(op_map.get(op, 0x00))
        return res

    # --- Literals (Creation) ---
    def array_literal(self, items):
        args_list = items[0] if items else []
        res = bytearray()
        count = 0
        if args_list:
            for a in args_list:
                res.extend(a)
                count += 1
        res.append(0xA0)  # GATHER
        res.extend(struct.pack("<I", count))
        return res

    def struct_literal(self, items):
        # struct_literal: "new" NAME "{" field_inits? "}"
        fields = items[1] if len(items) > 1 else []
        res = bytearray()
        count = 0
        for f_name, f_expr in fields:
            key_idx = self._add_const(f_name)
            res.append(0x10)  # PUSH_ESS
            res.extend(struct.pack("<I", key_idx))
            res.extend(f_expr)
            count += 1
        res.append(0xB0)  # MOLD
        res.extend(struct.pack("<I", count))
        return res

    def field_inits(self, items):
        return items

    def field_init(self, items):
        return (str(items[0]), items[1])

    # --- Access (read) ---
    def index_access(self, items):
        arr_expr, idx_expr = items[0], items[1]
        res = bytearray()
        res.extend(arr_expr)
        res.extend(idx_expr)
        res.append(0xA1)  # PARTAKE
        return res

    def dot_access(self, items):
        # dot_access: atom "." NAME call_suffix?
        obj_expr = items[0]
        name = str(items[1])

        # Method access (currently only Synod sugar: t.read(...), t.petition(...))
        if len(items) > 2:
            args_list = items[2] if items[2] is not None else []
            if name == "read":
                key_code = args_list[0]
                if len(key_code) == 5 and key_code[0] == 0x10:
                    res = bytearray([0x11])  # LOAD_ESS
                    res.extend(key_code[1:])
                    return res
                raise Exception("Ontological Error: Synod.read requires a literal Text key")

            if name == "petition":
                key_code = args_list[0]
                val_code = args_list[1]
                if len(key_code) == 5 and key_code[0] == 0x10:
                    res = bytearray()
                    res.extend(val_code)
                    res.append(0x20)  # PETITION
                    res.extend(key_code[1:])
                    return res
                raise Exception("Ontological Error: Synod.petition requires a literal Text key")

            raise Exception(f"Ontological Error: Unknown method '{name}'")

        # Field access (Icon)
        field_idx = self._add_const(name)
        res = bytearray()
        res.extend(obj_expr)
        res.append(0xB1)  # REVEAL
        res.extend(struct.pack("<I", field_idx))
        return res

    # --- Complex assignment targets ---
    def index_assignable(self, items):
        # NAME "[" expr "]"
        return ("INDEX_LVALUE", str(items[0]), items[1])

    def member_assignable(self, items):
        # NAME "." NAME
        return ("MEMBER_LVALUE", str(items[0]), str(items[1]))

    def assignable(self, items):
        # pass-through
        return items[0]

    def method_target(self, items):
        # NAME "." NAME (used only for method calls like t.read())
        return ("MEMBER", items[0], str(items[1]))

    def expr(self, items): return items[0]
    def expr_stmt(self, items): return items[0]

    def atom(self, items):
        if len(items) == 3 and str(items[0]) == "(":
            return items[1]
        
        val = items[0]
        res = bytearray()
        if isinstance(val, Token):
            if val.type == 'NUMBER':
                val_str = str(val)
                if "." in val_str:
                    const_idx = self._add_const(float(val_str))
                else:
                    const_idx = self._add_const(int(val_str))
                res.append(0x10)
                res.extend(struct.pack("<I", const_idx))
            elif val.type == 'STRING':
                const_idx = self._add_const(val[1:-1])
                res.append(0x10)
                res.extend(struct.pack("<I", const_idx))
            elif val.type == 'NAME':
                const_idx = self._add_const(str(val))
                res.append(0x11)
                res.extend(struct.pack("<I", const_idx))
        elif isinstance(val, str):
            if val.isdigit():
                const_idx = self._add_const(int(val))
                res.append(0x10)
                res.extend(struct.pack("<I", const_idx))
            else:
                const_idx = self._add_const(val)
                res.append(0x11)
                res.extend(struct.pack("<I", const_idx))
        elif isinstance(val, bytearray):
            return val
        return res

    def witness_expr(self, items):
        # items: [expr, type]
        expr = items[0]
        typ = str(items[1])
        res = bytearray()
        res.extend(expr)
        res.append(0x50)
        if typ == "HolyInt": res.append(0x01)
        elif typ == "Text": res.append(0x02)
        elif typ == "HolyFloat": res.append(0x03)
        else: res.append(0x00) # Unknown
        return res

    # --- Minor Orders (Literals) ---
    def bool_literal(self, items):
        val = str(items[0]) == "Verily"
        const_idx = self._add_const(val)
        res = bytearray([0x10])
        res.extend(struct.pack("<I", const_idx))
        return res

    def char_literal(self, items):
        tok = str(items[0])
        # token like 'A'
        inner = tok[1:-1]
        if len(inner) != 1:
            raise Exception("Ontological Error: Char literal must be exactly one character")
        const_idx = self._add_const(CharConst(ord(inner)))
        res = bytearray([0x10])
        res.extend(struct.pack("<I", const_idx))
        return res

    def byte_literal(self, items):
        tok = str(items[0])
        val = int(tok, 16)
        const_idx = self._add_const(ByteConst(val))
        res = bytearray([0x10])
        res.extend(struct.pack("<I", const_idx))
        return res

    def listen_expr(self, items):
        # listen expr -> push prompt, LISTEN
        res = bytearray()
        res.extend(items[0])
        res.append(0x30)
        return res

    def call_suffix(self, items):
        # call_suffix: "(" args? ")"
        # items is [] or [args_list]
        return items[0] if items else []

    def call_expr(self, items):
        # call_expr: NAME call_suffix
        name = str(items[0])
        args_list = items[1] if len(items) > 1 else []

        # Intrinsics: The Communion of Text
        if name == "measure":
            res = bytearray()
            for a in args_list:
                res.extend(a)
            res.append(0xC0)  # MEASURE
            return res

        if name == "passage":
            res = bytearray()
            for a in args_list:
                res.extend(a)
            res.append(0xC1)  # PASSAGE
            return res

        if name == "create_synod":
            const_idx = self._add_const(0)
            res = bytearray([0x10])
            res.extend(struct.pack("<I", const_idx))
            return res

        # Standard call: args..., CALL <patched addr>
        res = bytearray()
        for a in args_list:
            res.extend(a)

        res.append(0x90)  # CALL
        res.extend(struct.pack("<I", 0xFFFFFFFF))
        res.extend(name.encode('utf-8') + b"\x00")
        return res

    def args(self, items):
        return items

    def arg(self, items):
        return items[-1]

    def member_access(self, items):
        return ("MEMBER", items[0], str(items[1]))

    def await_expr(self, items):
        if isinstance(items[0], bytearray):
            return items[0]
        return bytearray()

    def gather_expr(self, items):
        # No-op for now
        return bytearray()

    def await_stmt(self, items):
        if isinstance(items[0], bytearray):
            return items[0]
        return bytearray()

    def call_stmt(self, items):
        if isinstance(items[0], bytearray):
            return items[0]
        return bytearray()

    def gather_stmt(self, items):
        # No-op for now
        return bytearray()

    def NAME(self, t): return t
    def NUMBER(self, t): return t
    def STRING(self, t): return t

def indent_body(body):
    if not body: return indent("pass")
    return "\n".join([indent(str(stmt)) for stmt in body if stmt])

def compile_and_run(filename, target="python"):
    base_dir = os.path.dirname(__file__)
    lark_path = os.path.join(base_dir, "logos.lark")
    parser = Lark(open(lark_path).read(), parser='lalr', propagate_positions=True)

    def _load_canon(entry_file: str) -> str:
        visited = set()
        chunks = []

        def load_one(path: str):
            norm = os.path.normpath(os.path.abspath(path))
            if norm in visited:
                return
            visited.add(norm)

            text = open(norm, encoding="utf-8").read()
            dir_name = os.path.dirname(norm)

            # Find imports and load them first.
            imports = []
            for m in re.finditer(r'^\s*import\s+"([^"]+)"\s*;\s*$', text, flags=re.MULTILINE):
                imports.append(m.group(1))

            for imp in imports:
                imp_path = imp
                if not os.path.isabs(imp_path):
                    imp_path = os.path.join(dir_name, imp_path)
                load_one(imp_path)

            # Strip import lines from this file (they are link directives, not runtime statements).
            stripped = re.sub(r'^\s*import\s+"[^"]+"\s*;\s*\n?', '', text, flags=re.MULTILINE)
            chunks.append(stripped)

        load_one(entry_file)
        return "\n\n".join(chunks)

    canon_text = _load_canon(filename)
    tree = parser.parse(canon_text)
    
    SynodValidator().visit(tree)
    print("[+] Commencing Diakrisis (Formal Verification)...")
    DiakrisisEngine().visit(tree)
    print("[+] Diakrisis complete. Program is Sanctified.")
    
    if target == "python":
        py_code = LogosToPython().transform(tree)
        print("--- GENERATED PYTHON ---")
        print(py_code)
        print("--- END GENERATED PYTHON ---")
        exec(py_code + "\nimport asyncio\nasyncio.run(main())", {"__name__": "__main__"})
    elif target == "lbc":
        transformer = LogosToBytecode()
        lbc = transformer.transform(tree)
        out_name = filename.replace(".lg", ".lbc")
        with open(out_name, "wb") as f:
            f.write(lbc)
        print(f"[+] Sanctification complete: {out_name}")

if __name__ == "__main__":
    target = sys.argv[2] if len(sys.argv) > 2 else "python"
    compile_and_run(sys.argv[1], target)
