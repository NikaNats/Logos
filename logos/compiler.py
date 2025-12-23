import sys, os, struct, hashlib
import z3
from lark import Lark, Transformer, Token, Tree
from lark.visitors import Interpreter

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
        if not self.in_service: raise Exception("Pride Error: Global essence forbidden.")
        name = str(tree.children[0])
        self._register(name, tree.children[0].line, True)
        self.visit_children(tree)

    def behold_stmt(self, tree):
        if not self.in_ministry:
            raise Exception(f"Sanctity Error: 'behold' forbidden in pure service at line {tree.meta.line}.")

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
        self.custom_types = {}

    def type_def(self, tree):
        # type_def: "type" NAME "=" "essence" "{" constraint+ "}" "amen"
        # Children: [NAME, constraint, constraint, ...]
        name = str(tree.children[0])
        constraints = []
        for c in tree.children:
            if isinstance(c, Tree) and c.data == 'constraint':
                # constraint: "not" OPERATOR expr ";"
                # Children: [OPERATOR, expr]
                op = str(c.children[0])
                expr = c.children[1]
                constraints.append((op, expr))
        self.custom_types[name] = constraints

    def essence_decl(self, tree):
        # essence_decl: "essence" NAME ":" TYPE "=" expr ";"
        # Children: [NAME, TYPE, expr]
        name = str(tree.children[0])
        typ = str(tree.children[1])
        expr = tree.children[2]
        self._verify_assignment(name, typ, expr, tree.meta.line)

    def gift_decl(self, tree):
        # gift_decl: "gift" NAME ":" TYPE "=" expr ";"
        # Children: [NAME, TYPE, expr]
        name = str(tree.children[0])
        typ = str(tree.children[1])
        expr = tree.children[2]
        self._verify_assignment(name, typ, expr, tree.meta.line)

    def assign_stmt(self, tree):
        name = str(tree.children[0])
        expr = tree.children[1]
        if name in self.symbols:
            # For simplicity, we assume the type remains the same as when it was declared
            # In a real compiler, we'd track the type of each symbol
            val = self.symbols[name]
            z3_expr = self._to_z3(expr)
            self.solver.add(val == z3_expr)

    def _verify_assignment(self, name, typ, expr, line):
        if typ == "HolyInt" or typ in self.custom_types:
            if name not in self.symbols:
                self.symbols[name] = z3.Real(name)
            
            val = self.symbols[name]
            z3_expr = self._to_z3(expr)
            
            constraints = self._get_constraints(typ)
            for op, c_expr in constraints:
                limit = self._to_z3(c_expr)
                self.solver.push()
                self.solver.add(val == z3_expr)
                
                if op == "<": cond = val < limit
                elif op == ">": cond = val > limit
                elif op == "==": cond = val == limit
                elif op == "!=": cond = val != limit
                elif op == ">=": cond = val >= limit
                elif op == "<=": cond = val <= limit
                else: cond = None
                
                if cond is not None:
                    self.solver.add(cond)
                    if self.solver.check() == z3.sat:
                        model = self.solver.model()
                        self.solver.pop()
                        raise Exception(f"Diakrisis Error: Essence '{name}' violates nature '{typ}' at line {line}. "
                                        f"Counter-example: {model}")
                self.solver.pop()
                
                if op == "<": self.solver.add(val >= limit)
                elif op == ">": self.solver.add(val <= limit)
                elif op == "==": self.solver.add(val != limit)
                elif op == "!=": self.solver.add(val == limit)
                elif op == ">=": self.solver.add(val < limit)
                elif op == "<=": self.solver.add(val > limit)
            
            # Add the assignment permanently to the solver's knowledge base
            self.solver.add(val == z3_expr)

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

    def service_def(self, items):
        name, params, body = items[0], items[1] or "", items[3]
        prefix = "async " # In Logos v1.0, all services are inherently ready for intercession
        return f"{prefix}def {name}({params}):\n{indent_body(body)}"

    def ministry_def(self, items): return self.service_def(items)
    def intercessor_def(self, items): return self.service_def(items)

    def params(self, items): return ", ".join(map(str, items))
    def param(self, items): return str(items[0])

    def args(self, items): return ", ".join(map(str, items))
    def arg(self, items):
        if len(items) == 2: return f"{items[0]}={items[1]}"
        return str(items[0])

    def essence_decl(self, items):
        name, typ, expr = str(items[0]), str(items[1]), items[2]
        checks = CANON_TYPES.get(typ, [])
        assertions = "\n".join([f"assert {c.format(name=name)}, 'Nature Violation'" for c in checks])
        return f"{name} = sanctify({expr})\n{assertions}"

    def gift_decl(self, items):
        name, typ, expr = str(items[0]), str(items[1]), items[2]
        return f"{name} = {expr}"

    def assign_stmt(self, items):
        return f"{items[0]} = {items[1]}"

    def cycle_stmt(self, items):
        cond, limit, body = items[0], items[1] if len(items)==3 else None, items[-1]
        loop = f"while {cond}:\n{indent_body(body)}"
        return f"__lim__={limit}\n{loop}" if limit else loop

    def kairos_stmt(self, items):
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
            
        res = f"if await t.wait_for_kairos(lambda: {expr}, {timeout}):\n{indent_body(body)}"
        if repent_body:
            res += f"\nelse:\n{indent_body(repent_body)}"
        return res

    def try_repent_stmt(self, items):
        try_body, error_name, repent_body = items[0], items[1], items[2]
        return f"try:\n{indent_body(try_body)}\nexcept Exception as {error_name}:\n{indent_body(repent_body)}"

    def call_stmt(self, items): return items[0]
    def await_stmt(self, items): return f"await {items[0]}"
    def gather_stmt(self, items): return f"await asyncio.gather({', '.join(map(str, items))})"
    def fast_stmt(self, items): return f"await asyncio.sleep({items[0]})"
    def council_stmt(self, items): return f"async with {items[0]}._lock:\n{indent_body(items[-1])}"
    def behold_stmt(self, items): return f"print({items[0]})"
    def offer_stmt(self, items): return f"return {items[0]}"
    def bin_op(self, items): return f"({items[0]} {items[1]} {items[2]})"
    def member_access(self, items): return f"{items[0]}.{items[1]}"
    def call_expr(self, items): return f"{items[0]}({items[1] or ''})"
    def witness_expr(self, items): return f"({items[0]})"
    def type_def(self, items): return ""
    def constraint(self, items): return ""
    def NAME(self, t): return str(t)
    def NUMBER(self, t): return str(t)
    def STRING(self, t): return str(t)

class LogosToBytecode(Transformer):
    def __init__(self):
        self.constants = []

    def _add_const(self, val):
        if val in self.constants:
            return self.constants.index(val)
        self.constants.append(val)
        return len(self.constants) - 1

    def start(self, items):
        code = items[0]
        code.append(0x01) # HALT_AMEN
        
        # Header: 'LOGOS' + Version 1 + Seal of Purity (32 bytes)
        header = b"LOGOS\x01"
        
        # Calculate Seal of Purity (Hash of the bytecode for now)
        seal = hashlib.sha256(code).digest()
        
        cp = bytearray()
        cp.extend(struct.pack("<I", len(self.constants)))
        for c in self.constants:
            if isinstance(c, int):
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

    def statements(self, items):
        res = bytearray()
        for item in items:
            if isinstance(item, bytearray):
                res.extend(item)
        return res

    def service_def(self, items): return items[3]
    def ministry_def(self, items): return items[3]
    def intercessor_def(self, items): return items[3]

    def behold_stmt(self, items):
        res = bytearray()
        res.extend(items[0])
        res.append(0x40) 
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
        return self.essence_decl(items)

    def assign_stmt(self, items):
        name, expr = str(items[0]), items[1]
        const_idx = self._add_const(name)
        res = bytearray()
        res.extend(expr)
        res.append(0x20) 
        res.extend(struct.pack("<I", const_idx))
        return res

    def try_repent_stmt(self, items):
        res = bytearray()
        # items[0] is the try block statements (already a bytearray from statements rule)
        res.extend(items[0])
        return res

    def cycle_stmt(self, items):
        # cycle (expr) { statements } amen
        # items: [expr, body] or [expr, limit, body]
        expr = items[0]
        body = items[-1]
        
        res = bytearray()
        start_label = 0 # Relative to this block
        
        # 1. Evaluate expr
        res.extend(expr)
        
        # 2. JZ to end
        # We don't know the body length yet, so we'll backpatch or calculate
        # JZ <offset> is 5 bytes (1 opcode + 4 offset)
        # Offset is from the end of the JZ instruction
        jz_placeholder_pos = len(res)
        res.append(0x81)
        res.extend(b"\x00\x00\x00\x00")
        
        # 3. Body
        res.extend(body)
        
        # 4. JMP to start
        # JMP <offset> is 5 bytes
        # Offset = start_label - (current_pos + 5)
        current_pos = len(res)
        jmp_offset = 0 - (current_pos + 5)
        res.append(0x80)
        res.extend(struct.pack("<i", jmp_offset))
        
        # 5. Backpatch JZ
        # Offset = current_pos_after_jmp - (jz_placeholder_pos + 5)
        end_pos = len(res)
        jz_offset = end_pos - (jz_placeholder_pos + 5)
        res[jz_placeholder_pos+1:jz_placeholder_pos+5] = struct.pack("<i", jz_offset)
        
        return res

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

    def call_expr(self, items):
        target = items[0]
        args_list = items[1] if len(items) > 1 else []
        
        # If target is a member_access like t.read
        if isinstance(target, tuple) and target[0] == "MEMBER":
            obj, method = target[1], target[2]
            if method == "read":
                # args_list[0] is the code for the key (e.g., PUSH_ESS <idx>)
                key_code = args_list[0]
                if len(key_code) == 5 and key_code[0] == 0x10:
                    res = bytearray([0x11])
                    res.extend(key_code[1:])
                    return res
            elif method == "petition":
                # args_list is [key_code, val_code]
                # We want: val_code, then PETITION <key_idx>
                key_code = args_list[0]
                val_code = args_list[1]
                if len(key_code) == 5 and key_code[0] == 0x10:
                    res = bytearray()
                    res.extend(val_code)
                    res.append(0x20)
                    res.extend(key_code[1:])
                    return res
        
        name = str(target)
        if name == "create_synod":
            const_idx = self._add_const(0)
            res = bytearray([0x10])
            res.extend(struct.pack("<I", const_idx))
            return res
        
        res = bytearray()
        for a in args_list:
            res.extend(a)
        return res

    def args(self, items):
        return items

    def arg(self, items):
        return items[-1]

    def member_access(self, items):
        return ("MEMBER", items[0], str(items[1]))

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

    def kairos_stmt(self, items):
        # No-op for now
        return bytearray()

    def expr(self, items):
        return items[0]

    def bin_op(self, items):
        left, op, right = items[0], str(items[1]), items[2]
        res = bytearray()
        res.extend(left)
        res.extend(right)
        if op == "+": res.append(0x70)
        elif op == "-": res.append(0x71)
        elif op == "*": res.append(0x72)
        elif op == "/": res.append(0x73)
        elif op == "==": res.append(0x74)
        elif op == "!=": res.append(0x75)
        elif op == "<": res.append(0x76)
        elif op == ">": res.append(0x77)
        elif op == "<=": res.append(0x78)
        elif op == ">=": res.append(0x79)
        return res

    def fast_stmt(self, items):
        res = bytearray()
        res.extend(items[0])
        res.append(0x60)
        return res

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
    tree = parser.parse(open(filename).read())
    
    SynodValidator().visit(tree)
    print("[+] Commencing Diakrisis (Formal Verification)...")
    DiakrisisEngine().visit(tree)
    print("[+] Diakrisis complete. Program is Sanctified.")
    
    if target == "python":
        py_code = LogosToPython().transform(tree)
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
