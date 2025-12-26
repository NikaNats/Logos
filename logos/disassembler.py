import struct
import sys

def disassemble(filename):
    with open(filename, "rb") as f:
        header = f.read(5)
        version = f.read(1)
        seal = f.read(32)
        print(f"Header: {header.decode()}, Version: {version[0]}")
        print(f"Seal of Purity: {seal.hex()}")
        
        cp_count = struct.unpack("<I", f.read(4))[0]
        print(f"Constant Pool ({cp_count} items):")
        constants = []
        for i in range(cp_count):
            tag = f.read(1)[0]
            if tag == 0x01:
                val = struct.unpack("<q", f.read(8))[0]
                print(f"  {i}: INT {val}")
                constants.append(val)
            elif tag == 0x02:
                length = struct.unpack("<I", f.read(4))[0]
                val = f.read(length).decode('utf-8')
                print(f"  {i}: STR '{val}'")
                constants.append(val)
            elif tag == 0x03:
                val = struct.unpack("<d", f.read(8))[0]
                print(f"  {i}: FLOAT {val}")
                constants.append(val)
            elif tag == 0x04:
                b = f.read(1)[0]
                val = (b != 0)
                print(f"  {i}: BOOL {'Verily' if val else 'Nay'}")
                constants.append(val)
            elif tag == 0x05:
                cp = struct.unpack("<I", f.read(4))[0]
                try:
                    ch = chr(cp)
                except ValueError:
                    ch = "\uFFFD"
                print(f"  {i}: CHAR '{ch}'")
                constants.append(f"'{ch}'")
            elif tag == 0x06:
                b = f.read(1)[0]
                print(f"  {i}: BYTE 0x{b:02X}")
                constants.append(f"0x{b:02X}")
        
        code_len = struct.unpack("<I", f.read(4))[0]
        print(f"Code ({code_len} bytes):")
        code = f.read(code_len)
        
        pc = 0
        while pc < len(code):
            op = code[pc]
            pc += 1
            if op == 0x01: print(f"  {pc-1:04x}: HALT_AMEN")
            elif op == 0xFE:
                lib_len = struct.unpack("<I", code[pc:pc+4])[0]
                pc += 4
                lib = code[pc:pc+lib_len].decode("utf-8", errors="replace")
                pc += lib_len

                fn_len = struct.unpack("<I", code[pc:pc+4])[0]
                pc += 4
                fn = code[pc:pc+fn_len].decode("utf-8", errors="replace")
                pc += fn_len

                ret_tag = code[pc]
                pc += 1
                argc = code[pc]
                pc += 1
                arg_tags = list(code[pc:pc+argc])
                pc += argc

                type_name = {0: "Void", 1: "HolyInt", 2: "HolyFloat"}
                ret_name = type_name.get(ret_tag, f"Unknown({ret_tag})")
                args_name = ",".join(type_name.get(t, f"?{t}") for t in arg_tags)
                print(f"  {pc-(1+4+lib_len+4+fn_len+1+1+argc):04x}: INVOKE_FOREIGN {lib}::{fn} ({args_name}) -> {ret_name}")
            elif op == 0x12:
                off = struct.unpack("<I", code[pc:pc+4])[0]
                pc += 4
                print(f"  {pc-5:04x}: GET_LOCAL {off}")
            elif op == 0x30:
                print(f"  {pc-1:04x}: LISTEN")
            elif op == 0x90:
                addr = struct.unpack("<I", code[pc:pc+4])[0]
                pc += 4
                print(f"  {pc-5:04x}: CALL 0x{addr:08x}")
            elif op == 0x91:
                print(f"  {pc-1:04x}: RET")
            elif op == 0xD0:
                off = struct.unpack("<i", code[pc:pc+4])[0]
                pc += 4
                print(f"  {pc-5:04x}: ENTER_TRY {off} (to {pc + off:04x})")
            elif op == 0xD1:
                print(f"  {pc-1:04x}: EXIT_TRY")
            elif op == 0xD2:
                print(f"  {pc-1:04x}: THROW")
            elif op == 0xD3:
                print(f"  {pc-1:04x}: IS_INSTANCE")
            elif op == 0xE0:
                idx = struct.unpack("<I", code[pc:pc+4])[0]
                pc += 4
                print(f"  {pc-5:04x}: ABSOLVE {idx} ({constants[idx]})")
            elif op == 0x10:
                idx = struct.unpack("<I", code[pc:pc+4])[0]
                pc += 4
                print(f"  {pc-5:04x}: PUSH_ESS {idx} ({constants[idx]})")
            elif op == 0x11:
                idx = struct.unpack("<I", code[pc:pc+4])[0]
                pc += 4
                print(f"  {pc-5:04x}: LOAD_ESS {idx} ({constants[idx]})")
            elif op == 0x20:
                idx = struct.unpack("<I", code[pc:pc+4])[0]
                pc += 4
                print(f"  {pc-5:04x}: PETITION {idx} ({constants[idx]})")
            elif op == 0xA0:
                count = struct.unpack("<I", code[pc:pc+4])[0]
                pc += 4
                print(f"  {pc-5:04x}: GATHER {count}")
            elif op == 0xA1:
                print(f"  {pc-1:04x}: PARTAKE")
            elif op == 0xA2:
                print(f"  {pc-1:04x}: INSCRIBE")
            elif op == 0xA3:
                print(f"  {pc-1:04x}: ALLOC")
            elif op == 0xB0:
                count = struct.unpack("<I", code[pc:pc+4])[0]
                pc += 4
                print(f"  {pc-5:04x}: MOLD {count}")
            elif op == 0xB1:
                idx = struct.unpack("<I", code[pc:pc+4])[0]
                pc += 4
                print(f"  {pc-5:04x}: REVEAL {idx} ({constants[idx]})")
            elif op == 0xB2:
                idx = struct.unpack("<I", code[pc:pc+4])[0]
                pc += 4
                print(f"  {pc-5:04x}: CONSECRATE {idx} ({constants[idx]})")
            elif op == 0xC0:
                print(f"  {pc-1:04x}: MEASURE")
            elif op == 0xC1:
                print(f"  {pc-1:04x}: PASSAGE")
            elif op == 0x40: print(f"  {pc-1:04x}: BEHOLD")
            elif op == 0x50:
                tag = code[pc]
                pc += 1
                t_name = {1: "HolyInt", 2: "Text", 3: "HolyFloat"}.get(tag, "Unknown")
                print(f"  {pc-2:04x}: WITNESS {t_name}")
            elif op == 0x60: print(f"  {pc-1:04x}: FAST")
            elif op == 0x70: print(f"  {pc-1:04x}: ADD")
            elif op == 0x71: print(f"  {pc-1:04x}: SUB")
            elif op == 0x72: print(f"  {pc-1:04x}: MUL")
            elif op == 0x73: print(f"  {pc-1:04x}: DIV")
            elif op == 0x74: print(f"  {pc-1:04x}: EQ")
            elif op == 0x75: print(f"  {pc-1:04x}: NE")
            elif op == 0x76: print(f"  {pc-1:04x}: LT")
            elif op == 0x77: print(f"  {pc-1:04x}: GT")
            elif op == 0x78: print(f"  {pc-1:04x}: LE")
            elif op == 0x79: print(f"  {pc-1:04x}: GE")
            elif op == 0x80:
                offset = struct.unpack("<i", code[pc:pc+4])[0]
                pc += 4
                print(f"  {pc-5:04x}: JMP {offset} (to {pc + offset:04x})")
            elif op == 0x81:
                offset = struct.unpack("<i", code[pc:pc+4])[0]
                pc += 4
                print(f"  {pc-5:04x}: JZ {offset} (to {pc + offset:04x})")
            elif op == 0x82:
                count = struct.unpack("<I", code[pc:pc+4])[0]
                pc += 4
                cases = []
                for _ in range(count):
                    case_val = struct.unpack("<q", code[pc:pc+8])[0]
                    pc += 8
                    offset = struct.unpack("<i", code[pc:pc+4])[0]
                    pc += 4
                    cases.append((case_val, offset))
                default_offset = struct.unpack("<i", code[pc:pc+4])[0]
                pc += 4

                table = ", ".join([f"{v}:{o}" for (v, o) in cases])
                print(f"  {pc-(1+4+count*12+4):04x}: DISCERN {count} [{table}] default:{default_offset}")
            elif op == 0xF0:
                print(f"  {pc-1:04x}: SYS_OPEN")
            elif op == 0xF1:
                print(f"  {pc-1:04x}: SYS_WRITE")
            elif op == 0xF2:
                print(f"  {pc-1:04x}: SYS_READ")
            elif op == 0xF3:
                print(f"  {pc-1:04x}: SYS_CLOSE")
            elif op == 0xF4:
                print(f"  {pc-1:04x}: SYS_TIME")
            elif op == 0xF5:
                print(f"  {pc-1:04x}: SYS_ENV")
            else: print(f"  {pc-1:04x}: UNKNOWN 0x{op:02x}")

if __name__ == "__main__":
    disassemble(sys.argv[1])
