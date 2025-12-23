import struct
import sys

def disassemble(filename):
    with open(filename, "rb") as f:
        header = f.read(5)
        version = f.read(1)
        print(f"Header: {header.decode()}, Version: {version[0]}")
        
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
        
        code_len = struct.unpack("<I", f.read(4))[0]
        print(f"Code ({code_len} bytes):")
        code = f.read(code_len)
        
        pc = 0
        while pc < len(code):
            op = code[pc]
            pc += 1
            if op == 0x01: print(f"  {pc-1:04x}: HALT_AMEN")
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
            elif op == 0x40: print(f"  {pc-1:04x}: BEHOLD")
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
            else: print(f"  {pc-1:04x}: UNKNOWN 0x{op:02x}")

if __name__ == "__main__":
    disassemble(sys.argv[1])
