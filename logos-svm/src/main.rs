use std::collections::HashMap;
use std::env;
use std::fs::File;
use std::io::{Read, Cursor};
use byteorder::{LittleEndian, ReadBytesExt};
use std::thread;
use std::time::Duration;

#[derive(Debug, Clone)]
enum Value {
    Int(i64),
    String(String),
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Int(i) => write!(f, "{}", i),
            Value::String(s) => write!(f, "{}", s),
        }
    }
}

struct SVM {
    stack: Vec<Value>,
    synod: HashMap<String, Value>,
    constants: Vec<Value>,
    pc: usize,
}

impl SVM {
    fn new(constants: Vec<Value>) -> Self {
        SVM {
            stack: Vec::new(),
            synod: HashMap::new(),
            constants,
            pc: 0,
        }
    }

    fn execute(&mut self, code: Vec<u8>) {
        let mut cursor = Cursor::new(code);
        while self.pc < cursor.get_ref().len() {
            cursor.set_position(self.pc as u64);
            let opcode = cursor.read_u8().unwrap();
            self.pc += 1;

            match opcode {
                0x01 => { // HALT_AMEN
                    println!("[+] Execution complete. Amen.");
                    return;
                }
                0x10 => { // PUSH_ESS <u32_idx>
                    let idx = cursor.read_u32::<LittleEndian>().unwrap();
                    self.pc += 4;
                    self.stack.push(self.constants[idx as usize].clone());
                }
                0x11 => { // LOAD_ESS <u32_idx>
                    let idx = cursor.read_u32::<LittleEndian>().unwrap();
                    self.pc += 4;
                    let name = match &self.constants[idx as usize] {
                        Value::String(s) => s,
                        _ => panic!("Ontological Error: Symbol name must be a string"),
                    };
                    let val = self.synod.get(name).expect("Ontological Error: Unknown spirit").clone();
                    self.stack.push(val);
                }
                0x20 => { // PETITION <u32_idx>
                    let idx = cursor.read_u32::<LittleEndian>().unwrap();
                    self.pc += 4;
                    let name = match &self.constants[idx as usize] {
                        Value::String(s) => s,
                        _ => panic!("Ontological Error: Symbol name must be a string"),
                    };
                    let val = self.stack.pop().expect("Stack Underflow");
                    self.synod.insert(name.clone(), val);
                }
                0x40 => { // BEHOLD
                    let val = self.stack.pop().expect("Stack Underflow");
                    println!("{}", val);
                }
                0x60 => { // FAST
                    let val = self.stack.pop().expect("Stack Underflow");
                    if let Value::Int(ms) = val {
                        thread::sleep(Duration::from_millis(ms as u64));
                    }
                }
                0x70 => { // ADD
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    match (a, b) {
                        (Value::Int(va), Value::Int(vb)) => self.stack.push(Value::Int(va + vb)),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x71 => { // SUB
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    match (a, b) {
                        (Value::Int(va), Value::Int(vb)) => self.stack.push(Value::Int(va - vb)),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x72 => { // MUL
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    match (a, b) {
                        (Value::Int(va), Value::Int(vb)) => self.stack.push(Value::Int(va * vb)),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x73 => { // DIV
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    match (a, b) {
                        (Value::Int(va), Value::Int(vb)) => self.stack.push(Value::Int(va / vb)),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x74 => { // EQ
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    match (a, b) {
                        (Value::Int(va), Value::Int(vb)) => self.stack.push(Value::Int(if va == vb { 1 } else { 0 })),
                        (Value::String(va), Value::String(vb)) => self.stack.push(Value::Int(if va == vb { 1 } else { 0 })),
                        _ => self.stack.push(Value::Int(0)),
                    }
                }
                0x75 => { // NE
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    match (a, b) {
                        (Value::Int(va), Value::Int(vb)) => self.stack.push(Value::Int(if va != vb { 1 } else { 0 })),
                        (Value::String(va), Value::String(vb)) => self.stack.push(Value::Int(if va != vb { 1 } else { 0 })),
                        _ => self.stack.push(Value::Int(1)),
                    }
                }
                0x76 => { // LT
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    match (a, b) {
                        (Value::Int(va), Value::Int(vb)) => self.stack.push(Value::Int(if va < vb { 1 } else { 0 })),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x77 => { // GT
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    match (a, b) {
                        (Value::Int(va), Value::Int(vb)) => self.stack.push(Value::Int(if va > vb { 1 } else { 0 })),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x78 => { // LE
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    match (a, b) {
                        (Value::Int(va), Value::Int(vb)) => self.stack.push(Value::Int(if va <= vb { 1 } else { 0 })),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x79 => { // GE
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    match (a, b) {
                        (Value::Int(va), Value::Int(vb)) => self.stack.push(Value::Int(if va >= vb { 1 } else { 0 })),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x80 => { // JMP <i32_offset>
                    let offset = cursor.read_i32::<LittleEndian>().unwrap();
                    self.pc = (self.pc as i64 + offset as i64) as usize;
                    continue;
                }
                0x81 => { // JZ <i32_offset>
                    let offset = cursor.read_i32::<LittleEndian>().unwrap();
                    let val = self.stack.pop().expect("Stack Underflow");
                    if let Value::Int(0) = val {
                        self.pc = (self.pc as i64 + offset as i64) as usize;
                        continue;
                    } else {
                        self.pc += 4;
                    }
                }
                _ => panic!("Ontological Error: Unknown Spirit 0x{:02X}", opcode),
            }
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("Usage: logos-svm <file.lbc>");
        return;
    }

    let mut file = File::open(&args[1]).expect("Could not open file");
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer).expect("Could not read file");

    let mut cursor = Cursor::new(buffer);
    
    // Header check
    let mut magic = [0u8; 5];
    cursor.read_exact(&mut magic).unwrap();
    if &magic != b"LOGOS" {
        panic!("Ontological Error: Not a LOGOS file");
    }
    let version = cursor.read_u8().unwrap();
    if version != 1 {
        panic!("Ontological Error: Unsupported version");
    }

    // Constant Pool
    let cp_count = cursor.read_u32::<LittleEndian>().unwrap();
    let mut constants = Vec::new();
    for _ in 0..cp_count {
        let tag = cursor.read_u8().unwrap();
        match tag {
            0x01 => {
                let val = cursor.read_i64::<LittleEndian>().unwrap();
                constants.push(Value::Int(val));
            }
            0x02 => {
                let len = cursor.read_u32::<LittleEndian>().unwrap();
                let mut s_buf = vec![0u8; len as usize];
                cursor.read_exact(&mut s_buf).unwrap();
                constants.push(Value::String(String::from_utf8(s_buf).unwrap()));
            }
            _ => panic!("Ontological Error: Invalid constant tag"),
        }
    }

    // Code Section
    let code_len = cursor.read_u32::<LittleEndian>().unwrap();
    let mut code = vec![0u8; code_len as usize];
    cursor.read_exact(&mut code).unwrap();

    let mut svm = SVM::new(constants);
    svm.execute(code);
}
