use std::collections::HashMap;
use std::env;
use std::fs::File;
use std::io::{Read, Cursor};
use byteorder::{LittleEndian, ReadBytesExt};
use std::thread;
use std::time::Duration;

#[derive(Debug, Clone)]
enum Data {
    Int(i64),
    Float(f64),
    String(String),
}

#[derive(Debug, Clone)]
struct Value {
    data: Data,
    is_sacred: bool,
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.data {
            Data::Int(i) => write!(f, "{}", i),
            Data::Float(fl) => write!(f, "{}", fl),
            Data::String(s) => write!(f, "{}", s),
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

    fn verify(&self, code: &[u8]) {
        let mut stack_types = Vec::new();
        let mut cursor = Cursor::new(code);
        let mut pc = 0;
        while pc < code.len() {
            cursor.set_position(pc as u64);
            let opcode = cursor.read_u8().unwrap();
            pc += 1;
            match opcode {
                0x01 => break, // HALT
                0x10 => { // PUSH_ESS
                    let idx = cursor.read_u32::<LittleEndian>().unwrap();
                    pc += 4;
                    let val = &self.constants[idx as usize];
                    stack_types.push(match val.data {
                        Data::Int(_) => "Int",
                        Data::Float(_) => "Float",
                        Data::String(_) => "String",
                    });
                }
                0x11 => { // LOAD_ESS
                    cursor.read_u32::<LittleEndian>().unwrap();
                    pc += 4;
                    stack_types.push("Any");
                }
                0x20 => { // PETITION
                    cursor.read_u32::<LittleEndian>().unwrap();
                    pc += 4;
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-5); }
                }
                0x40 => { // BEHOLD
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                }
                0x50 => { // WITNESS
                    cursor.read_u8().unwrap();
                    pc += 1;
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-2); }
                    stack_types.push("Any");
                }
                0x60 => { // FAST
                    if let Some(t) = stack_types.pop() {
                        if t != "Int" && t != "Any" { panic!("Verification Error: FAST requires Int at PC {}", pc-1); }
                    } else { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                }
                0x70 | 0x71 | 0x72 | 0x73 => { // Arithmetic
                    let b = stack_types.pop();
                    let a = stack_types.pop();
                    if a.is_none() || b.is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    let (ta, tb) = (a.unwrap(), b.unwrap());
                    if (ta != "Int" && ta != "Any") || (tb != "Int" && tb != "Any") {
                        panic!("Verification Error: Arithmetic requires Int at PC {}", pc-1);
                    }
                    stack_types.push("Int");
                }
                0x74 | 0x75 | 0x76 | 0x77 | 0x78 | 0x79 => { // Comparison
                    let b = stack_types.pop();
                    let a = stack_types.pop();
                    if a.is_none() || b.is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    stack_types.push("Int"); // Result is boolean (Int 0/1)
                }
                0x80 => { // JMP
                    cursor.read_i32::<LittleEndian>().unwrap();
                    pc += 4;
                }
                0x81 => { // JZ
                    cursor.read_i32::<LittleEndian>().unwrap();
                    pc += 4;
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-5); }
                }
                _ => {}
            }
        }
        println!("[+] Ontological Verification successful.");
    }

    fn execute(&mut self, code: Vec<u8>) {
        self.verify(&code);
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
                    let mut val = self.constants[idx as usize].clone();
                    val.is_sacred = true;
                    self.stack.push(val);
                }
                0x11 => { // LOAD_ESS <u32_idx>
                    let idx = cursor.read_u32::<LittleEndian>().unwrap();
                    self.pc += 4;
                    let name = match &self.constants[idx as usize].data {
                        Data::String(s) => s,
                        _ => panic!("Ontological Error: Symbol name must be a string"),
                    };
                    let val = self.synod.get(name).expect("Ontological Error: Unknown spirit").clone();
                    self.stack.push(val);
                }
                0x20 => { // PETITION <u32_idx>
                    let idx = cursor.read_u32::<LittleEndian>().unwrap();
                    self.pc += 4;
                    let name = match &self.constants[idx as usize].data {
                        Data::String(s) => s,
                        _ => panic!("Ontological Error: Symbol name must be a string"),
                    };
                    let val = self.stack.pop().expect("Stack Underflow");
                    if let Some(existing) = self.synod.get(name) {
                        if existing.is_sacred {
                            panic!("Ontological Error: Attempt to corrupt Sacred Essence '{}'", name);
                        }
                    }
                    self.synod.insert(name.clone(), val);
                }
                0x40 => { // BEHOLD
                    let val = self.stack.pop().expect("Stack Underflow");
                    println!("{}", val);
                }
                0x50 => { // WITNESS <u8_type>
                    let type_tag = cursor.read_u8().unwrap();
                    self.pc += 1;
                    let val = self.stack.pop().expect("Stack Underflow");
                    match type_tag {
                        1 => { // To Int
                            let new_val = match &val.data {
                                Data::Int(i) => *i,
                                Data::String(s) => s.parse::<i64>().expect("Ontological Error: Failed to witness Text as HolyInt"),
                                Data::Float(f) => *f as i64,
                            };
                            self.stack.push(Value { data: Data::Int(new_val), is_sacred: false });
                        }
                        2 => { // To String
                            let new_val = format!("{}", val);
                            self.stack.push(Value { data: Data::String(new_val), is_sacred: false });
                        }
                        3 => { // To Float
                            let new_val = match &val.data {
                                Data::Int(i) => *i as f64,
                                Data::String(s) => s.parse::<f64>().expect("Ontological Error: Failed to witness Text as HolyFloat"),
                                Data::Float(f) => *f,
                            };
                            self.stack.push(Value { data: Data::Float(new_val), is_sacred: false });
                        }
                        _ => panic!("Ontological Error: Unknown type tag for Witness"),
                    }
                }
                0x60 => { // FAST
                    let val = self.stack.pop().expect("Stack Underflow");
                    if let Data::Int(ms) = val.data {
                        thread::sleep(Duration::from_millis(ms as u64));
                    }
                }
                0x70 => { // ADD
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    let is_sacred = a.is_sacred || b.is_sacred;
                    match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => self.stack.push(Value { data: Data::Int(va + vb), is_sacred }),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x71 => { // SUB
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    let is_sacred = a.is_sacred || b.is_sacred;
                    match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => self.stack.push(Value { data: Data::Int(va - vb), is_sacred }),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x72 => { // MUL
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    let is_sacred = a.is_sacred || b.is_sacred;
                    match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => self.stack.push(Value { data: Data::Int(va * vb), is_sacred }),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x73 => { // DIV
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    let is_sacred = a.is_sacred || b.is_sacred;
                    match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => self.stack.push(Value { data: Data::Int(va / vb), is_sacred }),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x74 => { // EQ
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    let is_sacred = a.is_sacred || b.is_sacred;
                    let res = match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => va == vb,
                        (Data::String(va), Data::String(vb)) => va == vb,
                        _ => false,
                    };
                    self.stack.push(Value { data: Data::Int(if res { 1 } else { 0 }), is_sacred });
                }
                0x75 => { // NE
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    let is_sacred = a.is_sacred || b.is_sacred;
                    let res = match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => va != vb,
                        (Data::String(va), Data::String(vb)) => va != vb,
                        _ => true,
                    };
                    self.stack.push(Value { data: Data::Int(if res { 1 } else { 0 }), is_sacred });
                }
                0x76 => { // LT
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    let is_sacred = a.is_sacred || b.is_sacred;
                    match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => self.stack.push(Value { data: Data::Int(if va < vb { 1 } else { 0 }), is_sacred }),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x77 => { // GT
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    let is_sacred = a.is_sacred || b.is_sacred;
                    match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => self.stack.push(Value { data: Data::Int(if va > vb { 1 } else { 0 }), is_sacred }),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x78 => { // LE
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    let is_sacred = a.is_sacred || b.is_sacred;
                    match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => self.stack.push(Value { data: Data::Int(if va <= vb { 1 } else { 0 }), is_sacred }),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x79 => { // GE
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    let is_sacred = a.is_sacred || b.is_sacred;
                    match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => self.stack.push(Value { data: Data::Int(if va >= vb { 1 } else { 0 }), is_sacred }),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x80 => { // JMP <i32_offset>
                    let offset = cursor.read_i32::<LittleEndian>().unwrap();
                    self.pc += 4;
                    self.pc = (self.pc as i64 + offset as i64) as usize;
                    continue;
                }
                0x81 => { // JZ <i32_offset>
                    let offset = cursor.read_i32::<LittleEndian>().unwrap();
                    self.pc += 4;
                    let val = self.stack.pop().expect("Stack Underflow");
                    if let Data::Int(0) = val.data {
                        self.pc = (self.pc as i64 + offset as i64) as usize;
                        continue;
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

    // Skip Seal of Purity (32 bytes)
    let mut seal = [0u8; 32];
    cursor.read_exact(&mut seal).unwrap();

    // Constant Pool
    let cp_count = cursor.read_u32::<LittleEndian>().unwrap();
    let mut constants = Vec::new();
    for _ in 0..cp_count {
        let tag = cursor.read_u8().unwrap();
        match tag {
            0x01 => {
                let val = cursor.read_i64::<LittleEndian>().unwrap();
                constants.push(Value { data: Data::Int(val), is_sacred: false });
            }
            0x02 => {
                let len = cursor.read_u32::<LittleEndian>().unwrap();
                let mut s_buf = vec![0u8; len as usize];
                cursor.read_exact(&mut s_buf).unwrap();
                constants.push(Value { data: Data::String(String::from_utf8(s_buf).unwrap()), is_sacred: false });
            }
            0x03 => {
                let val = cursor.read_f64::<LittleEndian>().unwrap();
                constants.push(Value { data: Data::Float(val), is_sacred: false });
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
