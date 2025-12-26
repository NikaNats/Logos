use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::File;
use std::io::{self, Read, Cursor, Write};
use byteorder::{LittleEndian, ReadBytesExt};
use std::cell::RefCell;
use std::rc::Rc;
use std::thread;
use std::time::Duration;

#[derive(Debug, Clone)]
enum Data {
    Int(i64),
    Float(f64),
    String(String),

    Void,

    // The Minor Orders
    Boolean(bool),
    Char(char),
    Byte(u8),

    Congregation(Rc<RefCell<Vec<Value>>>),
    Icon(Rc<RefCell<HashMap<String, Value>>>),
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
            Data::Void => write!(f, "Void"),
            Data::Boolean(b) => write!(f, "{}", if *b { "Verily" } else { "Nay" }),
            Data::Char(c) => write!(f, "'{}'", c),
            Data::Byte(b) => write!(f, "0x{:02X}", b),
            Data::Congregation(v) => write!(f, "[List size: {}]", v.borrow().len()),
            Data::Icon(_) => write!(f, "{Icon}"),
        }
    }
}

impl Value {
    fn new_string(message: String) -> Self {
        Value { data: Data::String(message), is_sacred: false }
    }

    fn new_void() -> Self {
        Value { data: Data::Void, is_sacred: false }
    }
}

#[derive(Debug, Clone)]
struct CallFrame {
    return_addr: usize,
    base_ptr: usize,
}

#[derive(Debug, Clone)]
struct ExceptionHandler {
    catch_addr: usize,
    stack_depth: usize,
    call_depth: usize,
}

struct SVM {
    stack: Vec<Value>,
    call_stack: Vec<CallFrame>,
    exception_stack: Vec<ExceptionHandler>,
    scopes: Vec<HashMap<String, Value>>,
    constants: Vec<Value>,
    pc: usize,

    // Debugger Fields (The Confessional)
    debug_mode: bool,
    breakpoints: HashSet<usize>,
    symbol_map: HashMap<usize, String>,
}

impl SVM {
    fn new(constants: Vec<Value>, debug_mode: bool) -> Self {
        SVM {
            stack: Vec::new(),
            call_stack: Vec::new(),
            exception_stack: Vec::new(),
            scopes: vec![HashMap::new()],
            constants,
            pc: 0,

            debug_mode,
            breakpoints: HashSet::new(),
            symbol_map: HashMap::new(),
        }
    }

    fn peek_u32(&self, code: &[u8], idx: usize) -> u32 {
        if idx + 4 > code.len() {
            return 0;
        }
        let bytes: [u8; 4] = code[idx..idx + 4].try_into().unwrap();
        u32::from_le_bytes(bytes)
    }

    fn peek_i32(&self, code: &[u8], idx: usize) -> i32 {
        if idx + 4 > code.len() {
            return 0;
        }
        let bytes: [u8; 4] = code[idx..idx + 4].try_into().unwrap();
        i32::from_le_bytes(bytes)
    }

    fn disassemble_current(&self, code: &[u8]) -> String {
        if self.pc >= code.len() {
            return "END_OF_LITURGY".to_string();
        }

        let op = code[self.pc];
        match op {
            0x01 => "HALT_AMEN".to_string(),
            0x10 => {
                let idx = self.peek_u32(code, self.pc + 1) as usize;
                if idx < self.constants.len() {
                    format!("PUSH_ESS [{}] ({})", idx, self.constants[idx])
                } else {
                    format!("PUSH_ESS [{}]", idx)
                }
            }
            0x11 => {
                let idx = self.peek_u32(code, self.pc + 1) as usize;
                if idx < self.constants.len() {
                    format!("LOAD_ESS [{}] ({})", idx, self.constants[idx])
                } else {
                    format!("LOAD_ESS [{}]", idx)
                }
            }
            0x12 => {
                let off = self.peek_u32(code, self.pc + 1);
                format!("GET_LOCAL {}", off)
            }
            0x20 => {
                let idx = self.peek_u32(code, self.pc + 1) as usize;
                if idx < self.constants.len() {
                    format!("PETITION [{}] ({})", idx, self.constants[idx])
                } else {
                    format!("PETITION [{}]", idx)
                }
            }
            0x30 => "LISTEN".to_string(),
            0x40 => "BEHOLD".to_string(),
            0x50 => "WITNESS".to_string(),
            0x60 => "FAST".to_string(),
            0x70 => "ADD".to_string(),
            0x71 => "SUB".to_string(),
            0x72 => "MUL".to_string(),
            0x73 => "DIV".to_string(),
            0x74 => "EQ".to_string(),
            0x75 => "NE".to_string(),
            0x76 => "LT".to_string(),
            0x77 => "GT".to_string(),
            0x78 => "LE".to_string(),
            0x79 => "GE".to_string(),
            0x80 => {
                let offset = self.peek_i32(code, self.pc + 1);
                format!("JMP {}", offset)
            }
            0x81 => {
                let offset = self.peek_i32(code, self.pc + 1);
                format!("JZ {}", offset)
            }
            0x82 => {
                let count = self.peek_u32(code, self.pc + 1);
                format!("DISCERN (cases: {})", count)
            }
            0x90 => {
                let addr = self.peek_u32(code, self.pc + 1);
                if let Some(label) = self.symbol_map.get(&(addr as usize)) {
                    format!("CALL @{:04X} ({})", addr, label)
                } else {
                    format!("CALL @{:04X}", addr)
                }
            }
            0x91 => "RET".to_string(),
            0xA0 => {
                let count = self.peek_u32(code, self.pc + 1);
                format!("GATHER (Size: {})", count)
            }
            0xA1 => "PARTAKE".to_string(),
            0xA2 => "INSCRIBE".to_string(),
            0xA3 => "ALLOC".to_string(),
            0xB0 => {
                let count = self.peek_u32(code, self.pc + 1);
                format!("MOLD (Pairs: {})", count)
            }
            0xB1 => {
                let idx = self.peek_u32(code, self.pc + 1) as usize;
                if idx < self.constants.len() {
                    format!("REVEAL [{}] ({})", idx, self.constants[idx])
                } else {
                    format!("REVEAL [{}]", idx)
                }
            }
            0xB2 => {
                let idx = self.peek_u32(code, self.pc + 1) as usize;
                if idx < self.constants.len() {
                    format!("CONSECRATE [{}] ({})", idx, self.constants[idx])
                } else {
                    format!("CONSECRATE [{}]", idx)
                }
            }
            0xC0 => "MEASURE".to_string(),
            0xC1 => "PASSAGE".to_string(),
            0xD0 => "ENTER_TRY".to_string(),
            0xD1 => "EXIT_TRY".to_string(),
            0xD2 => "THROW".to_string(),
            0xE0 => "ABSOLVE".to_string(),
            _ => format!("UNKNOWN (0x{:02X})", op),
        }
    }

    fn enter_confessional(&mut self, code: &[u8]) {
        println!("\n=== THE CONFESSIONAL (Addr: 0x{:04X}) ===", self.pc);
        println!("Next:  {}", self.disassemble_current(code));

        print!("Stack: [");
        for i in 0..3 {
            if self.stack.len() > i {
                let idx = self.stack.len() - 1 - i;
                print!(" ({}) {} ", idx, self.stack[idx]);
            }
        }
        println!("] (Size: {})", self.stack.len());

        loop {
            print!("logos-dbg> ");
            io::stdout().flush().unwrap();

            let mut input = String::new();
            if io::stdin().read_line(&mut input).is_err() {
                println!("Revelation Error: Could not hear the input.");
                continue;
            }
            let input = input.trim();
            let parts: Vec<&str> = input.split_whitespace().collect();
            if parts.is_empty() {
                continue;
            }

            match parts[0] {
                "s" | "step" => {
                    self.debug_mode = true;
                    break;
                }
                "c" | "continue" => {
                    self.debug_mode = false;
                    println!("[+] Resuming Liturgy...");
                    break;
                }
                "b" | "break" => {
                    if parts.len() > 1 {
                        let addr_str = parts[1];
                        let addr = if addr_str.starts_with("0x") {
                            usize::from_str_radix(&addr_str[2..], 16).unwrap_or(0)
                        } else {
                            addr_str.parse::<usize>().unwrap_or(0)
                        };
                        self.breakpoints.insert(addr);
                        println!("[+] Breakpoint set at 0x{:04X}", addr);
                    } else {
                        println!("Usage: b <address>");
                    }
                }
                "st" | "stack" => {
                    println!("--- Full Stack Dump ---");
                    for (i, val) in self.stack.iter().enumerate().rev() {
                        println!("[{:03}] {}", i, val);
                    }
                }
                "m" | "mem" => {
                    println!("--- Synod (Global Scope) ---");
                    if let Some(global) = self.scopes.first() {
                        for (k, v) in global {
                            println!("'{}': {}", k, v);
                        }
                    }
                }
                "q" | "quit" => {
                    println!("Amen.");
                    std::process::exit(0);
                }
                "h" | "help" => {
                    println!("Commands:");
                    println!("  s, step      - Execute next instruction");
                    println!("  c, continue  - Run until breakpoint");
                    println!("  b, break <A> - Set breakpoint at address A");
                    println!("  st, stack    - Dump data stack");
                    println!("  m, mem       - Dump global synod variables");
                    println!("  q, quit      - Exit");
                }
                _ => println!("Unknown prayer. Try 'help'."),
            }
        }
    }
    
    fn lookup_symbol(&self, name: &str) -> Option<Value> {
        for scope in self.scopes.iter().rev() {
            if let Some(v) = scope.get(name) {
                return Some(v.clone());
            }
        }
        None
    }
    
    fn symbol_is_sacred_anywhere(&self, name: &str) -> bool {
        for scope in self.scopes.iter().rev() {
            if let Some(v) = scope.get(name) {
                return v.is_sacred;
            }
        }
        false
    }
    
    fn assign_symbol(&mut self, name: String, val: Value) {
        if self.symbol_is_sacred_anywhere(&name) {
            self.throw(format!("Ontological Error: Attempt to corrupt Sacred Essence '{}'", name));
            return;
        }
        
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name, val);
        } else {
            self.throw("Ontological Error: No scope available".to_string());
        }
    }
    
    fn absolve_symbol(&mut self, name: &str) {
        if self.symbol_is_sacred_anywhere(name) {
            self.throw(format!("Ontological Error: Attempt to corrupt Sacred Essence '{}'", name));
            return;
        }
        for scope in self.scopes.iter_mut().rev() {
            if scope.contains_key(name) {
                scope.insert(name.to_string(), Value::new_void());
                return;
            }
        }
        // If it doesn't exist, create it in the current scope.
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.to_string(), Value::new_void());
        }
    }

    fn throw(&mut self, message: String) {
        if let Some(handler) = self.exception_stack.pop() {
            println!("[!] Error encountered: {}. Seeking Repentance...", message);

            self.stack.truncate(handler.stack_depth);
            self.call_stack.truncate(handler.call_depth);
            // scopes = global + one per call frame
            let target_scopes_len = handler.call_depth.saturating_add(1);
            self.scopes.truncate(target_scopes_len);
            self.pc = handler.catch_addr;
            self.stack.push(Value::new_string(message));
        } else {
            panic!("Anathema: Uncaught Sin - {}", message);
        }
    }

    fn pop_or_throw(&mut self, context: &str) -> Option<Value> {
        match self.stack.pop() {
            Some(v) => Some(v),
            None => {
                self.throw(format!("Stack Underflow: {}", context));
                None
            }
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
                0x12 => { // GET_LOCAL
                    cursor.read_u32::<LittleEndian>().unwrap();
                    pc += 4;
                    stack_types.push("Any");
                }
                0x30 => { // LISTEN
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    stack_types.push("String");
                }
                0x90 => { // CALL
                    cursor.read_u32::<LittleEndian>().unwrap();
                    pc += 4;
                }
                0x91 => { // RET
                }
                0xD0 => { // ENTER_TRY
                    cursor.read_i32::<LittleEndian>().unwrap();
                    pc += 4;
                }
                0xD1 => { // EXIT_TRY
                }
                0xD2 => { // THROW
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                }
                0xE0 => { // ABSOLVE
                    cursor.read_u32::<LittleEndian>().unwrap();
                    pc += 4;
                }
                0xA0 => { // GATHER
                    let count = cursor.read_u32::<LittleEndian>().unwrap();
                    pc += 4;
                    for _ in 0..count {
                        if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-5); }
                    }
                    stack_types.push("Any");
                }
                0xA1 => { // PARTAKE
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    stack_types.push("Any");
                }
                0xA2 => { // INSCRIBE
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                }
                0xA3 => { // ALLOC
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    stack_types.push("Any");
                }
                0xB0 => { // MOLD
                    let count = cursor.read_u32::<LittleEndian>().unwrap();
                    pc += 4;
                    for _ in 0..count {
                        if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-5); }
                        if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-5); }
                    }
                    stack_types.push("Any");
                }
                0xB1 => { // REVEAL
                    cursor.read_u32::<LittleEndian>().unwrap();
                    pc += 4;
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-5); }
                    stack_types.push("Any");
                }
                0xB2 => { // CONSECRATE
                    cursor.read_u32::<LittleEndian>().unwrap();
                    pc += 4;
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-5); }
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-5); }
                }
                0x10 => { // PUSH_ESS
                    let idx = cursor.read_u32::<LittleEndian>().unwrap();
                    pc += 4;
                    let val = &self.constants[idx as usize];
                    stack_types.push(match &val.data {
                        Data::Int(_) => "Int",
                        Data::Float(_) => "Float",
                        Data::String(_) => "String",
                        Data::Void => "Any",
                        Data::Boolean(_) => "Boolean",
                        Data::Char(_) => "Char",
                        Data::Byte(_) => "Byte",
                        Data::Congregation(_) => "Any",
                        Data::Icon(_) => "Any",
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
                    // ADD also supports String concatenation (Text communion)
                    if opcode == 0x70 {
                        let ok = (
                            (ta == "Int" || ta == "Any") && (tb == "Int" || tb == "Any")
                        ) || (
                            (ta == "Float" || ta == "Any") && (tb == "Float" || tb == "Any")
                        ) || (
                            (ta == "String" || ta == "Any") && (tb == "String" || tb == "Any")
                        );
                        if !ok { panic!("Verification Error: ADD requires compatible natures at PC {}", pc-1); }
                        // result is Any (could be Int/Float/String)
                        stack_types.push("Any");
                    } else {
                        // SUB/MUL/DIV remain numeric
                        if !((ta == "Int" || ta == "Any") && (tb == "Int" || tb == "Any")) {
                            panic!("Verification Error: Arithmetic requires Int at PC {}", pc-1);
                        }
                        stack_types.push("Int");
                    }
                }
                0xC0 => { // MEASURE
                    // Pop String -> push Int
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    stack_types.push("Int");
                }
                0xC1 => { // PASSAGE
                    // Pop len, start, string -> push string
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    stack_types.push("String");
                }
                0x74 | 0x75 | 0x76 | 0x77 | 0x78 | 0x79 => { // Comparison
                    let b = stack_types.pop();
                    let a = stack_types.pop();
                    if a.is_none() || b.is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    stack_types.push("Boolean");
                }
                0x80 => { // JMP
                    cursor.read_i32::<LittleEndian>().unwrap();
                    pc += 4;
                }
                0x81 => { // JZ
                    cursor.read_i32::<LittleEndian>().unwrap();
                    pc += 4;
                    let t = stack_types.pop().unwrap_or_else(|| panic!("Verification Error: Stack Underflow at PC {}", pc-5));
                    if t != "Boolean" && t != "Int" && t != "Any" {
                        panic!("Verification Error: JZ requires Boolean (or Int for legacy) at PC {}", pc-5);
                    }
                }
                0x82 => { // DISCERN
                    let count = cursor.read_u32::<LittleEndian>().unwrap();
                    pc += 4;
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-5); }
                    for _ in 0..count {
                        cursor.read_i64::<LittleEndian>().unwrap();
                        cursor.read_i32::<LittleEndian>().unwrap();
                        pc += 12;
                    }
                    cursor.read_i32::<LittleEndian>().unwrap();
                    pc += 4;
                }
                _ => {}
            }
        }
        println!("[+] Ontological Verification successful.");
    }

    fn execute(&mut self, code: Vec<u8>) {
        self.verify(&code);
        let mut cursor = Cursor::new(&code);
        while self.pc < code.len() {

            // --- DEBUGGER HOOK ---
            if self.debug_mode || self.breakpoints.contains(&self.pc) {
                self.debug_mode = true;
                self.enter_confessional(&code);
            }
            // ---------------------

            cursor.set_position(self.pc as u64);
            let opcode = cursor.read_u8().unwrap();
            self.pc += 1;

            match opcode {
                0x01 => { // HALT_AMEN
                    println!("[+] Execution complete. Amen.");
                    return;
                }
                0x12 => { // GET_LOCAL <u32_offset>
                    let offset = cursor.read_u32::<LittleEndian>().unwrap() as usize;
                    self.pc += 4;
                    let frame = match self.call_stack.last() {
                        Some(f) => f,
                        None => {
                            self.throw("Global Scope has no locals".to_string());
                            continue;
                        }
                    };
                    let abs_index = frame.base_ptr + offset;
                    if abs_index >= self.stack.len() {
                        self.throw("Local access out of bounds".to_string());
                        continue;
                    }
                    let val = self.stack[abs_index].clone();
                    self.stack.push(val);
                }
                0x30 => { // LISTEN
                    let prompt_val = match self.pop_or_throw("LISTEN requires a prompt") {
                        Some(v) => v,
                        None => continue,
                    };
                    if let Data::String(s) = prompt_val.data {
                        print!("{}", s);
                        io::stdout().flush().unwrap();
                    } else {
                        self.throw("Ontological Error: Prompt must be Text.".to_string());
                        continue;
                    }

                    let mut buffer = String::new();
                    match io::stdin().read_line(&mut buffer) {
                        Ok(_) => {
                            let clean_input = buffer.trim().to_string();
                            self.stack.push(Value { data: Data::String(clean_input), is_sacred: false });
                        }
                        Err(error) => panic!("Revelation Error: Could not hear the input: {}", error),
                    }
                }
                0x90 => { // CALL <u32_addr>
                    let target_addr = cursor.read_u32::<LittleEndian>().unwrap() as usize;
                    self.pc += 4;
                    let bp = self.stack.len();
                    self.call_stack.push(CallFrame { return_addr: self.pc, base_ptr: bp });
                    self.scopes.push(HashMap::new());
                    self.pc = target_addr;
                    continue;
                }
                0x91 => { // RET
                    let frame = match self.call_stack.pop() {
                        Some(f) => f,
                        None => {
                            self.throw("Ontological Error: Root of Hierarchy reached".to_string());
                            continue;
                        }
                    };

                    // Pop scope for this frame.
                    if self.scopes.len() > 1 {
                        self.scopes.pop();
                    }

                    let return_value = if self.stack.len() > frame.base_ptr {
                        self.stack.pop()
                    } else {
                        None
                    };
                    self.stack.truncate(frame.base_ptr);
                    if let Some(v) = return_value {
                        self.stack.push(v);
                    }

                    self.pc = frame.return_addr;
                    continue;
                }
                0xD0 => { // ENTER_TRY <i32_offset>
                    let offset = cursor.read_i32::<LittleEndian>().unwrap();
                    self.pc += 4;
                    let catch_addr = (self.pc as i64 + offset as i64) as usize;
                    self.exception_stack.push(ExceptionHandler {
                        catch_addr,
                        stack_depth: self.stack.len(),
                        call_depth: self.call_stack.len(),
                    });
                }
                0xD1 => { // EXIT_TRY
                    self.exception_stack.pop();
                }
                0xD2 => { // THROW
                    let msg_val = match self.pop_or_throw("THROW requires a message") {
                        Some(v) => v,
                        None => continue,
                    };
                    let msg = msg_val.to_string();
                    self.throw(msg);
                    continue;
                }
                0xE0 => { // ABSOLVE <u32_name_idx>
                    let idx = cursor.read_u32::<LittleEndian>().unwrap();
                    self.pc += 4;
                    let name = match &self.constants[idx as usize].data {
                        Data::String(s) => s.clone(),
                        _ => {
                            self.throw("Ontological Error: Absolution target must be a symbol".to_string());
                            continue;
                        }
                    };

                    self.absolve_symbol(&name);
                }
                0xA0 => { // GATHER <u32_count>
                    let count = cursor.read_u32::<LittleEndian>().unwrap();
                    self.pc += 4;

                    let mut items = Vec::with_capacity(count as usize);
                    let mut is_sacred = false;
                    for _ in 0..count {
                        let v = self.stack.pop().expect("Stack Underflow");
                        is_sacred = is_sacred || v.is_sacred;
                        items.push(v);
                    }
                    items.reverse();

                    self.stack.push(Value {
                        data: Data::Congregation(Rc::new(RefCell::new(items))),
                        is_sacred,
                    });
                }
                0xA3 => { // ALLOC
                    let size_val = match self.pop_or_throw("ALLOC requires a size") {
                        Some(v) => v,
                        None => continue,
                    };
                    let size = match size_val.data {
                        Data::Int(i) if i >= 0 => i as usize,
                        _ => {
                            self.throw("Ontological Error: Size must be HolyInt".to_string());
                            continue;
                        }
                    };
                    let vec = vec![Value::new_void(); size];
                    self.stack.push(Value {
                        data: Data::Congregation(Rc::new(RefCell::new(vec))),
                        is_sacred: false,
                    });
                }
                0xA1 => { // PARTAKE
                    let index_val = self.stack.pop().expect("Stack Underflow");
                    let array_val = self.stack.pop().expect("Stack Underflow");

                    let index = match index_val.data {
                        Data::Int(i) => i as usize,
                        _ => panic!("Ontological Error: Index must be HolyInt"),
                    };

                    if let Data::Congregation(vec_rc) = array_val.data {
                        let vec = vec_rc.borrow();
                        if index >= vec.len() { panic!("Ontological Error: Index out of bounds"); }
                        self.stack.push(vec[index].clone());
                    } else {
                        panic!("Ontological Error: PARTAKE requires a Congregation");
                    }
                }
                0xA2 => { // INSCRIBE
                    let value = self.stack.pop().expect("Stack Underflow");
                    let index_val = self.stack.pop().expect("Stack Underflow");
                    let array_val = self.stack.pop().expect("Stack Underflow");

                    let index = match index_val.data {
                        Data::Int(i) => i as usize,
                        _ => panic!("Ontological Error: Index must be HolyInt"),
                    };

                    if let Data::Congregation(vec_rc) = array_val.data {
                        let mut vec = vec_rc.borrow_mut();
                        if index >= vec.len() { panic!("Ontological Error: Index out of bounds"); }
                        vec[index] = value;
                    } else {
                        panic!("Ontological Error: INSCRIBE requires a Congregation");
                    }
                }
                0xB0 => { // MOLD <u32_count>
                    let count = cursor.read_u32::<LittleEndian>().unwrap();
                    self.pc += 4;

                    let mut map = HashMap::new();
                    let mut is_sacred = false;
                    for _ in 0..count {
                        let val = self.stack.pop().expect("Stack Underflow");
                        let key_val = self.stack.pop().expect("Stack Underflow");
                        is_sacred = is_sacred || val.is_sacred || key_val.is_sacred;

                        let key = match key_val.data {
                            Data::String(s) => s,
                            _ => panic!("Ontological Error: Icon keys must be Text"),
                        };
                        map.insert(key, val);
                    }

                    self.stack.push(Value {
                        data: Data::Icon(Rc::new(RefCell::new(map))),
                        is_sacred,
                    });
                }
                0xB1 => { // REVEAL <u32_key_idx>
                    let idx = cursor.read_u32::<LittleEndian>().unwrap();
                    self.pc += 4;

                    let field_name = match &self.constants[idx as usize].data {
                        Data::String(s) => s.clone(),
                        _ => panic!("Ontological Error: Symbol name must be a string"),
                    };

                    let icon_val = self.stack.pop().expect("Stack Underflow");
                    if let Data::Icon(map_rc) = icon_val.data {
                        let map = map_rc.borrow();
                        let val = map.get(&field_name).expect("Ontological Error: Unknown field");
                        self.stack.push(val.clone());
                    } else {
                        panic!("Ontological Error: REVEAL requires an Icon");
                    }
                }
                0xB2 => { // CONSECRATE <u32_key_idx>
                    let idx = cursor.read_u32::<LittleEndian>().unwrap();
                    self.pc += 4;

                    let field_name = match &self.constants[idx as usize].data {
                        Data::String(s) => s.clone(),
                        _ => panic!("Ontological Error: Symbol name must be a string"),
                    };

                    let value = self.stack.pop().expect("Stack Underflow");
                    let icon_val = self.stack.pop().expect("Stack Underflow");

                    if let Data::Icon(map_rc) = icon_val.data {
                        let mut map = map_rc.borrow_mut();
                        map.insert(field_name, value);
                    } else {
                        panic!("Ontological Error: CONSECRATE requires an Icon");
                    }
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
                    match self.lookup_symbol(name) {
                        Some(v) => self.stack.push(v),
                        None => {
                            self.throw(format!("Ontological Error: Unknown spirit '{}'", name));
                            continue;
                        }
                    }
                }
                0x20 => { // PETITION <u32_idx>
                    let idx = cursor.read_u32::<LittleEndian>().unwrap();
                    self.pc += 4;
                    let name = match &self.constants[idx as usize].data {
                        Data::String(s) => s,
                        _ => panic!("Ontological Error: Symbol name must be a string"),
                    };
                    let val = match self.pop_or_throw("PETITION requires a value") {
                        Some(v) => v,
                        None => continue,
                    };
                    self.assign_symbol(name.clone(), val);
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
                                Data::Boolean(b) => if *b { 1 } else { 0 },
                                Data::Char(c) => *c as u32 as i64,
                                Data::Byte(b) => *b as i64,
                                _ => panic!("Ontological Error: Cannot witness this nature as HolyInt"),
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
                                Data::Boolean(b) => if *b { 1.0 } else { 0.0 },
                                Data::Char(c) => *c as u32 as f64,
                                Data::Byte(b) => *b as f64,
                                _ => panic!("Ontological Error: Cannot witness this nature as HolyFloat"),
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
                    let b = match self.pop_or_throw("ADD requires rhs") { Some(v) => v, None => continue };
                    let a = match self.pop_or_throw("ADD requires lhs") { Some(v) => v, None => continue };
                    let is_sacred = a.is_sacred || b.is_sacred;
                    match (a.data, b.data) {
                        (Data::Int(va), Data::Int(vb)) => {
                            self.stack.push(Value { data: Data::Int(va + vb), is_sacred });
                        }
                        (Data::Float(va), Data::Float(vb)) => {
                            self.stack.push(Value { data: Data::Float(va + vb), is_sacred });
                        }
                        (Data::String(sa), Data::String(sb)) => {
                            let combined = format!("{}{}", sa, sb);
                            self.stack.push(Value { data: Data::String(combined), is_sacred });
                        }
                        _ => {
                            self.throw("Schism Error: Incompatible natures for Synergy (Type Mismatch)".to_string());
                            continue;
                        }
                    }
                }
                0xC0 => { // MEASURE
                    let val = match self.pop_or_throw("MEASURE requires a value") {
                        Some(v) => v,
                        None => continue,
                    };
                    let len = match val.data {
                        Data::String(s) => s.chars().count(),
                        Data::Congregation(v) => v.borrow().len(),
                        Data::Icon(m) => m.borrow().len(),
                        _ => {
                            self.throw("Ontological Error: Cannot measure this essence.".to_string());
                            continue;
                        }
                    };
                    self.stack.push(Value { data: Data::Int(len as i64), is_sacred: false });
                }
                0x82 => { // DISCERN
                    let count = cursor.read_u32::<LittleEndian>().unwrap();
                    self.pc += 4;

                    let target_val = match self.pop_or_throw("DISCERN requires a value") {
                        Some(v) => v,
                        None => continue,
                    };
                    let target_int = match target_val.data {
                        Data::Int(i) => i,
                        _ => {
                            self.throw("Discernment currently requires HolyInt".to_string());
                            continue;
                        }
                    };

                    let mut matched_offset: Option<i32> = None;
                    for _ in 0..count {
                        let case_val = cursor.read_i64::<LittleEndian>().unwrap();
                        let offset = cursor.read_i32::<LittleEndian>().unwrap();
                        self.pc += 12;
                        if matched_offset.is_none() && target_int == case_val {
                            matched_offset = Some(offset);
                        }
                    }
                    let default_offset = cursor.read_i32::<LittleEndian>().unwrap();
                    self.pc += 4;

                    let jump_offset = matched_offset.unwrap_or(default_offset);
                    let new_pc = (self.pc as i64 + jump_offset as i64) as usize;
                    self.pc = new_pc;
                    continue;
                }
                0xC1 => { // PASSAGE
                    let len_val = self.stack.pop().expect("Stack Underflow");
                    let start_val = self.stack.pop().expect("Stack Underflow");
                    let str_val = self.stack.pop().expect("Stack Underflow");

                    let len = match len_val.data { Data::Int(i) => i as usize, _ => panic!("Length must be HolyInt") };
                    let start = match start_val.data { Data::Int(i) => i as usize, _ => panic!("Start must be HolyInt") };

                    if let Data::String(s) = str_val.data {
                        let substring: String = s.chars().skip(start).take(len).collect();
                        self.stack.push(Value { data: Data::String(substring), is_sacred: false });
                    } else {
                        panic!("Ontological Error: Only Text can be divided into Passages.");
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
                    let b = match self.pop_or_throw("DIV requires rhs") { Some(v) => v, None => continue };
                    let a = match self.pop_or_throw("DIV requires lhs") { Some(v) => v, None => continue };
                    let is_sacred = a.is_sacred || b.is_sacred;
                    match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => {
                            if *vb == 0 {
                                self.throw("Division by Zero".to_string());
                                continue;
                            }
                            self.stack.push(Value { data: Data::Int(va / vb), is_sacred })
                        }
                        _ => {
                            self.throw("Ontological Error: Type mismatch in Synergy".to_string());
                            continue;
                        }
                    }
                }
                0x74 => { // EQ
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    let is_sacred = a.is_sacred || b.is_sacred;
                    let res = match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => va == vb,
                        (Data::Float(va), Data::Float(vb)) => va == vb,
                        (Data::String(va), Data::String(vb)) => va == vb,
                        (Data::Boolean(va), Data::Boolean(vb)) => va == vb,
                        (Data::Char(va), Data::Char(vb)) => va == vb,
                        (Data::Byte(va), Data::Byte(vb)) => va == vb,
                        _ => false,
                    };
                    self.stack.push(Value { data: Data::Boolean(res), is_sacred });
                }
                0x75 => { // NE
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    let is_sacred = a.is_sacred || b.is_sacred;
                    let res = match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => va != vb,
                        (Data::Float(va), Data::Float(vb)) => va != vb,
                        (Data::String(va), Data::String(vb)) => va != vb,
                        (Data::Boolean(va), Data::Boolean(vb)) => va != vb,
                        (Data::Char(va), Data::Char(vb)) => va != vb,
                        (Data::Byte(va), Data::Byte(vb)) => va != vb,
                        _ => true,
                    };
                    self.stack.push(Value { data: Data::Boolean(res), is_sacred });
                }
                0x76 => { // LT
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    let is_sacred = a.is_sacred || b.is_sacred;
                    match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => self.stack.push(Value { data: Data::Boolean(va < vb), is_sacred }),
                        (Data::Float(va), Data::Float(vb)) => self.stack.push(Value { data: Data::Boolean(va < vb), is_sacred }),
                        (Data::Char(va), Data::Char(vb)) => self.stack.push(Value { data: Data::Boolean(va < vb), is_sacred }),
                        (Data::Byte(va), Data::Byte(vb)) => self.stack.push(Value { data: Data::Boolean(va < vb), is_sacred }),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x77 => { // GT
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    let is_sacred = a.is_sacred || b.is_sacred;
                    match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => self.stack.push(Value { data: Data::Boolean(va > vb), is_sacred }),
                        (Data::Float(va), Data::Float(vb)) => self.stack.push(Value { data: Data::Boolean(va > vb), is_sacred }),
                        (Data::Char(va), Data::Char(vb)) => self.stack.push(Value { data: Data::Boolean(va > vb), is_sacred }),
                        (Data::Byte(va), Data::Byte(vb)) => self.stack.push(Value { data: Data::Boolean(va > vb), is_sacred }),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x78 => { // LE
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    let is_sacred = a.is_sacred || b.is_sacred;
                    match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => self.stack.push(Value { data: Data::Boolean(va <= vb), is_sacred }),
                        (Data::Float(va), Data::Float(vb)) => self.stack.push(Value { data: Data::Boolean(va <= vb), is_sacred }),
                        (Data::Char(va), Data::Char(vb)) => self.stack.push(Value { data: Data::Boolean(va <= vb), is_sacred }),
                        (Data::Byte(va), Data::Byte(vb)) => self.stack.push(Value { data: Data::Boolean(va <= vb), is_sacred }),
                        _ => panic!("Ontological Error: Type mismatch in Synergy"),
                    }
                }
                0x79 => { // GE
                    let b = self.stack.pop().expect("Stack Underflow");
                    let a = self.stack.pop().expect("Stack Underflow");
                    let is_sacred = a.is_sacred || b.is_sacred;
                    match (&a.data, &b.data) {
                        (Data::Int(va), Data::Int(vb)) => self.stack.push(Value { data: Data::Boolean(va >= vb), is_sacred }),
                        (Data::Float(va), Data::Float(vb)) => self.stack.push(Value { data: Data::Boolean(va >= vb), is_sacred }),
                        (Data::Char(va), Data::Char(vb)) => self.stack.push(Value { data: Data::Boolean(va >= vb), is_sacred }),
                        (Data::Byte(va), Data::Byte(vb)) => self.stack.push(Value { data: Data::Boolean(va >= vb), is_sacred }),
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
                    let val = match self.pop_or_throw("JZ requires a condition") {
                        Some(v) => v,
                        None => continue,
                    };
                    let condition = match val.data {
                        Data::Boolean(b) => b,
                        Data::Int(i) => i != 0,
                        _ => {
                            self.throw("Ontological Error: Condition must be Boolean".to_string());
                            continue;
                        }
                    };

                    if !condition {
                        self.pc = (self.pc as i64 + offset as i64) as usize;
                        continue;
                    }
                }
                _ => {
                    self.throw(format!("Ontological Error: Unknown Spirit 0x{:02X}", opcode));
                    continue;
                }
            }
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("Usage: logos-svm <file.lbc> [--debug]");
        return;
    }

    let debug_mode = args.len() > 2 && args[2] == "--debug";

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
            0x04 => {
                let b = cursor.read_u8().unwrap();
                constants.push(Value { data: Data::Boolean(b != 0), is_sacred: false });
            }
            0x05 => {
                let cp = cursor.read_u32::<LittleEndian>().unwrap();
                let ch = std::char::from_u32(cp).unwrap_or('\u{FFFD}');
                constants.push(Value { data: Data::Char(ch), is_sacred: false });
            }
            0x06 => {
                let b = cursor.read_u8().unwrap();
                constants.push(Value { data: Data::Byte(b), is_sacred: false });
            }
            _ => panic!("Ontological Error: Invalid constant tag"),
        }
    }

    // Code Section
    let code_len = cursor.read_u32::<LittleEndian>().unwrap();
    let mut code = vec![0u8; code_len as usize];
    cursor.read_exact(&mut code).unwrap();

    let mut svm = SVM::new(constants, debug_mode);
    svm.execute(code);
}
