use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::{File, OpenOptions};
use std::io::{self, Read, Cursor, Write};
use std::path::Path;
use byteorder::{LittleEndian, ReadBytesExt};
use std::thread;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

mod memory;
use memory::{GcHeap, HeapData};

mod ffi;
use ffi::ForeignInterface;

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

    // Reference Types (Book of Life)
    Reference(usize),
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
            Data::Reference(idx) => write!(f, "{{Ref:{}}}", idx),
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

    fn as_ref_idx(&self) -> Option<usize> {
        match self.data {
            Data::Reference(idx) => Some(idx),
            _ => None,
        }
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

    heap: GcHeap,

    // Great Commission (FFI)
    ffi: ForeignInterface,

    // The Book of Genesis (System Intrinsics)
    open_scrolls: HashMap<usize, File>,
    next_fd: usize,

    // Debugger Fields (The Confessional)
    debug_mode: bool,
    breakpoints: HashSet<usize>,
    symbol_map: HashMap<usize, String>,

    // The Inquisition (Source Mapping)
    source_map: Vec<(usize, usize)>, // pc -> line
    source_lines: Vec<String>,
    source_path: Option<String>,
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

            heap: GcHeap::new(),

            ffi: ForeignInterface::new(),

            open_scrolls: HashMap::new(),
            next_fd: 1000,

            debug_mode,
            breakpoints: HashSet::new(),
            symbol_map: HashMap::new(),

            source_map: Vec::new(),
            source_lines: Vec::new(),
            source_path: None,
        }
    }

    fn load_debug_symbols(&mut self, lbc_filename: &str) {
        let sym_path = format!("{}.sym", lbc_filename);
        let Ok(sym_text) = std::fs::read_to_string(&sym_path) else {
            return;
        };

        let mut src_from_sym: Option<String> = None;
        let mut map: Vec<(usize, usize)> = Vec::new();

        for raw in sym_text.lines() {
            let line = raw.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            if let Some(rest) = line.strip_prefix("source=") {
                let p = rest.trim();
                if !p.is_empty() {
                    src_from_sym = Some(p.to_string());
                }
                continue;
            }

            let mut parts = line.split_whitespace();
            let Some(pc_s) = parts.next() else { continue; };
            let Some(line_s) = parts.next() else { continue; };
            let Ok(pc) = pc_s.parse::<usize>() else { continue; };
            let Ok(ln) = line_s.parse::<usize>() else { continue; };
            if ln == 0 {
                continue;
            }
            map.push((pc, ln));
        }

        map.sort_by_key(|(pc, _)| *pc);
        self.source_map = map;
        self.source_path = src_from_sym.clone();

        // Try to load the exact compiled source snapshot.
        let mut candidates: Vec<String> = Vec::new();
        if let Some(p) = src_from_sym {
            candidates.push(p);
        }
        candidates.push(format!("{}.src.lg", lbc_filename));
        if lbc_filename.ends_with(".lbc") {
            candidates.push(lbc_filename.trim_end_matches(".lbc").to_string() + ".lg");
        }

        for p in candidates {
            if Path::new(&p).is_file() {
                if let Ok(text) = std::fs::read_to_string(&p) {
                    self.source_lines = text.lines().map(|s| s.to_string()).collect();
                    self.source_path = Some(p);
                    break;
                }
            }
        }
    }

    fn line_for_pc(&self, pc: usize) -> Option<usize> {
        if self.source_map.is_empty() {
            return None;
        }
        // Upper bound search for last entry with entry.pc <= pc.
        let mut lo = 0usize;
        let mut hi = self.source_map.len();
        while lo < hi {
            let mid = (lo + hi) / 2;
            if self.source_map[mid].0 <= pc {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        if lo == 0 {
            return None;
        }
        Some(self.source_map[lo - 1].1)
    }

    fn print_source_context(&self) {
        let Some(line_num) = self.line_for_pc(self.pc) else {
            return;
        };
        if line_num == 0 {
            return;
        }
        let idx = line_num - 1;
        if idx < self.source_lines.len() {
            let text = self.source_lines[idx].trim_end();
            println!("\x1b[33mLine {}: {}\x1b[0m", line_num, text);
        } else {
            println!("\x1b[33mLine {}\x1b[0m", line_num);
        }
    }

    fn check_gc(&mut self) {
        if self.heap.bytes_allocated() > self.heap.threshold() {
            self.trigger_apokatastasis();
            if self.heap.bytes_allocated() > self.heap.threshold() {
                self.heap.grow_threshold();
            }
        }
    }

    fn trigger_apokatastasis(&mut self) {
        // Roots are: stack + all scoped values.
        self.heap.unmark_all();

        let mut roots: Vec<Value> = Vec::new();
        roots.extend(self.stack.iter().cloned());
        roots.extend(self.constants.iter().cloned());
        for scope in &self.scopes {
            for v in scope.values() {
                roots.push(v.clone());
            }
        }

        self.heap.mark_from_roots(&roots);
        let _freed = self.heap.sweep();
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
            0xF0 => "SYS_OPEN".to_string(),
            0xF1 => "SYS_WRITE".to_string(),
            0xF2 => "SYS_READ".to_string(),
            0xF3 => "SYS_CLOSE".to_string(),
            0xF4 => "SYS_TIME".to_string(),
            0xF5 => "SYS_ENV".to_string(),
            0xFE => {
                let mut idx = self.pc + 1;
                if idx + 4 > code.len() {
                    return "INVOKE_FOREIGN <truncated>".to_string();
                }
                let lib_len = self.peek_u32(code, idx) as usize;
                idx += 4;
                if idx + lib_len > code.len() {
                    return "INVOKE_FOREIGN <truncated>".to_string();
                }
                let lib = String::from_utf8_lossy(&code[idx..idx + lib_len]).to_string();
                idx += lib_len;

                if idx + 4 > code.len() {
                    return format!("INVOKE_FOREIGN {}::<truncated>", lib);
                }
                let fn_len = self.peek_u32(code, idx) as usize;
                idx += 4;
                if idx + fn_len > code.len() {
                    return format!("INVOKE_FOREIGN {}::<truncated>", lib);
                }
                let func = String::from_utf8_lossy(&code[idx..idx + fn_len]).to_string();
                format!("INVOKE_FOREIGN {}::{}", lib, func)
            }
            _ => format!("UNKNOWN (0x{:02X})", op),
        }
    }

    fn enter_confessional(&mut self, code: &[u8]) {
        println!("\n=== THE CONFESSIONAL (Addr: 0x{:04X}) ===", self.pc);
        self.print_source_context();
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

    fn genealogy_string(&self) -> String {
        // Minimal, always-available trace. We keep it string-based so it can live
        // inside Icon objects without introducing new runtime types.
        let mut parts: Vec<String> = Vec::new();
        parts.push(format!("pc={}", self.pc));
        if !self.call_stack.is_empty() {
            for (i, frame) in self.call_stack.iter().enumerate() {
                parts.push(format!("frame#{} return_addr={}", i, frame.return_addr));
            }
        }
        parts.join(" | ")
    }

    fn describe_sin(&self, sin: &Value) -> String {
        match &sin.data {
            Data::String(s) => s.clone(),
            Data::Reference(idx) => match self.heap.get(*idx) {
                Some(HeapData::Icon(map)) => {
                    let t = match map.get("__type__") {
                        Some(Value { data: Data::String(s), .. }) => Some(s.as_str()),
                        _ => None,
                    };
                    if let Some(tn) = t {
                        format!("{{Icon {} }}", tn)
                    } else {
                        "{Icon}".to_string()
                    }
                }
                Some(HeapData::Congregation(vec)) => format!("[List size: {}]", vec.len()),
                None => format!("{{Ref:{} (freed?)}}", idx),
            },
            _ => sin.to_string(),
        }
    }

    fn throw_value(&mut self, mut sin: Value) {
        if let Some(handler) = self.exception_stack.pop() {
            let summary = self.describe_sin(&sin);
            println!("[!] Error encountered: {}. Seeking Repentance...", summary);

            // Attach a genealogy trace to structured sins.
            let genealogy = self.genealogy_string();
            if let Data::Reference(idx) = sin.data {
                if let Some(HeapData::Icon(map)) = self.heap.get_mut(idx) {
                    map.insert("__genealogy__".to_string(), Value::new_string(genealogy));
                }
            }

            self.stack.truncate(handler.stack_depth);
            self.call_stack.truncate(handler.call_depth);
            // scopes = global + one per call frame
            let target_scopes_len = handler.call_depth.saturating_add(1);
            self.scopes.truncate(target_scopes_len);
            self.pc = handler.catch_addr;
            self.stack.push(sin);
        } else {
            panic!("Anathema: Uncaught Sin - {}", self.describe_sin(&sin));
        }
    }

    fn throw(&mut self, message: String) {
        self.throw_value(Value::new_string(message));
    }

    fn is_instance_of(&self, obj: &Value, typ: &str) -> bool {
        match &obj.data {
            Data::Int(_) => typ == "HolyInt",
            Data::Float(_) => typ == "HolyFloat",
            Data::String(_) => typ == "Text",
            Data::Boolean(_) => typ == "Bool" || typ == "Boolean",
            Data::Char(_) => typ == "Char",
            Data::Byte(_) => typ == "Byte",
            Data::Void => typ == "Void",
            Data::Reference(idx) => match self.heap.get(*idx) {
                Some(HeapData::Congregation(_)) => typ == "Congregation" || typ == "List",
                Some(HeapData::Icon(map)) => {
                    if typ == "Icon" {
                        return true;
                    }
                    if let Some(Value { data: Data::String(tn), .. }) = map.get("__type__") {
                        if tn == typ {
                            return true;
                        }
                    }
                    if let Some(Value { data: Data::Reference(bases_idx), .. }) = map.get("__bases__") {
                        if let Some(HeapData::Congregation(vec)) = self.heap.get(*bases_idx) {
                            for v in vec.iter() {
                                if let Data::String(s) = &v.data {
                                    if s == typ {
                                        return true;
                                    }
                                }
                            }
                        }
                    }
                    false
                }
                None => false,
            },
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
                0xD3 => { // IS_INSTANCE
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    stack_types.push("Bool");
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
                        Data::Reference(_) => "Any",
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
                0xF0 => { // SYS_OPEN
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    stack_types.push("Int");
                }
                0xF1 => { // SYS_WRITE
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    stack_types.push("Boolean");
                }
                0xF2 => { // SYS_READ
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    stack_types.push("String");
                }
                0xF3 => { // SYS_CLOSE
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                }
                0xF4 => { // SYS_TIME
                    stack_types.push("Int");
                }
                0xF5 => { // SYS_ENV
                    if stack_types.pop().is_none() { panic!("Verification Error: Stack Underflow at PC {}", pc-1); }
                    stack_types.push("Any");
                }
                0xFE => { // INVOKE_FOREIGN
                    // Payload: <u32 lib_len><bytes><u32 fn_len><bytes><u8 ret_tag><u8 argc><argc*u8 arg_tags>
                    let lib_len = cursor.read_u32::<LittleEndian>().unwrap() as usize;
                    pc += 4;
                    if pc + lib_len > code.len() {
                        panic!("Verification Error: INVOKE_FOREIGN lib truncated at PC {}", pc - 5);
                    }
                    cursor.set_position((pc + lib_len) as u64);
                    pc += lib_len;

                    let fn_len = cursor.read_u32::<LittleEndian>().unwrap() as usize;
                    pc += 4;
                    if pc + fn_len > code.len() {
                        panic!("Verification Error: INVOKE_FOREIGN fn truncated at PC {}", pc - 5);
                    }
                    cursor.set_position((pc + fn_len) as u64);
                    pc += fn_len;

                    let ret_tag = cursor.read_u8().unwrap();
                    pc += 1;
                    let argc = cursor.read_u8().unwrap() as usize;
                    pc += 1;

                    if pc + argc > code.len() {
                        panic!("Verification Error: INVOKE_FOREIGN arg tags truncated at PC {}", pc - 2);
                    }
                    cursor.set_position((pc + argc) as u64);
                    pc += argc;

                    for _ in 0..argc {
                        if stack_types.pop().is_none() {
                            panic!("Verification Error: Stack Underflow at PC {}", pc - 1);
                        }
                    }

                    match ret_tag {
                        0x00 => stack_types.push("Any"),
                        0x01 => stack_types.push("Int"),
                        0x02 => stack_types.push("Float"),
                        _ => stack_types.push("Any"),
                    }
                }
                _ => {}
            }
        }
        println!("[+] Ontological Verification successful.");
    }

    fn execute_slice(&mut self, code: &[u8], print_completion: bool) {
        self.verify(code);
        let mut cursor = Cursor::new(code);
        while self.pc < code.len() {

            // --- DEBUGGER HOOK ---
            if self.debug_mode || self.breakpoints.contains(&self.pc) {
                self.debug_mode = true;
                self.enter_confessional(code);
            }
            // ---------------------

            cursor.set_position(self.pc as u64);
            let opcode = cursor.read_u8().unwrap();
            self.pc += 1;

            match opcode {
                0x01 => { // HALT_AMEN
                    if print_completion {
                        println!("[+] Execution complete. Amen.");
                    }
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
                    let sin_val = match self.pop_or_throw("THROW requires a value") {
                        Some(v) => v,
                        None => continue,
                    };
                    self.throw_value(sin_val);
                    continue;
                }
                0xD3 => { // IS_INSTANCE
                    // Stack: [obj, typ] -> Bool
                    let typ_val = match self.pop_or_throw("IS_INSTANCE requires a type") {
                        Some(v) => v,
                        None => continue,
                    };
                    let obj_val = match self.pop_or_throw("IS_INSTANCE requires a value") {
                        Some(v) => v,
                        None => continue,
                    };
                    let typ = match typ_val.data {
                        Data::String(s) => s,
                        _ => {
                            self.throw("Ontological Error: IS_INSTANCE type must be Text".to_string());
                            continue;
                        }
                    };
                    let ok = self.is_instance_of(&obj_val, &typ);
                    self.stack.push(Value { data: Data::Boolean(ok), is_sacred: false });
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

                    let idx = self.heap.alloc(HeapData::Congregation(items));
                    self.check_gc();
                    self.stack.push(Value { data: Data::Reference(idx), is_sacred });
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

                    let idx = self.heap.alloc(HeapData::Congregation(vec));
                    self.check_gc();
                    self.stack.push(Value { data: Data::Reference(idx), is_sacred: false });
                }
                0xA1 => { // PARTAKE
                    let index_val = match self.pop_or_throw("PARTAKE requires an index") {
                        Some(v) => v,
                        None => continue,
                    };
                    let array_val = match self.pop_or_throw("PARTAKE requires a list") {
                        Some(v) => v,
                        None => continue,
                    };

                    let index = match index_val.data {
                        Data::Int(i) if i >= 0 => i as usize,
                        _ => {
                            self.throw("Ontological Error: Index must be HolyInt".to_string());
                            continue;
                        }
                    };

                    let Some(arr_idx) = array_val.as_ref_idx() else {
                        self.throw("Ontological Error: PARTAKE requires a Congregation".to_string());
                        continue;
                    };

                    match self.heap.get(arr_idx) {
                        Some(HeapData::Congregation(vec)) => {
                            if index >= vec.len() {
                                self.throw("Ontological Error: Index out of bounds".to_string());
                                continue;
                            }
                            self.stack.push(vec[index].clone());
                        }
                        _ => {
                            self.throw("Ontological Error: PARTAKE requires a Congregation".to_string());
                            continue;
                        }
                    }
                }
                0xA2 => { // INSCRIBE
                    let value = match self.pop_or_throw("INSCRIBE requires a value") {
                        Some(v) => v,
                        None => continue,
                    };
                    let index_val = match self.pop_or_throw("INSCRIBE requires an index") {
                        Some(v) => v,
                        None => continue,
                    };
                    let array_val = match self.pop_or_throw("INSCRIBE requires a list") {
                        Some(v) => v,
                        None => continue,
                    };

                    let index = match index_val.data {
                        Data::Int(i) if i >= 0 => i as usize,
                        _ => {
                            self.throw("Ontological Error: Index must be HolyInt".to_string());
                            continue;
                        }
                    };

                    let Some(arr_idx) = array_val.as_ref_idx() else {
                        self.throw("Ontological Error: INSCRIBE requires a Congregation".to_string());
                        continue;
                    };

                    match self.heap.get_mut(arr_idx) {
                        Some(HeapData::Congregation(vec)) => {
                            if index >= vec.len() {
                                self.throw("Ontological Error: Index out of bounds".to_string());
                                continue;
                            }
                            vec[index] = value;
                        }
                        _ => {
                            self.throw("Ontological Error: INSCRIBE requires a Congregation".to_string());
                            continue;
                        }
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

                    let idx = self.heap.alloc(HeapData::Icon(map));
                    self.check_gc();
                    self.stack.push(Value { data: Data::Reference(idx), is_sacred });
                }
                0xB1 => { // REVEAL <u32_key_idx>
                    let idx = cursor.read_u32::<LittleEndian>().unwrap();
                    self.pc += 4;

                    let field_name = match &self.constants[idx as usize].data {
                        Data::String(s) => s.clone(),
                        _ => panic!("Ontological Error: Symbol name must be a string"),
                    };

                    let icon_val = match self.pop_or_throw("REVEAL requires an icon") {
                        Some(v) => v,
                        None => continue,
                    };

                    let Some(icon_idx) = icon_val.as_ref_idx() else {
                        self.throw("Ontological Error: REVEAL requires an Icon".to_string());
                        continue;
                    };

                    match self.heap.get(icon_idx) {
                        Some(HeapData::Icon(map)) => {
                            let Some(val) = map.get(&field_name) else {
                                self.throw("Ontological Error: Unknown field".to_string());
                                continue;
                            };
                            self.stack.push(val.clone());
                        }
                        _ => {
                            self.throw("Ontological Error: REVEAL requires an Icon".to_string());
                            continue;
                        }
                    }
                }
                0xB2 => { // CONSECRATE <u32_key_idx>
                    let idx = cursor.read_u32::<LittleEndian>().unwrap();
                    self.pc += 4;

                    let field_name = match &self.constants[idx as usize].data {
                        Data::String(s) => s.clone(),
                        _ => panic!("Ontological Error: Symbol name must be a string"),
                    };

                    let value = match self.pop_or_throw("CONSECRATE requires a value") {
                        Some(v) => v,
                        None => continue,
                    };
                    let icon_val = match self.pop_or_throw("CONSECRATE requires an icon") {
                        Some(v) => v,
                        None => continue,
                    };

                    let Some(icon_idx) = icon_val.as_ref_idx() else {
                        self.throw("Ontological Error: CONSECRATE requires an Icon".to_string());
                        continue;
                    };

                    match self.heap.get_mut(icon_idx) {
                        Some(HeapData::Icon(map)) => {
                            map.insert(field_name, value);
                        }
                        _ => {
                            self.throw("Ontological Error: CONSECRATE requires an Icon".to_string());
                            continue;
                        }
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
                        Data::Reference(idx) => match self.heap.get(idx) {
                            Some(HeapData::Congregation(v)) => v.len(),
                            Some(HeapData::Icon(m)) => m.len(),
                            None => {
                                self.throw("Ontological Error: Dangling reference.".to_string());
                                continue;
                            }
                        },
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
                0xF0 => { // SYS_OPEN (Stack: [path, mode] -> [fd])
                    let mode_val = match self.pop_or_throw("SYS_OPEN requires a mode") {
                        Some(v) => v,
                        None => continue,
                    };
                    let path_val = match self.pop_or_throw("SYS_OPEN requires a path") {
                        Some(v) => v,
                        None => continue,
                    };

                    let path = match path_val.data {
                        Data::String(s) => s,
                        _ => {
                            self.throw("Ontological Error: Path must be Text".to_string());
                            continue;
                        }
                    };
                    let mode = match mode_val.data {
                        Data::Int(i) => i,
                        _ => {
                            self.throw("Ontological Error: Mode must be HolyInt".to_string());
                            continue;
                        }
                    };

                    // Modes: 0=Read, 1=Write(Truncate), 2=Append
                    let file_res = match mode {
                        0 => File::open(&path),
                        1 => File::create(&path),
                        2 => OpenOptions::new().write(true).append(true).create(true).open(&path),
                        _ => {
                            self.throw("Heresy: Unknown Scroll Mode".to_string());
                            continue;
                        }
                    };

                    match file_res {
                        Ok(f) => {
                            let fd = self.next_fd;
                            self.next_fd = self.next_fd.saturating_add(1);
                            self.open_scrolls.insert(fd, f);
                            self.stack.push(Value { data: Data::Int(fd as i64), is_sacred: false });
                        }
                        Err(_) => {
                            // Return 0 to signify the scroll could not be opened.
                            self.stack.push(Value { data: Data::Int(0), is_sacred: false });
                        }
                    }
                }
                0xF1 => { // SYS_WRITE (Stack: [fd, content] -> [bool])
                    let content_val = match self.pop_or_throw("SYS_WRITE requires content") {
                        Some(v) => v,
                        None => continue,
                    };
                    let fd_val = match self.pop_or_throw("SYS_WRITE requires fd") {
                        Some(v) => v,
                        None => continue,
                    };

                    let content = match content_val.data {
                        Data::String(s) => s,
                        _ => {
                            self.throw("Ontological Error: Content must be Text".to_string());
                            continue;
                        }
                    };
                    let fd = match fd_val.data {
                        Data::Int(i) if i >= 0 => i as usize,
                        _ => {
                            self.throw("Ontological Error: FD must be HolyInt".to_string());
                            continue;
                        }
                    };

                    let success = if let Some(file) = self.open_scrolls.get_mut(&fd) {
                        write!(file, "{}", content).is_ok()
                    } else {
                        false
                    };
                    self.stack.push(Value { data: Data::Boolean(success), is_sacred: false });
                }
                0xF2 => { // SYS_READ (Stack: [fd, bytes_to_read] -> [content])
                    let count_val = match self.pop_or_throw("SYS_READ requires count") {
                        Some(v) => v,
                        None => continue,
                    };
                    let fd_val = match self.pop_or_throw("SYS_READ requires fd") {
                        Some(v) => v,
                        None => continue,
                    };

                    let count = match count_val.data {
                        Data::Int(i) if i >= 0 => i as usize,
                        _ => {
                            self.throw("Ontological Error: Count must be HolyInt".to_string());
                            continue;
                        }
                    };
                    let fd = match fd_val.data {
                        Data::Int(i) if i >= 0 => i as usize,
                        _ => {
                            self.throw("Ontological Error: FD must be HolyInt".to_string());
                            continue;
                        }
                    };

                    if let Some(file) = self.open_scrolls.get_mut(&fd) {
                        let mut buffer = vec![0u8; count];
                        match file.read(&mut buffer) {
                            Ok(n) => {
                                buffer.truncate(n);
                                let s = String::from_utf8_lossy(&buffer).to_string();
                                self.stack.push(Value { data: Data::String(s), is_sacred: false });
                            }
                            Err(_) => {
                                self.stack.push(Value { data: Data::String("".to_string()), is_sacred: false });
                            }
                        }
                    } else {
                        self.stack.push(Value { data: Data::String("".to_string()), is_sacred: false });
                    }
                }
                0xF3 => { // SYS_CLOSE (Stack: [fd] -> [])
                    let fd_val = match self.pop_or_throw("SYS_CLOSE requires fd") {
                        Some(v) => v,
                        None => continue,
                    };
                    let fd = match fd_val.data {
                        Data::Int(i) if i >= 0 => i as usize,
                        _ => {
                            self.throw("Ontological Error: FD must be HolyInt".to_string());
                            continue;
                        }
                    };
                    self.open_scrolls.remove(&fd);
                }
                0xF4 => { // SYS_TIME (Stack: [] -> [timestamp_ms])
                    let start = SystemTime::now();
                    let since_the_epoch = start.duration_since(UNIX_EPOCH).unwrap_or_default();
                    let ms = since_the_epoch.as_millis() as i64;
                    self.stack.push(Value { data: Data::Int(ms), is_sacred: false });
                }
                0xF5 => { // SYS_ENV (Stack: [key] -> [value|Void])
                    let key_val = match self.pop_or_throw("SYS_ENV requires a key") {
                        Some(v) => v,
                        None => continue,
                    };
                    let key = match key_val.data {
                        Data::String(s) => s,
                        _ => {
                            self.throw("Ontological Error: Env Key must be Text".to_string());
                            continue;
                        }
                    };

                    match env::var(key) {
                        Ok(val) => self.stack.push(Value { data: Data::String(val), is_sacred: false }),
                        Err(_) => self.stack.push(Value { data: Data::Void, is_sacred: false }),
                    }
                }
                0xFE => { // INVOKE_FOREIGN
                    let lib_len = cursor.read_u32::<LittleEndian>().unwrap() as usize;
                    self.pc += 4;
                    let mut lib_buf = vec![0u8; lib_len];
                    cursor.read_exact(&mut lib_buf).unwrap();
                    self.pc += lib_len;
                    let lib_name = String::from_utf8_lossy(&lib_buf).to_string();

                    let fn_len = cursor.read_u32::<LittleEndian>().unwrap() as usize;
                    self.pc += 4;
                    let mut fn_buf = vec![0u8; fn_len];
                    cursor.read_exact(&mut fn_buf).unwrap();
                    self.pc += fn_len;
                    let func_name = String::from_utf8_lossy(&fn_buf).to_string();

                    let ret_tag = cursor.read_u8().unwrap();
                    self.pc += 1;
                    let argc = cursor.read_u8().unwrap() as usize;
                    self.pc += 1;

                    let mut arg_tags = vec![0u8; argc];
                    cursor.read_exact(&mut arg_tags).unwrap();
                    self.pc += argc;

                    let mut args: Vec<Value> = Vec::with_capacity(argc);
                    for _ in 0..argc {
                        let v = match self.pop_or_throw("INVOKE_FOREIGN requires arguments") {
                            Some(v) => v,
                            None => continue,
                        };
                        args.push(v);
                    }
                    args.reverse();

                    let res = self
                        .ffi
                        .call_typed(&lib_name, &func_name, ret_tag, &arg_tags, args);
                    self.stack.push(res);
                }
                _ => {
                    self.throw(format!("Ontological Error: Unknown Spirit 0x{:02X}", opcode));
                    continue;
                }
            }
        }
    }

    fn execute(&mut self, code: Vec<u8>) {
        self.execute_slice(&code, true);
    }

    fn execute_fragment(&mut self, mut fragment: Vec<u8>) {
        // Ensure the fragment terminates cleanly.
        fragment.push(0x01); // HALT
        self.pc = 0;
        self.execute_slice(&fragment, false);
        self.pc = 0;
    }

    fn print_status(&self) {
        if let Some(val) = self.stack.last() {
            println!("=> {}", val);
        } else {
            println!("=> (Void)");
        }
        io::stdout().flush().unwrap();
    }

    fn ingest_constant(&mut self, payload: &[u8]) {
        let mut cursor = Cursor::new(payload);
        let tag = match cursor.read_u8() {
            Ok(t) => t,
            Err(_) => {
                eprintln!("Heresy: empty constant payload");
                return;
            }
        };

        let val = match tag {
            0x01 => {
                let v = cursor.read_i64::<LittleEndian>().unwrap();
                Value { data: Data::Int(v), is_sacred: false }
            }
            0x02 => {
                let len = cursor.read_u32::<LittleEndian>().unwrap();
                let mut buf = vec![0u8; len as usize];
                cursor.read_exact(&mut buf).unwrap();
                Value { data: Data::String(String::from_utf8(buf).unwrap()), is_sacred: false }
            }
            0x03 => {
                let v = cursor.read_f64::<LittleEndian>().unwrap();
                Value { data: Data::Float(v), is_sacred: false }
            }
            0x04 => {
                let b = cursor.read_u8().unwrap();
                Value { data: Data::Boolean(b != 0), is_sacred: false }
            }
            0x05 => {
                let cp = cursor.read_u32::<LittleEndian>().unwrap();
                let ch = std::char::from_u32(cp).unwrap_or('\u{FFFD}');
                Value { data: Data::Char(ch), is_sacred: false }
            }
            0x06 => {
                let b = cursor.read_u8().unwrap();
                Value { data: Data::Byte(b), is_sacred: false }
            }
            _ => {
                eprintln!("Heresy: Invalid constant tag 0x{:02X}", tag);
                return;
            }
        };

        self.constants.push(val);
    }

    fn run_repl(&mut self) {
        let mut stdin = io::stdin();
        println!("[SVM] Ready for catechism...");
        io::stdout().flush().unwrap();

        loop {
            let mut type_buf = [0u8; 1];
            if stdin.read_exact(&mut type_buf).is_err() {
                break;
            }
            let p_type = type_buf[0];

            let mut len_buf = [0u8; 4];
            if stdin.read_exact(&mut len_buf).is_err() {
                break;
            }
            let len = u32::from_le_bytes(len_buf) as usize;

            let mut payload = vec![0u8; len];
            if len > 0 && stdin.read_exact(&mut payload).is_err() {
                break;
            }

            match p_type {
                0x01 => self.ingest_constant(&payload),
                0x02 => {
                    self.execute_fragment(payload);
                    self.print_status();
                }
                0x03 => break, // Amen
                _ => eprintln!("Heresy: Unknown packet type 0x{:02X}", p_type),
            }
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut debug_mode = false;
    let mut repl_mode = false;
    let mut filename: Option<String> = None;

    for a in args.iter().skip(1) {
        if a == "--debug" {
            debug_mode = true;
        } else if a == "--repl" {
            repl_mode = true;
        } else if filename.is_none() {
            filename = Some(a.clone());
        }
    }

    if repl_mode {
        let mut svm = SVM::new(Vec::new(), debug_mode);
        svm.run_repl();
        return;
    }

    let Some(filename) = filename else {
        println!("Usage: logos-svm <file.lbc> [--debug] | logos-svm --repl [--debug]");
        return;
    };

    let mut file = File::open(&filename).expect("Could not open file");
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
    if debug_mode {
        svm.load_debug_symbols(&filename);
    }
    svm.execute(code);
}
