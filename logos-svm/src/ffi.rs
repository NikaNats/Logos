use std::collections::HashMap;
use std::ffi::c_void;

use libffi::low::{
    ffi_abi_FFI_DEFAULT_ABI, ffi_call, ffi_cif, ffi_prep_cif, ffi_status_FFI_OK, ffi_type,
    ffi_type_double, ffi_type_sint64, ffi_type_void,
};
use libloading::{Library, Symbol};

use crate::{Data, Value};

pub struct ForeignInterface {
    libs: HashMap<String, Library>,
}

impl ForeignInterface {
    pub fn new() -> Self {
        ForeignInterface {
            libs: HashMap::new(),
        }
    }

    fn lib(&mut self, lib_name: &str) -> &Library {
        if !self.libs.contains_key(lib_name) {
            // Caller provides a platform-appropriate name/path.
            let lib = unsafe { Library::new(lib_name) }
                .unwrap_or_else(|e| panic!("Could not load Gentile library '{}': {}", lib_name, e));
            self.libs.insert(lib_name.to_string(), lib);
        }
        self.libs.get(lib_name).unwrap()
    }

    pub fn call_typed(
        &mut self,
        lib_name: &str,
        func_name: &str,
        ret_tag: u8,
        arg_tags: &[u8],
        args: Vec<Value>,
    ) -> Value {
        unsafe {
            if arg_tags.len() != args.len() {
                panic!(
                    "FFI Error: arg tag count {} != arg count {}",
                    arg_tags.len(),
                    args.len()
                );
            }

            let lib = self.lib(lib_name);

            // Symbol: we treat it as an opaque function pointer.
            let func_symbol: Symbol<*const c_void> = lib
                .get(func_name.as_bytes())
                .unwrap_or_else(|e| panic!("Function '{}' not found in '{}': {}", func_name, lib_name, e));
            let func_ptr = *func_symbol;

            // Storage to keep pointers valid across ffi_call
            let mut c_ints: Vec<i64> = Vec::new();
            let mut c_floats: Vec<f64> = Vec::new();

            let mut arg_types: Vec<*mut ffi_type> = Vec::new();
            let mut arg_values: Vec<*mut c_void> = Vec::new();

            for (tag, arg) in arg_tags.iter().zip(args.iter()) {
                match (*tag, &arg.data) {
                    (0x01, Data::Int(i)) => {
                        c_ints.push(*i);
                        arg_types.push(&mut ffi_type_sint64);
                        arg_values.push(c_ints.last_mut().unwrap() as *mut _ as *mut c_void);
                    }
                    (0x02, Data::Float(f)) => {
                        c_floats.push(*f);
                        arg_types.push(&mut ffi_type_double);
                        arg_values.push(c_floats.last_mut().unwrap() as *mut _ as *mut c_void);
                    }
                    _ => {
                        panic!(
                            "FFI Error: Only HolyInt/HolyFloat are supported (tag=0x{:02X}, val={})",
                            tag, arg
                        );
                    }
                }
            }

            let rtype: *mut ffi_type = match ret_tag {
                0x00 => &mut ffi_type_void,
                0x01 => &mut ffi_type_sint64,
                0x02 => &mut ffi_type_double,
                _ => panic!("FFI Error: Unsupported return tag 0x{:02X}", ret_tag),
            };

            // Prepare CIF
            let mut cif: ffi_cif = std::mem::zeroed();
            let status = ffi_prep_cif(
                &mut cif,
                ffi_abi_FFI_DEFAULT_ABI,
                args.len() as u32,
                rtype,
                arg_types.as_mut_ptr(),
            );

            if status != ffi_status_FFI_OK {
                panic!("FFI Prep Failed");
            }

            match ret_tag {
                0x00 => {
                    ffi_call(
                        &mut cif,
                        Some(std::mem::transmute(func_ptr)),
                        std::ptr::null_mut(),
                        arg_values.as_mut_ptr(),
                    );
                    Value::new_void()
                }
                0x01 => {
                    let mut result: i64 = 0;
                    ffi_call(
                        &mut cif,
                        Some(std::mem::transmute(func_ptr)),
                        &mut result as *mut _ as *mut c_void,
                        arg_values.as_mut_ptr(),
                    );
                    Value {
                        data: Data::Int(result),
                        is_sacred: false,
                    }
                }
                0x02 => {
                    let mut result: f64 = 0.0;
                    ffi_call(
                        &mut cif,
                        Some(std::mem::transmute(func_ptr)),
                        &mut result as *mut _ as *mut c_void,
                        arg_values.as_mut_ptr(),
                    );
                    Value {
                        data: Data::Float(result),
                        is_sacred: false,
                    }
                }
                _ => unreachable!(),
            }
        }
    }
}
