use std::collections::HashMap;

use crate::{Data, Value};

/// The nature of the Essence stored in the Heap.
#[derive(Debug, Clone)]
pub enum HeapData {
    /// A List (Congregation)
    Congregation(Vec<Value>),
    /// A Map (Icon)
    Icon(HashMap<String, Value>),
}

/// A container for the Essence, tracking its spiritual state.
#[derive(Debug, Clone)]
pub struct GcObject {
    pub data: HeapData,
    pub marked: bool,
    pub bytes_estimate: usize,
}

/// The Creation (Heap).
/// Uses a free-list to reuse memory slots.
#[derive(Debug)]
pub struct GcHeap {
    objects: Vec<Option<GcObject>>, // None represents a free slot
    free_idxs: Vec<usize>,
    bytes_allocated: usize,
    threshold: usize,
}

impl GcHeap {
    pub fn new() -> Self {
        GcHeap {
            objects: Vec::with_capacity(1024),
            free_idxs: Vec::new(),
            bytes_allocated: 0,
            threshold: 1024 * 1024, // ~1MB initial threshold
        }
    }

    pub fn bytes_allocated(&self) -> usize {
        self.bytes_allocated
    }

    pub fn threshold(&self) -> usize {
        self.threshold
    }

    pub fn grow_threshold(&mut self) {
        self.threshold = self.threshold.saturating_mul(2).max(1024 * 1024);
    }

    /// Allocates a new Essence and returns its handle (index).
    pub fn alloc(&mut self, data: HeapData) -> usize {
        let size_est = estimate_size(&data);
        self.bytes_allocated = self.bytes_allocated.saturating_add(size_est);

        let obj = GcObject {
            data,
            marked: false,
            bytes_estimate: size_est,
        };

        if let Some(idx) = self.free_idxs.pop() {
            self.objects[idx] = Some(obj);
            idx
        } else {
            self.objects.push(Some(obj));
            self.objects.len() - 1
        }
    }

    pub fn get(&self, idx: usize) -> Option<&HeapData> {
        self.objects.get(idx).and_then(|o| o.as_ref().map(|g| &g.data))
    }

    pub fn get_mut(&mut self, idx: usize) -> Option<&mut HeapData> {
        self.objects
            .get_mut(idx)
            .and_then(|o| o.as_mut().map(|g| &mut g.data))
    }

    pub fn unmark_all(&mut self) {
        for obj in self.objects.iter_mut().flatten() {
            obj.marked = false;
        }
    }

    pub fn mark_from_roots(&mut self, roots: &[Value]) {
        let mut gray_stack: Vec<usize> = Vec::new();

        for v in roots {
            if let Data::Reference(idx) = v.data {
                gray_stack.push(idx);
            }
        }

        while let Some(idx) = gray_stack.pop() {
            let Some(Some(obj)) = self.objects.get_mut(idx) else {
                continue;
            };
            if obj.marked {
                continue;
            }
            obj.marked = true;

            match &obj.data {
                HeapData::Congregation(vec) => {
                    for v in vec {
                        if let Data::Reference(child_idx) = v.data {
                            gray_stack.push(child_idx);
                        }
                    }
                }
                HeapData::Icon(map) => {
                    for v in map.values() {
                        if let Data::Reference(child_idx) = v.data {
                            gray_stack.push(child_idx);
                        }
                    }
                }
            }
        }
    }

    /// Sweep dead objects. Returns estimated freed bytes.
    pub fn sweep(&mut self) -> usize {
        let mut freed = 0usize;
        for (idx, slot) in self.objects.iter_mut().enumerate() {
            let is_dead = slot.as_ref().is_some_and(|obj| !obj.marked);
            if is_dead {
                if let Some(obj) = slot.take() {
                    freed = freed.saturating_add(obj.bytes_estimate);
                }
                self.free_idxs.push(idx);
            }
        }
        self.bytes_allocated = self.bytes_allocated.saturating_sub(freed);
        freed
    }
}

fn estimate_size(data: &HeapData) -> usize {
    match data {
        HeapData::Congregation(v) => v.capacity() * std::mem::size_of::<Value>(),
        HeapData::Icon(m) => m.capacity() * (std::mem::size_of::<Value>() + 64),
    }
}
