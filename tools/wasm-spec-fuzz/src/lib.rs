//! Property tests of the Wasm specification library's array programs (`Silmaril/WasmSpec`),
//! run on the `wasmi` interpreter: an independent engine, as `tested` evidence next to the
//! Lean proofs. The modules in `wasm/` are silmaril-lean's encoding (`encodeModule?`) of the
//! entries' quoted programs; `tests/sorts.rs` checks that they match the byte lists recorded in
//! the entries' Lean test modules.

use wasmi::{Engine, Instance, Linker, Memory, Module, Store};

/// A deterministic xorshift generator (no dependency on `rand`).
pub struct Rng(pub u64);

impl Rng {
    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    /// A random array: length below `max_len`, values in `[-range, range)`.
    pub fn array(&mut self, max_len: u64, range: i64) -> Vec<i32> {
        let n = self.next() % max_len;
        (0..n)
            .map(|_| ((self.next() % (2 * range as u64)) as i64 - range) as i32)
            .collect()
    }
}

/// An instantiated module and its memory `0`.
pub struct Inst {
    pub store: Store<()>,
    pub instance: Instance,
    pub memory: Memory,
}

impl Inst {
    pub fn new(wasm: &[u8]) -> Inst {
        let engine = Engine::default();
        let module = Module::new(&engine, wasm).expect("valid module");
        let mut store = Store::new(&engine, ());
        let instance = Linker::new(&engine)
            .instantiate(&mut store, &module)
            .expect("instantiate")
            .ensure_no_start(&mut store)
            .expect("no start");
        let memory = instance
            .get_memory(&store, "memory")
            .expect("exported memory");
        Inst {
            store,
            instance,
            memory,
        }
    }

    pub fn write_words(&mut self, p: usize, xs: &[i32]) {
        let data = self.memory.data_mut(&mut self.store);
        for (k, x) in xs.iter().enumerate() {
            data[p + 4 * k..p + 4 * k + 4].copy_from_slice(&x.to_le_bytes());
        }
    }

    pub fn read_words(&self, p: usize, n: usize) -> Vec<i32> {
        let data = self.memory.data(&self.store);
        (0..n)
            .map(|k| i32::from_le_bytes(data[p + 4 * k..p + 4 * k + 4].try_into().unwrap()))
            .collect()
    }

    pub fn bytes(&self) -> Vec<u8> {
        self.memory.data(&self.store).to_vec()
    }
}
