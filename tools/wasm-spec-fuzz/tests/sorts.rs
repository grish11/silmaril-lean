//! Property tests of `IsSorted`, `InsertionSort` and `MergeSort` (`Silmaril/WasmSpec`) on `wasmi`.
//!
//! Each test checks the entry's specification on thousands of pseudo-random inputs: `is_sorted`
//! answers whether the segment is sorted and changes no byte of memory; `insertion_sort` and
//! `merge_sort` leave the segment sorted (signed order) and a permutation of the input, and every
//! other byte of memory unchanged (for `merge_sort`: outside the segment and the scratch buffer).
//! The modules are checked to be the bytes recorded in the Lean test modules (silmaril-lean's
//! encoding of the quoted programs).

use std::fs;
use std::path::Path;
use wasm_spec_fuzz::{Inst, Rng};

const MEM: usize = 65536;

/// The `wasmBytes` list of a Lean test module.
fn lean_bytes(module: &str) -> Vec<u8> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let text = fs::read_to_string(root.join(module)).expect("Lean test module");
    let start = text
        .find("def wasmBytes : List UInt8 := [")
        .expect("wasmBytes")
        + 31;
    let end = start + text[start..].find(']').expect("end of wasmBytes");
    text[start..end]
        .split(',')
        .map(|t| t.trim().parse::<u8>().expect("byte"))
        .collect()
}

fn wasm(name: &str, lean_module: &str) -> Vec<u8> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("wasm")
        .join(name);
    let bytes = fs::read(path).expect("wasm file");
    assert_eq!(
        bytes,
        lean_bytes(lean_module),
        "{name} differs from the Lean encoding"
    );
    bytes
}

fn is_sorted(xs: &[i32]) -> bool {
    xs.windows(2).all(|w| w[0] <= w[1])
}

/// A random base address with room for `n` words.
fn base(rng: &mut Rng, n: usize) -> usize {
    (rng.next() as usize) % (MEM - 4 * n + 1)
}

#[test]
fn is_sorted_meets_spec() {
    let bytes = wasm(
        "is_sorted.wasm",
        "Silmaril/Proofs/WasmSpec/IsSorted/Tests.lean",
    );
    let mut rng = Rng(0x9e3779b97f4a7c15);
    for round in 0..3000 {
        let mut inst = Inst::new(&bytes);
        let f = inst
            .instance
            .get_typed_func::<(i32, i32), i32>(&inst.store, "is_sorted")
            .unwrap();
        let mut xs = rng.array(40, if round % 2 == 0 { 3 } else { i32::MAX as i64 });
        if round % 3 == 0 {
            xs.sort();
        }
        let p = base(&mut rng, xs.len());
        inst.write_words(p, &xs);
        let before = inst.bytes();
        let r = f
            .call(&mut inst.store, (p as i32, xs.len() as i32))
            .unwrap();
        assert_eq!(r, is_sorted(&xs) as i32, "is_sorted({p}, {xs:?})");
        assert_eq!(inst.bytes(), before, "memory changed");
    }
}

#[test]
fn insertion_sort_meets_spec() {
    let bytes = wasm(
        "insertion_sort.wasm",
        "Silmaril/Proofs/WasmSpec/InsertionSort/Tests.lean",
    );
    let mut rng = Rng(0x2545f4914f6cdd1d);
    for round in 0..3000 {
        let mut inst = Inst::new(&bytes);
        let f = inst
            .instance
            .get_typed_func::<(i32, i32), ()>(&inst.store, "insertion_sort")
            .unwrap();
        let xs = rng.array(60, if round % 2 == 0 { 4 } else { i32::MAX as i64 });
        let p = if round % 50 == 0 {
            MEM - 4 * xs.len()
        } else {
            base(&mut rng, xs.len())
        };
        // random bytes around the segment, to detect writes outside it
        for _ in 0..64 {
            let a = (rng.next() as usize) % MEM;
            inst.memory.data_mut(&mut inst.store)[a] = rng.next() as u8;
        }
        inst.write_words(p, &xs);
        let before = inst.bytes();
        f.call(&mut inst.store, (p as i32, xs.len() as i32))
            .unwrap();
        let mut expected = xs.clone();
        expected.sort();
        assert_eq!(inst.read_words(p, xs.len()), expected, "sort({p}, {xs:?})");
        let after = inst.bytes();
        assert_eq!(after[..p], before[..p], "bytes below the segment changed");
        assert_eq!(
            after[p + 4 * xs.len()..],
            before[p + 4 * xs.len()..],
            "bytes above changed"
        );
    }
}

#[test]
fn merge_sort_meets_spec() {
    let bytes = wasm(
        "merge_sort.wasm",
        "Silmaril/Proofs/WasmSpec/MergeSort/Tests.lean",
    );
    let mut rng = Rng(0x853c49e6748fea9b);
    for round in 0..3000 {
        let mut inst = Inst::new(&bytes);
        let f = inst
            .instance
            .get_typed_func::<(i32, i32, i32), ()>(&inst.store, "merge_sort")
            .unwrap();
        let xs = rng.array(200, if round % 2 == 0 { 5 } else { i32::MAX as i64 });
        let n = xs.len();
        // array and buffer disjoint, in either order, anywhere in memory
        let (p, t) = loop {
            let p = base(&mut rng, n);
            let t = base(&mut rng, n);
            if p + 4 * n <= t || t + 4 * n <= p {
                break (p, t);
            }
        };
        for _ in 0..64 {
            let a = (rng.next() as usize) % MEM;
            inst.memory.data_mut(&mut inst.store)[a] = rng.next() as u8;
        }
        inst.write_words(p, &xs);
        let before = inst.bytes();
        f.call(&mut inst.store, (p as i32, n as i32, t as i32))
            .unwrap();
        let mut expected = xs.clone();
        expected.sort();
        assert_eq!(
            inst.read_words(p, n),
            expected,
            "merge_sort({p}, {xs:?}, {t})"
        );
        let after = inst.bytes();
        for i in 0..MEM {
            let in_array = p <= i && i < p + 4 * n;
            let in_buffer = t <= i && i < t + 4 * n;
            if !in_array && !in_buffer {
                assert_eq!(
                    after[i], before[i],
                    "byte {i} changed (p = {p}, t = {t}, n = {n})"
                );
            }
        }
    }
}
