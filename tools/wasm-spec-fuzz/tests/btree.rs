//! Property tests of the `BTree` entry (`Silmaril/WasmSpec/BTree`) on `wasmi`: `oba_find` and
//! `oba_get` against their specifications on random ordered arrays, and `btree_search` against
//! set membership on random B-trees (branching factors 2 to 5) laid out in memory as the paper
//! describes (metadata page 0: `t` at 0, root page at 4; node page `x`: leaf indicator (nonzero: leaf) at
//! `65536 x`, keys OBA at `65536 x + 4`, child-page BA at `65536 x + 32768`). The trees are
//! built by CLRS insertion with node splitting, in Rust.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use wasm_spec_fuzz::{Inst, Rng};

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

fn wasm() -> Vec<u8> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("wasm/btree.wasm");
    let bytes = fs::read(path).expect("wasm file");
    assert_eq!(
        bytes,
        lean_bytes("Silmaril/Proofs/WasmSpec/BTree/Tests.lean")
    );
    bytes
}

/// An abstract B-tree node.
struct Node {
    keys: Vec<i32>,
    children: Vec<Node>,
}

impl Node {
    fn leaf() -> Node {
        Node {
            keys: vec![],
            children: vec![],
        }
    }
    fn is_leaf(&self) -> bool {
        self.children.is_empty()
    }
    /// Split the full child `i` (2t - 1 keys) of `self`.
    fn split_child(&mut self, i: usize, t: usize) {
        let child = &mut self.children[i];
        let right_keys = child.keys.split_off(t);
        let median = child.keys.pop().unwrap();
        let right_children = if child.is_leaf() {
            vec![]
        } else {
            child.children.split_off(t)
        };
        self.keys.insert(i, median);
        self.children.insert(
            i + 1,
            Node {
                keys: right_keys,
                children: right_children,
            },
        );
    }
    fn insert_nonfull(&mut self, k: i32, t: usize) {
        let mut i = self.keys.partition_point(|&x| x < k);
        if self.is_leaf() {
            self.keys.insert(i, k);
        } else {
            if self.children[i].keys.len() == 2 * t - 1 {
                self.split_child(i, t);
                if k > self.keys[i] {
                    i += 1;
                }
            }
            self.children[i].insert_nonfull(k, t);
        }
    }
}

fn insert(root: Node, k: i32, t: usize) -> Node {
    if root.keys.contains(&k) || contains(&root, k) {
        return root;
    }
    let mut root = root;
    if root.keys.len() == 2 * t - 1 {
        let mut new_root = Node {
            keys: vec![],
            children: vec![root],
        };
        new_root.split_child(0, t);
        root = new_root;
    }
    root.insert_nonfull(k, t);
    root
}

fn contains(n: &Node, k: i32) -> bool {
    match n.keys.binary_search(&k) {
        Ok(_) => true,
        Err(i) => !n.is_leaf() && contains(&n.children[i], k),
    }
}

/// Lay out `n` at the next free page; returns its page number.
fn layout(inst: &mut Inst, n: &Node, next: &mut u32) -> u32 {
    let x = *next;
    *next += 1;
    let pages: Vec<u32> = n.children.iter().map(|c| layout(inst, c, next)).collect();
    let base = 65536 * x as usize;
    inst.write_words(base, &[if n.is_leaf() { 1 } else { 0 }]);
    inst.write_words(base + 4, &[n.keys.len() as i32]);
    inst.write_words(base + 8, &n.keys);
    inst.write_words(base + 32768, &[pages.len() as i32]);
    let ps: Vec<i32> = pages.iter().map(|&p| p as i32).collect();
    inst.write_words(base + 32772, &ps);
    x
}

fn count(n: &Node) -> u32 {
    1 + n.children.iter().map(count).sum::<u32>()
}

#[test]
fn oba_find_and_get_meet_spec() {
    let bytes = wasm();
    let mut rng = Rng(0x1234_5678_9abc_def1);
    for _ in 0..2000 {
        let mut inst = Inst::new(&bytes);
        let find = inst
            .instance
            .get_typed_func::<(i32, i32), i32>(&inst.store, "oba_find")
            .unwrap();
        let get = inst
            .instance
            .get_typed_func::<(i32, i32), i32>(&inst.store, "oba_get")
            .unwrap();
        let mut xs = rng.array(50, 100);
        xs.sort();
        let x = 4 * ((rng.next() as usize) % 1000);
        inst.write_words(x, &[xs.len() as i32]);
        inst.write_words(x + 4, &xs);
        let e = (rng.next() % 220) as i32 - 110;
        let i = find.call(&mut inst.store, (x as i32, e)).unwrap() as usize;
        assert!(i <= xs.len() && xs[..i].iter().all(|&a| a < e) && xs[i..].iter().all(|&a| e <= a));
        for (k, &a) in xs.iter().enumerate() {
            assert_eq!(get.call(&mut inst.store, (x as i32, k as i32)).unwrap(), a);
        }
    }
}

#[test]
fn btree_search_meets_spec() {
    let bytes = wasm();
    let mut rng = Rng(0x0fed_cba9_8765_4321);
    for round in 0..300 {
        let t = 2 + (round % 4);
        let mut root = Node::leaf();
        let mut set = BTreeSet::new();
        for _ in 0..(rng.next() % 120) {
            let k = (rng.next() % 400) as i32 - 200;
            root = insert(root, k, t);
            set.insert(k);
        }
        let mut inst = Inst::new(&bytes);
        let pages = count(&root) + 1;
        inst.memory.grow(&mut inst.store, pages).expect("grow");
        inst.write_words(0, &[t as i32]);
        let mut next = 1;
        let r = layout(&mut inst, &root, &mut next);
        inst.write_words(4, &[r as i32]);
        let before = inst.bytes();
        let search = inst
            .instance
            .get_typed_func::<i32, i32>(&inst.store, "btree_search")
            .unwrap();
        for k in -210..210 {
            let b = search.call(&mut inst.store, k).unwrap();
            assert_eq!(b, set.contains(&k) as i32, "search {k} (t = {t})");
        }
        assert!(inst.bytes() == before, "memory changed");
    }
}
