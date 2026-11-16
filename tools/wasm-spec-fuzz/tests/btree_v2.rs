//! Property tests of the `BTree` entry, major version 2 (`Silmaril/WasmSpec/BTree/V2`), on `wasmi`:
//! random sequences of `btree_insert` and `btree_search` after `btree_create`, checked against a
//! Rust `BTreeSet` and against a Rust model of CLRS insertion (`Node`); after every insertion the
//! memory is parsed back and checked to be a B-tree (`check_tree`: leaf indicators, ordered keys
//! without duplicates, bounds, key counts `t - 1 ..= 2 t - 1` below the root, all leaves at one
//! depth, distinct pages, disjoint from the free pages and the metadata page) holding exactly
//! the set, and the **memory frame** is checked: every byte outside page `0`, the old tree's
//! pages and the old free pages is unchanged. Out-of-memory runs use a `wasmi` resource limiter
//! (growth refused beyond a page budget): `btree_insert` must then return `0` and leave a B-tree
//! of the old keys. Free-page runs put spare pages (filled with garbage) on the free list first.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use wasm_spec_fuzz::Rng;
use wasmi::{
    errors::{MemoryError, TableError},
    Engine, Instance, Linker, Memory, Module, ResourceLimiter, Store, TypedFunc,
};

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
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("wasm/btree_v2.wasm");
    let bytes = fs::read(path).expect("wasm file");
    assert_eq!(
        bytes,
        lean_bytes("Silmaril/Proofs/WasmSpec/BTree/V2/Tests.lean")
    );
    bytes
}

const PAGE: usize = 65536;

/// `n` rounds in release builds, a tenth (at least 4) in debug builds, where the memory checks
/// after every insertion are slow.
fn rounds(n: usize) -> usize {
    if cfg!(debug_assertions) {
        (n / 10).max(4)
    } else {
        n
    }
}

/// Refuses memory growth beyond `max_pages` pages.
struct Budget {
    max_pages: usize,
}

impl ResourceLimiter for Budget {
    fn memory_growing(
        &mut self,
        _: usize,
        desired: usize,
        _: Option<usize>,
    ) -> Result<bool, MemoryError> {
        Ok(desired <= self.max_pages * PAGE)
    }
    fn table_growing(&mut self, _: u32, _: u32, _: Option<u32>) -> Result<bool, TableError> {
        Ok(true)
    }
}

struct Tree {
    store: Store<Budget>,
    memory: Memory,
    create: TypedFunc<i32, i32>,
    insert: TypedFunc<i32, i32>,
    search: TypedFunc<i32, i32>,
}

impl Tree {
    fn new(bytes: &[u8], max_pages: usize) -> Tree {
        let engine = Engine::default();
        let module = Module::new(&engine, bytes).expect("valid module");
        let mut store = Store::new(&engine, Budget { max_pages });
        store.limiter(|b| b);
        let instance: Instance = Linker::new(&engine)
            .instantiate(&mut store, &module)
            .expect("instantiate")
            .ensure_no_start(&mut store)
            .expect("no start");
        let memory = instance.get_memory(&store, "memory").expect("memory");
        let create = instance.get_typed_func(&store, "btree_create").unwrap();
        let insert = instance.get_typed_func(&store, "btree_insert").unwrap();
        let search = instance.get_typed_func(&store, "btree_search").unwrap();
        Tree {
            store,
            memory,
            create,
            insert,
            search,
        }
    }
    fn bytes(&self) -> Vec<u8> {
        self.memory.data(&self.store).to_vec()
    }
    fn wd(&self, a: usize) -> i32 {
        let d = self.memory.data(&self.store);
        i32::from_le_bytes(d[a..a + 4].try_into().unwrap())
    }
    fn write(&mut self, a: usize, v: i32) {
        let d = self.memory.data_mut(&mut self.store);
        d[a..a + 4].copy_from_slice(&v.to_le_bytes());
    }
}

/// The abstract node read from memory, with its page.
#[derive(Debug, PartialEq, Eq, Clone)]
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
    fn contains(&self, k: i32) -> bool {
        match self.keys.binary_search(&k) {
            Ok(_) => true,
            Err(i) => !self.is_leaf() && self.children[i].contains(k),
        }
    }
}

fn model_insert(root: Node, k: i32, t: usize) -> Node {
    if root.contains(k) {
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

/// Read the tree at page `x`, checking the B-tree invariants; collects its pages and keys.
#[allow(clippy::too_many_arguments)]
fn read_node(
    tr: &Tree,
    x: usize,
    t: usize,
    root: bool,
    lo: Option<i32>,
    hi: Option<i32>,
    pages: &mut Vec<usize>,
    keys: &mut Vec<i32>,
    depth: usize,
    leaf_depth: &mut Option<usize>,
) -> Node {
    let size = tr.memory.data(&tr.store).len();
    assert!(
        x >= 1 && x < 32768 && (x + 1) * PAGE <= size,
        "page {x} out of range"
    );
    pages.push(x);
    let base = PAGE * x;
    let leaf = tr.wd(base) != 0;
    let n = tr.wd(base + 4) as usize;
    assert!(
        n <= 2 * t - 1 && (root || n >= t - 1),
        "key count {n} at page {x}"
    );
    let ks: Vec<i32> = (0..n).map(|j| tr.wd(base + 8 + 4 * j)).collect();
    assert!(
        ks.windows(2).all(|w| w[0] < w[1]),
        "keys not strictly increasing at page {x}"
    );
    assert!(ks
        .iter()
        .all(|&k| lo.is_none_or(|l| l < k) && hi.is_none_or(|h| k < h)));
    keys.extend(&ks);
    let mut children = vec![];
    if leaf {
        match leaf_depth {
            Some(d) => assert_eq!(*d, depth, "leaves at different depths"),
            None => *leaf_depth = Some(depth),
        }
    } else {
        let m = tr.wd(base + 32768) as usize;
        assert_eq!(m, n + 1, "pointer count at page {x}");
        for j in 0..m {
            let c = tr.wd(base + 32772 + 4 * j) as usize;
            let clo = if j == 0 { lo } else { Some(ks[j - 1]) };
            let chi = if j == n { hi } else { Some(ks[j]) };
            children.push(read_node(
                tr,
                c,
                t,
                false,
                clo,
                chi,
                pages,
                keys,
                depth + 1,
                leaf_depth,
            ));
        }
    }
    Node { keys: ks, children }
}

/// Check that memory holds a B-tree with branching factor `t` and key set `set`; returns the
/// abstract tree and the owned pages (metadata, tree, free list).
fn check_tree(tr: &Tree, t: usize, set: &BTreeSet<i32>) -> (Node, Vec<usize>) {
    assert_eq!(tr.wd(0) as usize, t);
    let r = tr.wd(4) as usize;
    let mut pages = vec![];
    let mut keys = vec![];
    let mut leaf_depth = None;
    let node = read_node(
        tr,
        r,
        t,
        true,
        None,
        None,
        &mut pages,
        &mut keys,
        0,
        &mut leaf_depth,
    );
    let nfree = tr.wd(8) as usize;
    let free: Vec<usize> = (0..nfree).map(|j| tr.wd(12 + 4 * j) as usize).collect();
    assert!(
        free.windows(2).all(|w| w[0] < w[1]),
        "free list not ordered"
    );
    let mut all = pages.clone();
    all.extend(&free);
    all.push(0);
    let distinct: BTreeSet<usize> = all.iter().copied().collect();
    assert_eq!(distinct.len(), all.len(), "pages not distinct");
    keys.sort();
    assert_eq!(keys, set.iter().copied().collect::<Vec<_>>(), "key set");
    (node, all)
}

/// Every byte of `after` outside the pages `owned` (and below `before.len()`) equals `before`.
fn check_frame(before: &[u8], after: &[u8], owned: &[usize]) {
    assert!(after.len() >= before.len());
    for (i, (&a, &b)) in before.iter().zip(after).enumerate() {
        if a != b {
            assert!(
                owned.contains(&(i / PAGE)),
                "byte {i} (page {}) outside the tree changed",
                i / PAGE
            );
        }
    }
}

#[test]
fn insert_and_search_meet_spec() {
    let bytes = wasm();
    let mut rng = Rng(0x2468_ace0_1357_9bdf);
    for round in 0..rounds(120) {
        let t = 2 + (round % 4);
        let mut tr = Tree::new(&bytes, 1 << 16);
        assert_eq!(tr.create.call(&mut tr.store, t as i32).unwrap(), 1);
        let mut set = BTreeSet::new();
        let mut model = Node::leaf();
        let range = 20 + (rng.next() % 400) as i32;
        // Pages the tree does not own, filled with garbage: the frame check must find them
        // unchanged.
        let extra = 1 + (rng.next() % 3) as u32;
        tr.memory.grow(&mut tr.store, extra).expect("grow");
        for a in (2 * PAGE..(2 + extra as usize) * PAGE).step_by(4) {
            tr.write(a, rng.next() as i32);
        }
        for _ in 0..(rng.next() % 300) {
            let k = (rng.next() % (2 * range as u64)) as i32 - range;
            let before = tr.bytes();
            let (_, owned) = check_tree(&tr, t, &set);
            assert_eq!(tr.insert.call(&mut tr.store, k).unwrap(), 1, "insert {k}");
            set.insert(k);
            model = model_insert(model, k, t);
            let (node, _) = check_tree(&tr, t, &set);
            assert_eq!(node, model, "structure differs from CLRS insertion");
            check_frame(&before, &tr.bytes(), &owned);
            let q = (rng.next() % (2 * range as u64)) as i32 - range;
            let before = tr.bytes();
            assert_eq!(
                tr.search.call(&mut tr.store, q).unwrap(),
                set.contains(&q) as i32
            );
            assert!(tr.bytes() == before, "search changed memory");
        }
        // Extreme keys.
        for k in [i32::MIN, i32::MAX, 0, -1] {
            assert_eq!(tr.insert.call(&mut tr.store, k).unwrap(), 1);
            set.insert(k);
            check_tree(&tr, t, &set);
        }
    }
}

#[test]
fn insert_out_of_memory_keeps_the_keys() {
    let bytes = wasm();
    let mut rng = Rng(0x1357_9bdf_2468_ace0);
    for round in 0..rounds(200) {
        let t = 2 + (round % 3);
        let budget = 2 + (rng.next() % 12) as usize;
        let mut tr = Tree::new(&bytes, budget);
        assert_eq!(tr.create.call(&mut tr.store, t as i32).unwrap(), 1);
        let mut set = BTreeSet::new();
        let mut failed = false;
        for _ in 0..400 {
            let k = (rng.next() % 2000) as i32 - 1000;
            let before = tr.bytes();
            let (_, owned) = check_tree(&tr, t, &set);
            let r = tr.insert.call(&mut tr.store, k).unwrap();
            if r == 1 {
                set.insert(k);
            } else {
                assert_eq!(r, 0);
                failed = true;
            }
            check_tree(&tr, t, &set);
            check_frame(&before, &tr.bytes(), &owned);
        }
        assert!(failed || budget >= 12, "budget {budget} never exhausted");
    }
    // create fails on an exhausted budget
    let mut tr = Tree::new(&bytes, 1);
    assert_eq!(tr.create.call(&mut tr.store, 2).unwrap(), 0);
    assert_eq!(tr.bytes().len(), 0);
}

#[test]
fn insert_uses_free_pages() {
    let bytes = wasm();
    let mut rng = Rng(0x0bad_cafe_dead_beef);
    for round in 0..rounds(60) {
        let t = 2 + (round % 3);
        let spare = 1 + (rng.next() % 8) as usize;
        let mut tr = Tree::new(&bytes, 2 + spare);
        assert_eq!(tr.create.call(&mut tr.store, t as i32).unwrap(), 1);
        tr.memory.grow(&mut tr.store, spare as u32).expect("grow");
        for a in (2 * PAGE..(2 + spare) * PAGE).step_by(4) {
            tr.write(a, rng.next() as i32);
        }
        tr.write(8, spare as i32);
        for j in 0..spare {
            tr.write(12 + 4 * j, (2 + j) as i32);
        }
        let mut set = BTreeSet::new();
        let mut failed = false;
        for _ in 0..200 {
            let k = (rng.next() % 1000) as i32 - 500;
            let before = tr.bytes();
            let (_, owned) = check_tree(&tr, t, &set);
            match tr.insert.call(&mut tr.store, k).unwrap() {
                1 => {
                    set.insert(k);
                }
                r => {
                    assert_eq!(r, 0);
                    failed = true;
                }
            }
            check_tree(&tr, t, &set);
            check_frame(&before, &tr.bytes(), &owned);
        }
        assert!(failed, "the free pages were never exhausted");
        assert_eq!(
            tr.bytes().len(),
            (2 + spare) * PAGE,
            "memory grew although the budget is spent"
        );
    }
}
