module

public import Silmaril.Wasm.Wat
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.Logic.Words.Defs
public import Silmaril.Wasm.Logic.Total.Defs

/-!
# The B-tree library of Wasm Logic (Watt et al., ECOOP 2019), major version 2

Version 2 of the entry `BTree` (version 1: `Silmaril.WasmSpec.BTree`, superseded): the B-tree
library of the paper's §4 with **insertion and creation implemented**, page allocation through
`memory.grow` and an explicit free-page list, and specifications in Silmaril's every-run total
correctness (`TFSpecAt`) where the paper's triples are partial correctness.

## The program (`btree.wat`)

Functions, by index:

0. `oba_get(x, k)`: element `k` of the bounded array at `x` (the paper's `OBAGet`, Figure 12,
   also used on the unordered pointer arrays, as the report's `GetNodePtr` does);
1. `oba_find(x, e)`: the first index whose element is not below `e` (`OBAFind`, Figure 13);
2. `btree_search(k)`: `1` if `k` is a key, else `0` (`BTreeSearch`, report §B.5.2), descending
   in a loop where the report recurses;
3. `ba_insert(x, j, v)`: insert `v` at index `j` of the bounded array at `x`, shifting the
   elements from `j` on (the report's `OBAInsert`/`BASet`/`AsegShr`, combined);
4. `ba_copy(src, dst, n)`: make the bounded array at `dst` hold the `n` words at `src`;
5. `alloc_node()`: a page for a node: the **last** page of the free list if it is non-empty
   (the report's `AllocNode` takes the first and calls `OBADelete`), else a page from
   `memory.grow 1`; `-1` when growth fails or the new page is beyond `32767` (the report
   loops forever instead);
6. `split_child(x, i, z)`: split the full child `i` of node `x` (CLRS `B-TREE-SPLIT-CHILD`,
   the report's `BTreeSplitChild`), the right half going to the free page `z`;
7. `insert_nonfull(x, k)`: insert `k` below the non-full node `x`, splitting full children on
   the way down (CLRS `B-TREE-INSERT-NONFULL`, the report's `BTreeInsertNonFull`, recursive);
   `0` when a page allocation fails;
8. `btree_create(t)`: from an empty memory, the metadata page and an empty root leaf
   (`BTreeCreate`, report §B.5.1, with one `memory.grow 2`); `0` when growth fails;
9. `btree_insert(k)`: insert `k` (`BTreeInsert`, report §B.5.3): nothing if `btree_search`
   finds it, else grow the root if it is full, then `insert_nonfull`; `1` on success, `0`
   when a page allocation fails.

## Layout (paper §4.2, report §B.3–B.5)

* `OBA`/`BA`/`OBAnd` as in version 1;
* page `x` of a node: leaf indicator at `65536 x` (nonzero: a leaf, as in the report's code),
  keys `OBAnd` at `65536 x + 4` (at most 8090), child pages `BA` at `65536 x + 32768` (at most
  8091), as in the paper's §4.2 (the report's §B.4 uses 4095/4096);
* metadata page `0` (`Meta`): branching factor `t` at `0`, root page at `4`, the free pages
  `φ` as an `OBAnd` at `8` of capacity 16381 (the paper's `Free(φ)`);
* `Tree`: abstract nodes **carrying their page**; `Repr B T`, `Ordered`, `Balanced` as in
  version 1; `Owns p T` (page `p` is a node of `T`) and `Distinct T` (no page is used twice),
  the separation the paper's `*` gives; every node and free page lies in `[1, 32768)` and in
  memory (`PageOK`), free pages are not nodes of the tree, and the memory size is a whole
  number of pages;
* `2 ≤ t ≤ 4045`, so that a full node (`2 t - 1` keys, `2 t` children) fits the arrays (the
  paper's bound 4095 would allow `8189 > 8090` keys).

## Specifications

`searchSpec` (store unchanged, `1` iff `k ∈ κ`), `insertSpec` (`1` and `κ ∪ {k}`, or `0` and
`κ`: an out-of-memory outcome where the paper does not terminate; every byte outside page `0`,
the old tree's pages and the old free pages is unchanged; only memory `0` changes) and
`createSpec` (`1` and an empty tree, or `0` and the memory unchanged), each at every profile
and host relation, for instances whose function indices resolve to the module's functions
(`Resolved`).

A Silmaril addition (the predicates transcribe the paper's; the code follows the report).
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Hoare (FSpec)

/-- **The module.** -/
def program := wat3! r#"
(module
  (memory (export "memory") 0)
  (func $oba_get (export "oba_get") (param $x i32) (param $k i32) (result i32)
    (i32.load offset=4 (i32.add (local.get $x) (i32.mul (local.get $k) (i32.const 4)))))
  (func $oba_find (export "oba_find") (param $x i32) (param $e i32) (result i32)
    (local $i i32)
    (block $done
      (loop $next
        (br_if $done (i32.ge_u (local.get $i) (i32.load (local.get $x))))
        (br_if $done (i32.ge_s
          (i32.load offset=4 (i32.add (local.get $x) (i32.mul (local.get $i) (i32.const 4))))
          (local.get $e)))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $next)))
    (local.get $i))
  (func $btree_search (export "btree_search") (param $k i32) (result i32)
    (local $x i32) (local $i i32) (local $keys i32)
    (local.set $x (i32.load (i32.const 4)))
    (block $never
      (loop $descend
        (local.set $keys (i32.add (i32.mul (local.get $x) (i32.const 65536)) (i32.const 4)))
        (local.set $i (call $oba_find (local.get $keys) (local.get $k)))
        (if (i32.lt_u (local.get $i) (i32.load (local.get $keys)))
          (then
            (if (i32.eq (call $oba_get (local.get $keys) (local.get $i)) (local.get $k))
              (then (return (i32.const 1))))))
        (if (i32.load (i32.mul (local.get $x) (i32.const 65536)))
          (then (return (i32.const 0))))
        (local.set $x (call $oba_get
          (i32.add (i32.mul (local.get $x) (i32.const 65536)) (i32.const 32768)) (local.get $i)))
        (br $descend)))
    (i32.const 0))
  (func $ba_insert (export "ba_insert") (param $x i32) (param $j i32) (param $v i32)
    (local $i i32)
    (local.set $i (i32.load (local.get $x)))
    (block $done
      (loop $shift
        (br_if $done (i32.le_u (local.get $i) (local.get $j)))
        (i32.store offset=4 (i32.add (local.get $x) (i32.mul (local.get $i) (i32.const 4)))
          (i32.load (i32.add (local.get $x) (i32.mul (local.get $i) (i32.const 4)))))
        (local.set $i (i32.sub (local.get $i) (i32.const 1)))
        (br $shift)))
    (i32.store offset=4 (i32.add (local.get $x) (i32.mul (local.get $j) (i32.const 4)))
      (local.get $v))
    (i32.store (local.get $x) (i32.add (i32.load (local.get $x)) (i32.const 1))))
  (func $ba_copy (export "ba_copy") (param $src i32) (param $dst i32) (param $n i32)
    (local $i i32)
    (block $done
      (loop $copy
        (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
        (i32.store offset=4 (i32.add (local.get $dst) (i32.mul (local.get $i) (i32.const 4)))
          (i32.load (i32.add (local.get $src) (i32.mul (local.get $i) (i32.const 4)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $copy)))
    (i32.store (local.get $dst) (local.get $n)))
  (func $alloc_node (export "alloc_node") (result i32)
    (local $n i32) (local $p i32)
    (local.set $n (i32.load (i32.const 8)))
    (if (local.get $n)
      (then
        (local.set $n (i32.sub (local.get $n) (i32.const 1)))
        (i32.store (i32.const 8) (local.get $n))
        (return (i32.load offset=12 (i32.mul (local.get $n) (i32.const 4))))))
    (local.set $p (memory.grow (i32.const 1)))
    (if (i32.ge_u (local.get $p) (i32.const 32768))
      (then (return (i32.const -1))))
    (local.get $p))
  (func $split_child (export "split_child") (param $x i32) (param $i i32) (param $z i32)
    (local $t i32) (local $xp i32) (local $yp i32) (local $zp i32)
    (local.set $t (i32.load (i32.const 0)))
    (local.set $xp (i32.mul (local.get $x) (i32.const 65536)))
    (local.set $yp (i32.mul
      (call $oba_get (i32.add (local.get $xp) (i32.const 32768)) (local.get $i))
      (i32.const 65536)))
    (local.set $zp (i32.mul (local.get $z) (i32.const 65536)))
    (i32.store (local.get $zp) (i32.load (local.get $yp)))
    (call $ba_copy
      (i32.add (i32.add (local.get $yp) (i32.const 8)) (i32.mul (local.get $t) (i32.const 4)))
      (i32.add (local.get $zp) (i32.const 4))
      (i32.sub (local.get $t) (i32.const 1)))
    (if (i32.eqz (i32.load (local.get $yp)))
      (then
        (call $ba_copy
          (i32.add (i32.add (local.get $yp) (i32.const 32772)) (i32.mul (local.get $t) (i32.const 4)))
          (i32.add (local.get $zp) (i32.const 32768))
          (local.get $t))
        (i32.store offset=32768 (local.get $yp) (local.get $t))))
    (call $ba_insert (i32.add (local.get $xp) (i32.const 4)) (local.get $i)
      (call $oba_get (i32.add (local.get $yp) (i32.const 4)) (i32.sub (local.get $t) (i32.const 1))))
    (i32.store offset=4 (local.get $yp) (i32.sub (local.get $t) (i32.const 1)))
    (call $ba_insert (i32.add (local.get $xp) (i32.const 32768))
      (i32.add (local.get $i) (i32.const 1)) (local.get $z)))
  (func $insert_nonfull (export "insert_nonfull") (param $x i32) (param $k i32) (result i32)
    (local $xp i32) (local $i i32) (local $c i32) (local $z i32)
    (local.set $xp (i32.mul (local.get $x) (i32.const 65536)))
    (local.set $i (call $oba_find (i32.add (local.get $xp) (i32.const 4)) (local.get $k)))
    (if (i32.load (local.get $xp))
      (then
        (call $ba_insert (i32.add (local.get $xp) (i32.const 4)) (local.get $i) (local.get $k))
        (return (i32.const 1))))
    (local.set $c (call $oba_get (i32.add (local.get $xp) (i32.const 32768)) (local.get $i)))
    (if (i32.eq (i32.load offset=4 (i32.mul (local.get $c) (i32.const 65536)))
          (i32.sub (i32.mul (i32.load (i32.const 0)) (i32.const 2)) (i32.const 1)))
      (then
        (local.set $z (call $alloc_node))
        (if (i32.eq (local.get $z) (i32.const -1))
          (then (return (i32.const 0))))
        (call $split_child (local.get $x) (local.get $i) (local.get $z))
        (if (i32.gt_s (local.get $k)
              (call $oba_get (i32.add (local.get $xp) (i32.const 4)) (local.get $i)))
          (then (local.set $c (local.get $z))))))
    (call $insert_nonfull (local.get $c) (local.get $k)))
  (func $btree_create (export "btree_create") (param $t i32) (result i32)
    (if (i32.eq (memory.grow (i32.const 2)) (i32.const -1))
      (then (return (i32.const 0))))
    (i32.store (i32.const 0) (local.get $t))
    (i32.store (i32.const 4) (i32.const 1))
    (i32.store (i32.const 8) (i32.const 0))
    (i32.store (i32.const 65536) (i32.const 1))
    (i32.store (i32.const 65540) (i32.const 0))
    (i32.const 1))
  (func $btree_insert (export "btree_insert") (param $k i32) (result i32)
    (local $r i32) (local $s i32) (local $z i32)
    (if (call $btree_search (local.get $k))
      (then (return (i32.const 1))))
    (local.set $r (i32.load (i32.const 4)))
    (if (i32.eq (i32.load offset=4 (i32.mul (local.get $r) (i32.const 65536)))
          (i32.sub (i32.mul (i32.load (i32.const 0)) (i32.const 2)) (i32.const 1)))
      (then
        (local.set $s (call $alloc_node))
        (if (i32.eq (local.get $s) (i32.const -1))
          (then (return (i32.const 0))))
        (local.set $z (call $alloc_node))
        (if (i32.eq (local.get $z) (i32.const -1))
          (then (return (i32.const 0))))
        (i32.store (i32.mul (local.get $s) (i32.const 65536)) (i32.const 0))
        (i32.store offset=4 (i32.mul (local.get $s) (i32.const 65536)) (i32.const 0))
        (i32.store offset=32768 (i32.mul (local.get $s) (i32.const 65536)) (i32.const 1))
        (i32.store offset=32772 (i32.mul (local.get $s) (i32.const 65536)) (local.get $r))
        (call $split_child (local.get $s) (i32.const 0) (local.get $z))
        (i32.store (i32.const 4) (local.get $s))
        (local.set $r (local.get $s))))
    (call $insert_nonfull (local.get $r) (local.get $k))))
"#

/-- The store after instantiating the module against no imports. -/
def store₀ : Store Nat :=
  match instantiateOnce? ({} : Store Nat) program [] with
  | some (s, _, _) => s
  | none => {}

/-- `oba_get`. -/
def getFunc : Func := program.funcs[0]
/-- `oba_find`. -/
def findFunc : Func := program.funcs[1]
/-- `btree_search`. -/
def searchFunc : Func := program.funcs[2]
/-- `ba_insert`. -/
def baInsertFunc : Func := program.funcs[3]
/-- `ba_copy`. -/
def baCopyFunc : Func := program.funcs[4]
/-- `alloc_node`. -/
def allocFunc : Func := program.funcs[5]
/-- `split_child`. -/
def splitFunc : Func := program.funcs[6]
/-- `insert_nonfull`. -/
def insertNonfullFunc : Func := program.funcs[7]
/-- `btree_create`. -/
def createFunc : Func := program.funcs[8]
/-- `btree_insert`. -/
def insertFunc : Func := program.funcs[9]

/-! ## Ordered, bounded arrays (as in version 1) -/

/-- `INT32_MAX`. -/
abbrev int32Max : Nat := 2 ^ 31 - 1

/-- **A bounded array** at `x` of capacity `n` holding `α`. -/
def BA (B : ByteArray) (x n : Nat) (α : List (BitVec 32)) : Prop :=
  wd B x = BitVec.ofNat 32 α.length ∧ words B (x + 4) α.length = α ∧ α.length ≤ n ∧
    x + 4 + 4 * n ≤ int32Max ∧ x + 4 + 4 * n ≤ B.size

/-- **An ordered, bounded array** (the paper's `OBA(x, n, α)`). -/
def OBA (B : ByteArray) (x n : Nat) (α : List (BitVec 32)) : Prop := BA B x n α ∧ SortedS α

/-- An ordered, bounded array without duplicates (`OBA_nd`). -/
def OBAnd (B : ByteArray) (x n : Nat) (α : List (BitVec 32)) : Prop := OBA B x n α ∧ α.Nodup

/-! ## B-trees -/

/-- The bytes per page. -/
abbrev page : Nat := 65536

/-- Abstract B-tree nodes: the page, the leaf flag, the keys and the children. -/
inductive Tree where
  | node (x : Nat) (leaf : Bool) (keys : List (BitVec 32)) (children : List Tree)

/-- The page of the root node. -/
def Tree.page : Tree → Nat
  | .node x _ _ _ => x

/-- The page of the root node as an `i32` (a child pointer). -/
def Tree.ptr (T : Tree) : BitVec 32 := BitVec.ofNat 32 T.page

/-- **The tree `T` is in memory** (the paper's `Node` and `BTreeRec`): at each node's page,
the leaf indicator, the keys as an `OBAnd`, and for an inner node the children's pages as a
`BA`, each child in memory. -/
inductive Repr (B : ByteArray) : Tree → Prop where
  | leaf {x : Nat} {ks : List (BitVec 32)} (hl : wd B (page * x) ≠ 0)
      (hk : OBAnd B (page * x + 4) 8090 ks) : Repr B (.node x true ks [])
  | inner {x : Nat} {ks : List (BitVec 32)} {cs : List Tree} (hl : wd B (page * x) = 0)
      (hk : OBAnd B (page * x + 4) 8090 ks) (hp : BA B (page * x + 32768) 8091 (cs.map Tree.ptr))
      (hc : ∀ c ∈ cs, Repr B c) : Repr B (.node x false ks cs)

/-- `k` is a key of the tree. -/
inductive InTree (k : BitVec 32) : Tree → Prop where
  | here {x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree} (h : k ∈ ks) :
      InTree k (.node x l ks cs)
  | child {x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree} {c : Tree}
      (hc : c ∈ cs) (h : InTree k c) : InTree k (.node x l ks cs)

/-- Page `p` is a node of the tree. -/
inductive Owns (p : Nat) : Tree → Prop where
  | here {l : Bool} {ks : List (BitVec 32)} {cs : List Tree} : Owns p (.node p l ks cs)
  | child {x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree} {c : Tree}
      (hc : c ∈ cs) (h : Owns p c) : Owns p (.node x l ks cs)

/-- **No page is used twice**: a node's page is not in its subtrees, and distinct children
own disjoint pages. -/
inductive Distinct : Tree → Prop where
  | node {x : Nat} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree}
      (hx : ∀ c ∈ cs, ¬ Owns x c)
      (hd : cs.Pairwise fun c c' => ∀ p, Owns p c → ¬ Owns p c')
      (hc : ∀ c ∈ cs, Distinct c) : Distinct (.node x l ks cs)

/-- `lo < x < hi`, for optional (signed) bounds. -/
def Within (lo hi : Option (BitVec 32)) (x : BitVec 32) : Prop :=
  (∀ l, lo = some l → l.toInt < x.toInt) ∧ (∀ h, hi = some h → x.toInt < h.toInt)

/-- **Search-tree order**: the keys are strictly increasing and within `(lo, hi)`; a leaf has
no children and an inner node one child more than keys, child `i` lying between keys `i - 1`
and `i`. -/
inductive Ordered : Option (BitVec 32) → Option (BitVec 32) → Tree → Prop where
  | mk {lo hi : Option (BitVec 32)} {x : Nat} {l : Bool} {ks : List (BitVec 32)}
      {cs : List Tree} (hs : ks.Pairwise fun a b => a.toInt < b.toInt)
      (hw : ∀ k ∈ ks, Within lo hi k) (hlen : cs.length = if l then 0 else ks.length + 1)
      (hc : ∀ i (h : i < cs.length), Ordered (if i = 0 then lo else ks[i - 1]?)
        (if i = ks.length then hi else ks[i]?) cs[i]) :
      Ordered lo hi (.node x l ks cs)

/-- **Balance** with branching factor `t`: every leaf at depth `d` below this node, and
`t - 1 ≤ |keys| ≤ 2 t - 1` for every node except the root (`root`), which has at most
`2 t - 1` keys. -/
inductive Balanced (t : Nat) : Bool → Nat → Tree → Prop where
  | leaf {root : Bool} {x : Nat} {ks : List (BitVec 32)}
      (hk : (root ∨ t - 1 ≤ ks.length) ∧ ks.length ≤ 2 * t - 1) :
      Balanced t root 0 (.node x true ks [])
  | inner {root : Bool} {d x : Nat} {ks : List (BitVec 32)} {cs : List Tree}
      (hk : (root ∨ t - 1 ≤ ks.length) ∧ ks.length ≤ 2 * t - 1)
      (hc : ∀ c ∈ cs, Balanced t false d c) : Balanced t root (d + 1) (.node x false ks cs)

/-- Page `p` can hold a node: not the metadata page, below `32768` (so that its arrays stay
below `INT32_MAX`) and inside memory (the paper's `Page(p)`). -/
def PageOK (B : ByteArray) (p : Nat) : Prop := 1 ≤ p ∧ p < 32768 ∧ page * (p + 1) ≤ B.size

/-- **The metadata page and the tree** (the paper's `Meta(t, r, μ, φ) * BTreeRec(r, κ, …)`):
`t` at `0`, the root's page at `4`, the free pages `φ` at `8` (`Free(φ)`); `T` in memory,
ordered and balanced, its pages distinct, valid and disjoint from the free pages, which are
valid too; the memory a whole number of pages; `2 ≤ t ≤ 4045`. -/
def BTreeAt (B : ByteArray) (t : Nat) (T : Tree) (φ : List (BitVec 32)) : Prop :=
  2 ≤ t ∧ t ≤ 4045 ∧ B.size % page = 0 ∧ wd B 0 = BitVec.ofNat 32 t ∧ wd B 4 = T.ptr ∧
    Repr B T ∧ Ordered none none T ∧ (∃ d, Balanced t true d T) ∧ Distinct T ∧
    (∀ p, Owns p T → PageOK B p) ∧ OBAnd B 8 16381 φ ∧
    (∀ q ∈ φ, PageOK B q.toNat ∧ ¬ Owns q.toNat T)

/-- **`BTree(t, κ)`** (paper §4.2): a B-tree with branching factor `t` and key set `κ`. -/
def IsBTree (B : ByteArray) (t : Nat) (κ : BitVec 32 → Prop) : Prop :=
  ∃ T φ, BTreeAt B t T φ ∧ ∀ k, InTree k T ↔ κ k

/-- The pages a B-tree owns: the metadata page, its nodes and its free pages. -/
def Owned (T : Tree) (φ : List (BitVec 32)) (p : Nat) : Prop :=
  p = 0 ∨ Owns p T ∨ ∃ q ∈ φ, q.toNat = p

/-- **The memory frame**: `B'` is at least as large as `B` and has the bytes of `B` on every
page outside `S`. -/
def Unchanged (B B' : ByteArray) (S : Nat → Prop) : Prop :=
  B.size ≤ B'.size ∧ ∀ i, i < B.size → ¬ S (i / page) → B'.data.toList[i]? = B.data.toList[i]?

/-! ## Linking -/

variable {H : Type}

/-- The parameter and result counts of the module's functions, by index. -/
def arity : Nat → Nat × Nat
  | 0 => (2, 1) | 1 => (2, 1) | 2 => (1, 1) | 3 => (3, 0) | 4 => (3, 0) | 5 => (0, 1)
  | 6 => (3, 0) | 7 => (2, 1) | 8 => (1, 1) | _ => (1, 1)

open Silmaril.Wasm.Numerics Silmaril.Wasm.Validation in
/-- The function instance `fi` has a function type with `n` parameters and `m` results. -/
def HasArity (fi : FuncInst H) (n m : Nat) : Prop :=
  ∃ ps rs : Ty (.list .val), Expand fi.type (.func ps rs) ∧ ps.length = n ∧ rs.length = m

/-- **The calls of `mi` resolve to the module's functions**: function index `j < 10` of `mi`
is an address holding an instance of `mi` running `program.funcs[j]`, of its arity. -/
def Resolved (s : Store H) (mi : ModuleInst) : Prop :=
  ∀ j, j < 10 → ∃ (a : Nat) (fi : FuncInst H), mi.funcs[j]? = some a ∧ s.funcs[a]? = some fi ∧
    fi.module = mi ∧ (∃ code, program.funcs[j]? = some code ∧ fi.code = .wasm code) ∧
    HasArity fi (arity j).1 (arity j).2

/-! ## Specifications -/

/-- **`OBAGet`** (Figure 12) on a bounded array (ordered or not): the store is unchanged and
the call returns `α!k`. -/
def getSpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ ∃ (x k : BitVec 32) (ma : Nat) (mt : MemoryType)
    (B : ByteArray) (n : Nat) (α : List (BitVec 32)), args = [.i32 x, .i32 k] ∧
    MemAt s fi.module ma mt B ∧ BA B x.toNat n α ∧ k.toNat < α.length
  post s args s' o := s' = s ∧ ∀ (x k : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (n : Nat) (α : List (BitVec 32)), args = [.i32 x, .i32 k] → MemAt s fi.module ma mt B →
    BA B x.toNat n α → k.toNat < α.length → o = .normal [.i32 (α.getD k.toNat 0)]

/-- What `OBAFind` returns (Figure 13): the first index `i ≤ |α|` with every element before it
below `e` and every element from it on at least `e`. -/
def FindsAt (α : List (BitVec 32)) (e : BitVec 32) (i : Nat) : Prop :=
  i ≤ α.length ∧ (∀ j < i, (α.getD j 0).toInt < e.toInt) ∧
    (∀ j, i ≤ j → j < α.length → e.toInt ≤ (α.getD j 0).toInt)

/-- **`OBAFind`** (Figure 13). -/
def findSpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ ∃ (x e : BitVec 32) (ma : Nat) (mt : MemoryType)
    (B : ByteArray) (n : Nat) (α : List (BitVec 32)), args = [.i32 x, .i32 e] ∧
    MemAt s fi.module ma mt B ∧ OBA B x.toNat n α
  post s args s' o := s' = s ∧ ∀ (x e : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (n : Nat) (α : List (BitVec 32)), args = [.i32 x, .i32 e] → MemAt s fi.module ma mt B →
    OBA B x.toNat n α → ∃ i, FindsAt α e i ∧ o = .normal [.i32 (BitVec.ofNat 32 i)]

/-- **`BTreeSearch`** (Figure 14): `{[k] | BTree(t, κ)} btree_search {∃ b. [b] | BTree(t, κ) ∧
(k ∈ κ ⇒ b = 1) ∧ (k ∉ κ ⇒ b = 0)}`; here the store is unchanged. -/
def searchSpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ Resolved s fi.module ∧ ∃ (k : BitVec 32) (ma : Nat)
    (mt : MemoryType) (B : ByteArray) (t : Nat) (κ : BitVec 32 → Prop), args = [.i32 k] ∧
    MemAt s fi.module ma mt B ∧ IsBTree B t κ
  post s args s' o := s' = s ∧ ∀ (k : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (t : Nat) (κ : BitVec 32 → Prop), args = [.i32 k] → MemAt s fi.module ma mt B →
    IsBTree B t κ → ∃ b : BitVec 32, o = .normal [.i32 b] ∧ (κ k → b = 1) ∧ (¬ κ k → b = 0)

/-- **`BTreeInsert`** (Figure 14), with an out-of-memory outcome: `{[k] | BTree(t, κ)}
btree_insert {∃ b. [b] | (b = 1 ∧ BTree(t, κ ∪ {k})) ∨ (b = 0 ∧ BTree(t, κ))}`; only memory
`0` changes, and on every page outside the metadata page, the old tree's nodes and the old
free pages its bytes are unchanged. The memory has address type `i32` (a 64-bit memory's page
numbers would not fit the `i32` that `memory.grow` returns). -/
def insertSpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ Resolved s fi.module ∧ ∃ (k : BitVec 32) (ma : Nat)
    (mt : MemoryType) (B : ByteArray) (t : Nat) (κ : BitVec 32 → Prop), args = [.i32 k] ∧
    MemAt s fi.module ma mt B ∧ mt.address = .i32 ∧ IsBTree B t κ
  post s args s' o := ∀ (k : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray) (t : Nat)
    (T : Tree) (φ : List (BitVec 32)), args = [.i32 k] → MemAt s fi.module ma mt B →
    mt.address = .i32 → BTreeAt B t T φ → ∃ (b : BitVec 32) (mt' : MemoryType) (B' : ByteArray),
      o = .normal [.i32 b] ∧ s' = s.setMem ma ⟨mt', B'⟩ ∧ mt'.address = .i32 ∧
      Unchanged B B' (Owned T φ) ∧
      ((b = 1 ∧ IsBTree B' t fun k' => InTree k' T ∨ k' = k) ∨ (b = 0 ∧ IsBTree B' t fun k' => InTree k' T))

/-- **`BTreeCreate`** (Figure 14), with an out-of-memory outcome: `{[t] | size(0) ∧ 2 ≤ t ≤ 4045}
btree_create {∃ b. [b] | (b = 1 ∧ BTree(t, ∅)) ∨ (b = 0 ∧ size(0))}`; only memory `0` changes. -/
def createSpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ ∃ (t : BitVec 32) (ma : Nat) (mt : MemoryType)
    (B : ByteArray), args = [.i32 t] ∧ MemAt s fi.module ma mt B ∧ mt.address = .i32 ∧
    B.size = 0 ∧ 2 ≤ t.toNat ∧ t.toNat ≤ 4045
  post s args s' o := ∀ (t : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray),
    args = [.i32 t] → MemAt s fi.module ma mt B → mt.address = .i32 → B.size = 0 →
    ∃ (b : BitVec 32) (mt' : MemoryType) (B' : ByteArray), o = .normal [.i32 b] ∧
      s' = s.setMem ma ⟨mt', B'⟩ ∧ mt'.address = .i32 ∧
      ((b = 1 ∧ IsBTree B' t.toNat fun _ => False) ∨ (b = 0 ∧ B'.size = 0))

open Silmaril.Wasm.Numerics in
/-- **Specification of `oba_get` and `oba_find`**: every instance running them meets
`getSpec`/`findSpec` for total correctness, at every profile and host relation. -/
def OBASpec : Prop :=
  ∀ {H : Type} (P : Profile) (host : HostSemantics H) (a : Nat) (fi : FuncInst H),
    HasArity fi 2 1 →
    (fi.code = .wasm getFunc → Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (getSpec a fi)) ∧
    (fi.code = .wasm findFunc → Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (findSpec a fi))

open Silmaril.Wasm.Numerics in
/-- **Specification of `btree_search`**: every instance running it meets `searchSpec` for
total correctness (its calls resolving to the module's functions, `Resolved`, in the
precondition). -/
def SearchSpec : Prop :=
  ∀ {H : Type} (P : Profile) (host : HostSemantics H) (a : Nat) (fi : FuncInst H),
    fi.code = .wasm searchFunc → HasArity fi 1 1 →
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (searchSpec a fi)

open Silmaril.Wasm.Numerics in
/-- **Specification of `btree_insert` and `btree_create`**: every instance running them meets
`insertSpec`/`createSpec` for total correctness. -/
def InsertCreateSpec : Prop :=
  ∀ {H : Type} (P : Profile) (host : HostSemantics H) (a : Nat) (fi : FuncInst H),
    HasArity fi 1 1 →
    (fi.code = .wasm insertFunc → Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (insertSpec a fi)) ∧
    (fi.code = .wasm createFunc → Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (createSpec a fi))

end Silmaril.WasmSpec.BTree.V2
