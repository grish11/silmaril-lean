module

public import Silmaril.Proofs.WasmSpec.BTree.V2.Calls

/-!
# The B-tree library, version 2: specifications of the helper functions

The internal functions of `btree_insert` (not part of the entry's statements): `ba_insert`,
`ba_copy` and `split_child`, as every-run total specifications (`alloc_node`'s is
`allocSpecI32`, in `Silmaril.Proofs.WasmSpec.BTree.V2.Alloc`) over the `i32`
view, and the abstract node split (`Tree.splitChild`) that `split_child` performs in memory.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Hoare (FSpec)

variable {H : Type}

/-! ## Abstract trees -/

/-- The keys of the root node. -/
def Tree.keys : Tree → List (BitVec 32)
  | .node _ _ ks _ => ks

/-- The children of the root node. -/
def Tree.children : Tree → List Tree
  | .node _ _ _ cs => cs

/-- The leaf flag of the root node. -/
def Tree.leaf : Tree → Bool
  | .node _ l _ _ => l

/-- **Splitting the full child `i`** (CLRS `B-TREE-SPLIT-CHILD`) of a node with branching
factor `t`, the right half going to page `z`: the child keeps its first `t - 1` keys and `t`
children, the new node at `z` gets the last `t - 1` keys and `t` children, and the median key
`t - 1` moves up to index `i` of the node, with `z` as child `i + 1`. -/
def Tree.splitChild (t z : Nat) (T : Tree) (i : Nat) : Tree :=
  match T with
  | .node x l kx cs =>
    match cs[i]? with
    | some (.node y ly ky cy) =>
      .node x l (kx.insertIdx i (ky.getD (t - 1) 0))
        ((cs.set i (.node y ly (ky.take (t - 1)) (cy.take t))).insertIdx (i + 1)
          (.node z ly (ky.drop t) (cy.drop t)))
    | none => .node x l kx cs

/-! ## Helper specifications -/

/-- **`ba_insert(x, j, v)`**: in a bounded array `α` at `x` with room for one more element,
insert `v` at index `j ≤ |α|`; only the array's cells change. -/
def baInsertSpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ ∃ (x j v : BitVec 32) (ma : Nat) (mt : MemoryType)
    (B : ByteArray) (n : Nat) (α : List (BitVec 32)), args = [.i32 x, .i32 j, .i32 v] ∧
    MemAt s fi.module ma mt B ∧ BA B x.toNat n α ∧ j.toNat ≤ α.length ∧ α.length < n
  post s args s' o := ∀ (x j v : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (n : Nat) (α : List (BitVec 32)), args = [.i32 x, .i32 j, .i32 v] →
    MemAt s fi.module ma mt B → BA B x.toNat n α → j.toNat ≤ α.length → α.length < n →
    o = .normal [] ∧ ∃ B' : ByteArray, s' = s.setMem ma ⟨mt, B'⟩ ∧
      BA B' x.toNat n (α.insertIdx j.toNat v) ∧ SameOutside B B' x.toNat (4 + 4 * n)

/-- **`ba_copy(src, dst, n)`**: make the bounded array at `dst` (capacity `cap ≥ n`) hold the
`n` words at `src`, the two regions disjoint; only the array's cells change. -/
def baCopySpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ ∃ (src dst n : BitVec 32) (ma : Nat) (mt : MemoryType)
    (B : ByteArray) (cap : Nat), args = [.i32 src, .i32 dst, .i32 n] ∧
    MemAt s fi.module ma mt B ∧ n.toNat ≤ cap ∧ src.toNat + 4 * n.toNat ≤ B.size ∧
    src.toNat + 4 * n.toNat ≤ int32Max ∧ dst.toNat + 4 + 4 * cap ≤ B.size ∧
    dst.toNat + 4 + 4 * cap ≤ int32Max ∧
    (src.toNat + 4 * n.toNat ≤ dst.toNat ∨ dst.toNat + 4 + 4 * cap ≤ src.toNat)
  post s args s' o := ∀ (src dst n : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (cap : Nat), args = [.i32 src, .i32 dst, .i32 n] → MemAt s fi.module ma mt B →
    n.toNat ≤ cap → src.toNat + 4 * n.toNat ≤ B.size → src.toNat + 4 * n.toNat ≤ int32Max →
    dst.toNat + 4 + 4 * cap ≤ B.size → dst.toNat + 4 + 4 * cap ≤ int32Max →
    (src.toNat + 4 * n.toNat ≤ dst.toNat ∨ dst.toNat + 4 + 4 * cap ≤ src.toNat) →
    o = .normal [] ∧ ∃ B' : ByteArray, s' = s.setMem ma ⟨mt, B'⟩ ∧
      BA B' dst.toNat cap (words B src.toNat n.toNat) ∧ SameOutside B B' dst.toNat (4 + 4 * cap)

/-- What `alloc_node` leaves: the memory `B'` (a whole number of pages, at least as large as
`B`, with the bytes of `B` outside the free list's cells `[8, 65536)`), the free list `φ'` (a
sublist of `φ`, its pages valid in `B'`), and the result `r`: `-1`, or a valid page of `B'`
not in `φ'` that was either a free page or beyond the old memory. -/
def AllocPost (B : ByteArray) (φ : List (BitVec 32)) (r : BitVec 32) (B' : ByteArray)
    (φ' : List (BitVec 32)) : Prop :=
  B'.size % page = 0 ∧ B.size ≤ B'.size ∧ OBAnd B' 8 16381 φ' ∧ φ'.Sublist φ ∧
    (∀ i, i < B.size → (i < 8 ∨ 65536 ≤ i) → B'.data.toList[i]? = B.data.toList[i]?) ∧
    (∀ q ∈ φ', PageOK B' q.toNat) ∧
    (r = -1 ∨ (PageOK B' r.toNat ∧ r ∉ φ' ∧ (r ∈ φ ∨ B.size ≤ page * r.toNat)))

/-- The precondition of `split_child(x, i, z)` on the memory `B`: `t` at `0`; the inner node
`X` at page `x` in memory, its pages distinct and valid, with fewer than `2 t - 1` keys; its
child `i` full (`2 t - 1` keys, and `2 t` children if inner); `z` a valid page not in `X`; `X`
ordered within some bounds. -/
def SplitPre (B : ByteArray) (t : Nat) (X : Tree) (i z : Nat) : Prop :=
  2 ≤ t ∧ t ≤ 4045 ∧ wd B 0 = BitVec.ofNat 32 t ∧ X.leaf = false ∧ Repr B X ∧ Distinct X ∧
    (∃ lo hi, Ordered lo hi X) ∧
    (∀ p, Owns p X → PageOK B p) ∧ PageOK B z ∧ ¬ Owns z X ∧ X.keys.length < 2 * t - 1 ∧
    X.children.length = X.keys.length + 1 ∧
    ∃ c : Tree, X.children[i]? = some c ∧ c.keys.length = 2 * t - 1 ∧
      (c.leaf = false → c.children.length = 2 * t)

/-- **`split_child(x, i, z)`**: split the full child `i` of the node at `x` into it and a new
node at `z` (`Tree.splitChild`); only the pages of `x`, of the child and `z` change. -/
def splitSpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ Resolved s fi.module ∧ ∃ (x i z : BitVec 32) (ma : Nat)
    (mt : MemoryType) (B : ByteArray) (t : Nat) (X : Tree), args = [.i32 x, .i32 i, .i32 z] ∧
    MemAt s fi.module ma mt B ∧ X.page = x.toNat ∧ SplitPre B t X i.toNat z.toNat
  post s args s' o := ∀ (x i z : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray) (t : Nat)
    (X : Tree), args = [.i32 x, .i32 i, .i32 z] → MemAt s fi.module ma mt B → X.page = x.toNat →
    SplitPre B t X i.toNat z.toNat → o = .normal [] ∧ ∃ B' : ByteArray,
      s' = s.setMem ma ⟨mt, B'⟩ ∧ B'.size = B.size ∧ Repr B' (X.splitChild t z.toNat i.toNat) ∧
      Unchanged B B' (fun p => p = x.toNat ∨ p = ((X.children.getD i.toNat X).page) ∨
        p = z.toNat)

end Silmaril.WasmSpec.BTree.V2
