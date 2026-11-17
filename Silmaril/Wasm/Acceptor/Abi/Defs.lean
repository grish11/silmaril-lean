module

public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Defs

/-!
# The acceptor kit: reading canonical-ABI arguments back from memory

`ListLift.params_holds` ends the lowering of list arguments with `FlatHolds`: each list is the
`i32` pair `(ptr, len)` of a block holding its elements (`Holds`, `HoldsL`). A checker's core
code reads them back with its own loads; its Core-level theorems are stated with **readers**,
Lean functions of the memory bytes, and **in-bounds predicates** on them. This file gives
generic readers and bounds, the contract tying them to `Holds`, and combinators building the
contract for the types `LTy` the fragment lowers, so that a new checker only composes readers:

* `listAt sz rd B p n`: the `n` values at `p, p + sz, …` read by `rd`;
  `pairAt sz rd B a`: the list whose `(ptr, len)` pair is at byte `a`;
* `ListIn sz inn B p n`: the `n` elements lie in `B`, each meeting `inn`;
  `PairIn sz B a`: the block of the pair at `a` lies in `B`;
* `Reads t enc rd inn`: **the reader contract** of a Lean type `α` encoded at the type `t`
  (`enc : α → LVal`): whenever the bytes hold `enc a` at `p` (`Holds`, any block bounds), `rd`
  reads `a` back at `p` and `inn` holds there. The combinators (`Thms`) are `reads_s32`,
  `reads_u32`, `reads_s64` (scalars, `NoBounds`), `Reads.list` (a `(ptr, len)` pair, its block
  in bounds), `Reads.tuple2`, `Reads.record2` (two fields at their canonical-ABI offsets
  `fieldOff₁`, `fieldOff₂`), `Reads.map` (a type in bijection with a read one) and
  `Reads.mono`; `holdsL_listAt` reads a top-level `list<t>` argument.
* `nestedAt`, `NestedIn`: the reader and bounds of a `list<list<s32>>` argument (an instance:
  `nestedAt_eq`, `nestedIn_iff`), shared by the SAT and LRAT acceptors.

Offsets are computed from `LTy.layout` (`ABI.alignTo`, `LTy.size`), not fixed: a checker's
concrete readers (`p + 16 * i`, `+ 8`) are instances by `rfl`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Acceptor

open Silmaril.Wasm.Component.Reference.ListLift (LTy LVal Holds HoldsL wd64)
open Silmaril.Wasm.Logic.Words (wd words)

/-- The `n` values at `p, p + sz, …`, each read by `rd`. -/
def listAt {α : Type} (sz : Nat) (rd : ByteArray → Nat → α) (B : ByteArray) (p n : Nat) :
    List α :=
  (List.range n).map fun i => rd B (p + sz * i)

/-- The list whose `(ptr, len)` pair is at byte `a`: `len` values of `sz` bytes from `ptr`. -/
def pairAt {α : Type} (sz : Nat) (rd : ByteArray → Nat → α) (B : ByteArray) (a : Nat) : List α :=
  listAt sz rd B (wd B a).toNat (wd B (a + 4)).toNat

/-- The block of the `(ptr, len)` pair at `a`, of `len` elements of `sz` bytes, lies in `B`. -/
def PairIn (sz : Nat) (B : ByteArray) (a : Nat) : Prop :=
  (wd B a).toNat + sz * (wd B (a + 4)).toNat ≤ B.size

/-- The `n` elements of `sz` bytes at `p` lie in `B`, and each meets `inn`. -/
def ListIn (sz : Nat) (inn : ByteArray → Nat → Prop) (B : ByteArray) (p n : Nat) : Prop :=
  p + sz * n ≤ B.size ∧ ∀ i < n, inn B (p + sz * i)

/-- No bounds (a scalar). -/
def NoBounds : ByteArray → Nat → Prop := fun _ _ => True

/-- **The reader contract**: whenever the bytes hold `enc a` of type `t` at `p`, the reader
`rd` reads `a` at `p`, and `inn` holds at `p`. -/
def Reads {α : Type} (t : LTy) (enc : α → LVal) (rd : ByteArray → Nat → α)
    (inn : ByteArray → Nat → Prop) : Prop :=
  ∀ {B : ByteArray} {lo hi : Nat} (a : α) (p : Nat), Holds B lo hi t (enc a) p →
    rd B p = a ∧ inn B p

/-- The offset of the first field of a two-field tuple or record of types `t₁`, `t₂`. -/
def fieldOff₁ (t₁ : LTy) : Nat := Silmaril.Wasm.Component.ABI.alignTo 0 t₁.align

/-- The offset of the second field. -/
def fieldOff₂ (t₁ t₂ : LTy) : Nat :=
  Silmaril.Wasm.Component.ABI.alignTo (fieldOff₁ t₁ + t₁.size) t₂.align

/-- The value of a two-field tuple or record. -/
def enc2 {α β : Type} (e₁ : α → LVal) (e₂ : β → LVal) (c : α × β) : LVal := .fields [e₁ c.1, e₂ c.2]

/-- The reader of a two-field tuple or record of types `t₁`, `t₂`. -/
def read2 {α β : Type} (t₁ t₂ : LTy) (r₁ : ByteArray → Nat → α) (r₂ : ByteArray → Nat → β)
    (B : ByteArray) (p : Nat) : α × β :=
  (r₁ B (p + fieldOff₁ t₁), r₂ B (p + fieldOff₂ t₁ t₂))

/-- The bounds of a two-field tuple or record. -/
def in2 (t₁ t₂ : LTy) (i₁ i₂ : ByteArray → Nat → Prop) (B : ByteArray) (p : Nat) : Prop :=
  i₁ B (p + fieldOff₁ t₁) ∧ i₂ B (p + fieldOff₂ t₁ t₂)

/-- The bounds of a list of elements of type `t` meeting `inn`, at its `(ptr, len)` pair. -/
def listIn (t : LTy) (inn : ByteArray → Nat → Prop) (B : ByteArray) (a : Nat) : Prop :=
  PairIn t.size B a ∧ ∀ i < (wd B (a + 4)).toNat, inn B ((wd B a).toNat + t.size * i)

/-! ## `list<list<s32>>` -/

/-- The nested input of `n` pairs `(ptr, len)` at byte `p`: the words of each pair's block (a
`list<list<s32>>` value). -/
def nestedAt (B : ByteArray) (p n : Nat) : List (List (BitVec 32)) :=
  (List.range n).map fun i => words B (wd B (p + 8 * i)).toNat (wd B (p + 8 * i + 4)).toNat

/-- Every block of the nested input lies in memory. -/
def NestedIn (B : ByteArray) (p n : Nat) : Prop :=
  p + 8 * n ≤ B.size ∧ ∀ i < n, (wd B (p + 8 * i)).toNat + 4 * (wd B (p + 8 * i + 4)).toNat ≤ B.size

end Silmaril.Wasm.Acceptor
