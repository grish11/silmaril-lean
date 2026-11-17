module

public import Silmaril.Wasm.Component.Reference.ListLift.Defs
public import Silmaril.Wasm.Logic.Words.Defs

/-!
# Lowered lists in the memory of a bump allocator: definitions

`LParams` (`Silmaril.Wasm.Component.Reference.ListLift`) relates the store before a call to the
store and flat arguments after the canonical ABI's lowering of list arguments: each list is
stored through allocator calls and little-endian writes. It quantifies over the allocator's
runs and says nothing about the final memory. This file states what the final memory holds
when the allocator is a **bump allocator**: every block it answers lies at or above its heap
pointer, and the heap pointer moves past it.

* `BumpAlloc P ra ma N Inv`: the hypothesis on the allocator. `Inv s t` is a store invariant
  with heap pointer `t`; memory `ma` has `N < 2³²` bytes under it, writes to memory `ma` keep
  it, and an allocator run (`ReallocRun`, at any alignment) from heap pointer `t` leaves memory
  `ma` unchanged and answers a block `q ≥ t` whose end is below the new heap pointer `t'`
  whenever the block lies in memory (the canonical ABI's bounds check rejects the other
  blocks);
* `Holds B lo hi t v p`: the bytes `B` hold the value `v` of type `t` at byte `p`, with every
  block it points to in `[lo, hi)` and in `B`: an `s32` or `u32` is its word (`wd`), an `s64`
  its 64-bit word (`wd64`), a list its `(ptr, len)` pair at `p`, with its elements (`HoldsL`) at
  `ptr, ptr + size, …`, a tuple or record its fields at their aligned offsets from `p`
  (`HoldsF`);
* `FlatHolds B lo hi ts vs fl`: the flat arguments `fl` of the parameters `vs` of types `ts`:
  an `s32` is its `i32`, a list the `i32` pair `(q, len)` of a block in `[lo, hi)` holding the
  elements.

The result (`Silmaril.Wasm.Component.Reference.ListLift.Bump.Thms`) is that `LParams` from a
store with heap pointer `t` ends in a store with a heap pointer `t' ≥ t` whose memory is the
old one outside `[t, t')` and holds the arguments (`FlatHolds … t t'`): blocks of later
arguments and of inner lists never overwrite earlier ones, because each is allocated above the
heap pointer and the `(ptr, len)` pairs are written inside their parent's block, below it.

`LVal.ofWords` and `LVal.ofNested` are the values of `list<s32>` and `list<list<s32>>` from
lists of words.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference.ListLift

open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Logic.Words (wd)
open Silmaril.Wasm.Numerics (Profile)

/-- The bytes of memory `ma` (empty if there is none). -/
def memBytesOf (s : Store Nat) (ma : Nat) : ByteArray :=
  ((s.mems[ma]?).map (·.bytes)).getD .empty

/-- **A bump allocator** at function address `ra` for memory `ma` of `N` bytes, with the store
invariant `Inv s t` (heap pointer `t`). -/
structure BumpAlloc (P : Profile) (ra ma N : Nat) (Inv : Store Nat → Nat → Prop) : Prop where
  /-- The memory is 32-bit addressable. -/
  small : N < 2 ^ 32
  /-- Memory `ma` has `N` bytes. -/
  size : ∀ {s t}, Inv s t → (memBytesOf s ma).size = N
  /-- Writes to memory `ma` keep the invariant and the heap pointer. -/
  write : ∀ {s t p bs s'}, Inv s t →
    Silmaril.Wasm.SingleThreaded.memWrite? s ma p bs = some s' → Inv s' t
  /-- An allocation from heap pointer `t`, at any alignment, leaves the memory unchanged and
  answers a block at or above `t`, below the new heap pointer when it lies in memory. -/
  realloc : ∀ {s t al n q s'}, Inv s t → ReallocRun P ra s al n q s' →
    ∃ t', Inv s' t' ∧ memBytesOf s' ma = memBytesOf s ma ∧ t ≤ q ∧ (q + n ≤ N → q + n ≤ t')

/-- The little-endian 64-bit word at byte `a` (`0` out of bounds). -/
def wd64 (B : ByteArray) (a : Nat) : BitVec 64 :=
  (Silmaril.Wasm.Execution.Memory.load B a 8).getD 0

mutual
/-- The bytes `B` hold the value `v` of type `t` at byte `p`, the blocks it points to lying in
`[lo, hi)` and in `B`. -/
def Holds (B : ByteArray) (lo hi : Nat) : LTy → LVal → Nat → Prop
  | .s32, .s32 x, p => p + 4 ≤ B.size ∧ wd B p = x
  | .u32, .u32 x, p => p + 4 ≤ B.size ∧ wd B p = x
  | .s64, .s64 x, p => p + 8 ≤ B.size ∧ wd64 B p = x
  | .list t, .list vs, p => p + 8 ≤ B.size ∧ (wd B (p + 4)).toNat = vs.length ∧
      lo ≤ (wd B p).toNat ∧ (wd B p).toNat + vs.length * t.size ≤ hi ∧
      (wd B p).toNat + vs.length * t.size ≤ B.size ∧ HoldsL B lo hi t vs (wd B p).toNat
  | .tuple t ts, .fields vs, p => HoldsF B lo hi (t :: ts) vs p 0
  | .record _ _ t fs, .fields vs, p => HoldsF B lo hi (t :: fs.map (·.2)) vs p 0
  | _, _, _ => False

/-- The bytes `B` hold the values `vs` of type `t` at `p`, `p + size`, …. -/
def HoldsL (B : ByteArray) (lo hi : Nat) (t : LTy) : List LVal → Nat → Prop
  | [], _ => True
  | v :: vs, p => Holds B lo hi t v p ∧ HoldsL B lo hi t vs (p + t.size)

/-- The bytes `B` hold the fields `vs` of types `ts` of a tuple or record at byte `p`, from the
offset `c` on: each at the offset rounded up to its type's alignment (`ABI.alignTo`), the offset
then moving past it. -/
def HoldsF (B : ByteArray) (lo hi : Nat) : List LTy → List LVal → Nat → Nat → Prop
  | [], [], _, _ => True
  | t :: ts, v :: vs, p, c =>
    Holds B lo hi t v (p + Silmaril.Wasm.Component.ABI.alignTo c t.align) ∧
      HoldsF B lo hi ts vs p (Silmaril.Wasm.Component.ABI.alignTo c t.align + t.size)
  | _, _, _, _ => False
end

/-- The flat arguments `fl` of the parameters `vs` of types `ts` with the bytes `B`: an `s32` is
its `i32`; a list is the `i32` pair `(q, len)` of a block `[q, q + len · size)` in `[lo, hi)` and
in `B` that holds its elements. -/
def FlatHolds (B : ByteArray) (lo hi : Nat) :
    List LTy → List LVal → List Silmaril.Wasm.Execution.Core.Val → Prop
  | [], [], fl => fl = []
  | .s32 :: ts, .s32 x :: vs, fl => ∃ fl', fl = .i32 x :: fl' ∧ FlatHolds B lo hi ts vs fl'
  | .list t :: ts, .list us :: vs, fl => ∃ q fl',
      fl = .i32 (BitVec.ofNat 32 q) :: .i32 (BitVec.ofNat 32 us.length) :: fl' ∧
      q < 2 ^ 32 ∧ us.length < 2 ^ 32 ∧ lo ≤ q ∧ q + us.length * t.size ≤ hi ∧
      q + us.length * t.size ≤ B.size ∧ HoldsL B lo hi t us q ∧ FlatHolds B lo hi ts vs fl'
  | _, _, _ => False

/-- The `list<s32>` value of a list of words. -/
def LVal.ofWords (xs : List (BitVec 32)) : LVal := .list (xs.map .s32)

/-- The `list<list<s32>>` value of a list of lists of words. -/
def LVal.ofNested (p : List (List (BitVec 32))) : LVal := .list (p.map LVal.ofWords)

end Silmaril.Wasm.Component.Reference.ListLift
