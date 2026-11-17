module

public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Defs
import Silmaril.Proofs.Wasm.Component.Reference.ListLift.Bump

/-!
# Lowered lists in the memory of a bump allocator: results

* **`params_holds`**: with a bump allocator (`BumpAlloc`), the lowering `LParams` of list
  arguments from a store with heap pointer `t₀` ends in a store with heap pointer `t₁ ≥ t₀`
  whose memory is the old one outside `[t₀, t₁)` and holds the arguments (`FlatHolds … t₀ t₁`):
  each list is the `i32` pair `(q, len)` of a block in `[t₀, t₁)` holding its elements, inner
  lists, tuples and records recursively (`Holds`). Later allocations and writes never overwrite
  earlier blocks. The allocator is asked for each element type's alignment (`BumpAlloc.realloc`
  holds at every alignment).
* **`holdsL_words`**: the elements of a `list<s32>` are the words of its block.

Proofs in `Silmaril.Proofs.Wasm.Component.Reference.ListLift.Bump`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference.ListLift

open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Logic.Words (words SameOutside)
open Silmaril.Wasm.Numerics (Profile)

/-- **The lowered arguments are in memory** (bump allocator). -/
theorem params_holds {P : Profile} {ra ma N : Nat} {Inv : Store Nat → Nat → Prop}
    (hb : BumpAlloc P ra ma N Inv) {ts : List LTy} {vs : List LVal} {s : Store Nat}
    {fl : List Silmaril.Wasm.Execution.Core.Val} {s' : Store Nat} {t₀ : Nat}
    (h : LParams P ra ma ts vs s fl s') (hi : Inv s t₀) :
    ∃ t₁, Inv s' t₁ ∧ t₀ ≤ t₁ ∧
      SameOutside (memBytesOf s ma) (memBytesOf s' ma) t₀ (t₁ - t₀) ∧
      FlatHolds (memBytesOf s' ma) t₀ t₁ ts vs fl :=
  Silmaril.Proofs.Wasm.Component.Reference.ListLift.Bump.params_holds hb h hi

/-- **The elements of a `list<s32>` are the words of its block.** -/
theorem holdsL_words {B : ByteArray} {lo hi : Nat} (xs : List (BitVec 32)) (q : Nat)
    (h : HoldsL B lo hi .s32 (xs.map .s32) q) : words B q xs.length = xs :=
  Silmaril.Proofs.Wasm.Component.Reference.ListLift.Bump.holdsL_words xs q h

end Silmaril.Wasm.Component.Reference.ListLift
