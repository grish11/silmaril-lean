module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Thms
public import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Execution.Core.SpecProfile
import Silmaril.Wasm.Spec.Run.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Replay

/-!
# Chunk exports in instance plays: replayed sessions (non-vacuity)

A session of **four export calls**, `feed(7)`, `feed(8)`, `finish(1)`, `finish(5)`, replayed on the
verified interpreter one after the other, each from the store the previous call left
(`Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.replaySeqR`), with a host returning the
fresh handles `1, 2, …` to the writer calls (`chunkScript`), by kernel evaluation: `feed(7)` calls
`nil() = 1`, `word(7) = 2`, `cons(2, 1) = 3`; `feed(8)` calls `word(8) = 4`, `cons(4, 3) = 5`;
`finish(1)`, with two values buffered, calls `nil() = 6` and answers `(0, 6)`: nothing is
consumed; `finish(5)` answers `(2, 5)`. Simulating the mixed host along the decoded events with
the chunk buffer (`Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.mem_moduleMixedRel_of_replaySeqC`):
the third call relates `([], ())`, the fourth `([7, 8], (8 7))`: the two values stayed buffered
across the `finish` that consumed none of them.

**Profiles and policies.** Every profile `P` admitting the deterministic steps of the interpreter
(hypothesis `hP`; every specification profile `Profile.spec nd {}`, the `_spec` corollary), every
writer policy whose sentinel, if any, is `0`, and every parsing policy with sentinel `0`.

* `chunkStack_relates_78`, `chunkStack_relates_nil`: the two pairs are related;
* `chunkStack_rel_eq_78`: with `chunkStack_sound`, the relation restricted to the input `[7, 8]`
  is exactly `{([7, 8], (8 7))}`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Accept.Handle Silmaril.Accept.Parse
  Silmaril.Wasm.Game.HandleAccept.Mixed Silmaril.Wasm.Game.HandleAccept.Writers.Builders

/-- The host: the `k`-th callout returns the fresh handle `k + 1`, except `accept`, which
returns nothing. -/
def chunkScript : Script := fun k h _ =>
  if h = twoIx.accept then [] else [Val.i32 (BitVec.ofNat 32 (k + 1))]

section Positive

variable {P : Profile}
  (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
  {pol : Policy (BitVec 32)} (hs : ∀ r, pol.sentinel = some r → r = 0)
  {ppol : PPolicy (BitVec 32)} (h0 : ppol.sentinel = 0)
include hP hs h0

open Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk (mem_moduleMixedRel_of_replaySeqC)

/-- **`feed(7)`, `feed(8)`, `finish(1)`, `finish(5)` relates `[7, 8]` to `(8 7)`.** -/
theorem chunkStack_relates_78 :
    ([7, 8], SExp2.ofAtoms [8, 7]) ∈ moduleMixedRel P chunkStack twoIx chunkPix pol ppol :=
  mem_moduleMixedRel_of_replaySeqC chunkStack_instance hP twoIx chunkPix
    (bad := fun r => decide (r = 0)) (fun r h => by simp [hs r h]) (by simp [h0])
    chunkScript refFuel 8
    [⟨⟨0, by decide +kernel⟩, ⟨[.i64 7], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩,
     ⟨⟨0, by decide +kernel⟩, ⟨[.i64 8], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩,
     ⟨⟨1, by decide +kernel⟩, ⟨[.i32 1], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩,
     ⟨⟨1, by decide +kernel⟩, ⟨[.i32 5], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩]
    (by decide +kernel)

/-- **The `finish(1)` that consumes nothing relates `[]` to `()`.** -/
theorem chunkStack_relates_nil :
    ([], SExp2.ofAtoms []) ∈ moduleMixedRel P chunkStack twoIx chunkPix pol ppol :=
  mem_moduleMixedRel_of_replaySeqC chunkStack_instance hP twoIx chunkPix
    (bad := fun r => decide (r = 0)) (fun r h => by simp [hs r h]) (by simp [h0])
    chunkScript refFuel 8
    [⟨⟨0, by decide +kernel⟩, ⟨[.i64 7], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩,
     ⟨⟨0, by decide +kernel⟩, ⟨[.i64 8], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩,
     ⟨⟨1, by decide +kernel⟩, ⟨[.i32 1], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩,
     ⟨⟨1, by decide +kernel⟩, ⟨[.i32 5], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩]
    (by decide +kernel)

end Positive

/-- **The relation at the input `[7, 8]`** is exactly `([7, 8], (8 7))`. -/
theorem chunkStack_rel_eq_78 {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)} (h0 : ppol.sentinel = 0)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    {t | ([7, 8], t) ∈ moduleMixedRel P chunkStack twoIx chunkPix pol ppol} =
      {SExp2.ofAtoms [8, 7]} :=
  Set.eq_singleton_iff_unique_mem.2 ⟨chunkStack_relates_78 hP (fun r h => by simp [hsen] at h) h0,
    fun _ h => chunkStack_rel P hsen hw ha hb ho h⟩

/-! ### At the specification profiles -/

theorem chunkStack_relates_78_spec (nd : Bool) {pol : Policy (BitVec 32)}
    (hs : ∀ r, pol.sentinel = some r → r = 0) {ppol : PPolicy (BitVec 32)}
    (h0 : ppol.sentinel = 0) :
    ([7, 8], SExp2.ofAtoms [8, 7]) ∈
      moduleMixedRel (Profile.spec nd {}) chunkStack twoIx chunkPix pol ppol :=
  chunkStack_relates_78 (fun _ _ h => Step.deterministic_refines_spec nd h) hs h0

end Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk
