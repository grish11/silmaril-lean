module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take.Thms
public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Examples
public import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Execution.Core.SpecProfile
import Silmaril.Wasm.Spec.Run.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Replay

/-!
# Partial consumption: replayed sessions (non-vacuity)

A session of **four export calls**, `feed(7)`, `feed(8)`, `finish(1)`, `finish(1)`, replayed on
the verified interpreter one after the other (as for `chunkStack`, host `chunkScript`: the `k`-th
callout returns the fresh handle `k + 1`), by kernel evaluation. `feed` calls no import; the first
`finish(1)` calls `word(7) = 1`, `nil() = 2`, `cons(1, 2) = 3` and answers `(1, 3)`: with **two**
values buffered it consumes **one** (`used = 1`, strictly between `0` and the buffered count); the
second calls `word(8) = 4`, `nil() = 5`, `cons(4, 5) = 6` and answers `(1, 6)`: the value `8` stayed
buffered across the first `finish`. Simulating the mixed host along the decoded events with the
chunk buffer:

* `chunkTake_relates_7`: the first `finish` relates `([7], (7))`;
* `chunkTake_relates_8`: the second relates `([8], (8))`;
* `chunkTake_rel_eq_8`: with `chunkTake_sound`, the relation restricted to the input `[8]` is
  exactly `{([8], (8))}`.

**Profiles and policies.** Every profile `P` admitting the deterministic steps of the interpreter
(hypothesis `hP`; the specification profiles, `_spec`), every writer policy whose sentinel, if
any, is `0`, and every parsing policy with sentinel `0`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Accept.Handle Silmaril.Accept.Parse
  Silmaril.Wasm.Game.HandleAccept.Mixed Silmaril.Wasm.Game.HandleAccept.Writers.Builders
  Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk

section Positive

variable {P : Profile}
  (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
  {pol : Policy (BitVec 32)} (hs : ∀ r, pol.sentinel = some r → r = 0)
  {ppol : PPolicy (BitVec 32)} (h0 : ppol.sentinel = 0)
include hP hs h0

open Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk (mem_moduleMixedRel_of_replaySeqC)

/-- **The first `finish(1)` consumes one of two buffered values: `([7], (7))`.** -/
theorem chunkTake_relates_7 :
    ([7], SExp2.ofAtoms [7]) ∈ moduleMixedRel P chunkTake twoIx takePix pol ppol :=
  mem_moduleMixedRel_of_replaySeqC chunkTake_instance hP twoIx takePix
    (bad := fun r => decide (r = 0)) (fun r h => by simp [hs r h]) (by simp [h0])
    chunkScript refFuel 8
    [⟨⟨0, by decide +kernel⟩, ⟨[.i64 7], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩,
     ⟨⟨0, by decide +kernel⟩, ⟨[.i64 8], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩,
     ⟨⟨1, by decide +kernel⟩, ⟨[.i32 1], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩,
     ⟨⟨1, by decide +kernel⟩, ⟨[.i32 1], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩]
    (by decide +kernel)

/-- **The second `finish(1)` consumes the value left buffered: `([8], (8))`.** -/
theorem chunkTake_relates_8 :
    ([8], SExp2.ofAtoms [8]) ∈ moduleMixedRel P chunkTake twoIx takePix pol ppol :=
  mem_moduleMixedRel_of_replaySeqC chunkTake_instance hP twoIx takePix
    (bad := fun r => decide (r = 0)) (fun r h => by simp [hs r h]) (by simp [h0])
    chunkScript refFuel 8
    [⟨⟨0, by decide +kernel⟩, ⟨[.i64 7], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩,
     ⟨⟨0, by decide +kernel⟩, ⟨[.i64 8], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩,
     ⟨⟨1, by decide +kernel⟩, ⟨[.i32 1], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩,
     ⟨⟨1, by decide +kernel⟩, ⟨[.i32 1], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩]
    (by decide +kernel)

end Positive

/-- **The relation at the input `[8]`** is exactly `([8], (8))`. -/
theorem chunkTake_rel_eq_8 {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)} (h0 : ppol.sentinel = 0)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    {t | ([8], t) ∈ moduleMixedRel P chunkTake twoIx takePix pol ppol} = {SExp2.ofAtoms [8]} :=
  Set.eq_singleton_iff_unique_mem.2 ⟨chunkTake_relates_8 hP (fun r h => by simp [hsen] at h) h0,
    fun _ => chunkTake_rel P hsen hw ha hb ho⟩

/-! ### At the specification profiles -/

theorem chunkTake_relates_7_spec (nd : Bool) {pol : Policy (BitVec 32)}
    (hs : ∀ r, pol.sentinel = some r → r = 0) {ppol : PPolicy (BitVec 32)}
    (h0 : ppol.sentinel = 0) :
    ([7], SExp2.ofAtoms [7]) ∈
      moduleMixedRel (Profile.spec nd {}) chunkTake twoIx takePix pol ppol :=
  chunkTake_relates_7 (fun _ _ h => Step.deterministic_refines_spec nd h) hs h0

theorem chunkTake_relates_8_spec (nd : Bool) {pol : Policy (BitVec 32)}
    (hs : ∀ r, pol.sentinel = some r → r = 0) {ppol : PPolicy (BitVec 32)}
    (h0 : ppol.sentinel = 0) :
    ([8], SExp2.ofAtoms [8]) ∈
      moduleMixedRel (Profile.spec nd {}) chunkTake twoIx takePix pol ppol :=
  chunkTake_relates_8 (fun _ _ h => Step.deterministic_refines_spec nd h) hs h0

end Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take
