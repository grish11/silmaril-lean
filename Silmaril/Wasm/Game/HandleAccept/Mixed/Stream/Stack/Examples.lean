module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack.Thms
public import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Execution.Core.SpecProfile
import Silmaril.Wasm.Spec.Run.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Replay

/-!
# A streaming parser keeping its stack in globals: examples (non-vacuity)

`stackParse_sound` bounds the mixed relation of `stackParse` by `stackR`. Here it is shown
non-empty on a session of **three export calls**, `append(7)`, `append(8)`, `done()`, replayed on
the verified interpreter one after the other, each from the store the previous call left
(`Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.replaySeqR`), with a host returning the
fresh handles `1, 2, …` to the writer calls (`stackScript`), by kernel evaluation: `append(7)`
calls `nil() = 1`, `word(7) = 2`, `cons(2, 1) = 3`; `append(8)` calls `word(8) = 4`,
`cons(4, 3) = 5`; `done()` answers `5`. Simulating the mixed host (store semantics, with the
append buffer) along the decoded events resolves `5` to `(8 7)` for the input `[7, 8]`
(`Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.mem_moduleMixedRel_of_replaySeq`).

**Profiles and policies.** Every profile `P` admitting the deterministic steps of the interpreter
(hypothesis `hP`; every specification profile `Profile.spec nd {}`, the `_spec` corollary), every
writer policy whose sentinel, if any, is `0`, and every parsing policy with sentinel `0` whose
`done` clears the buffer.

* `stackParse_relates_78`: `([7, 8], (8 7))` is in the mixed relation of `stackParse`;
* `stackParse_rel_eq_78`: with `stackParse_sound`, the relation restricted to the input `[7, 8]`
  is exactly `{([7, 8], (8 7))}`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Accept.Handle Silmaril.Accept.Parse
  Silmaril.Wasm.Game.HandleAccept.Mixed Silmaril.Wasm.Game.HandleAccept.Writers.Builders

/-- The host: the `k`-th callout returns the fresh handle `k + 1`, except `accept`, which
returns nothing. -/
def stackScript : Script := fun k h _ =>
  if h = twoIx.accept then [] else [Val.i32 (BitVec.ofNat 32 (k + 1))]

section Positive

variable {P : Profile}
  (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
  {pol : Policy (BitVec 32)} (hs : ∀ r, pol.sentinel = some r → r = 0)
  {ppol : PPolicy (BitVec 32)} (h0 : ppol.sentinel = 0) (hc : ppol.doneClears = true)
include hP hs h0 hc

open Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream (mem_moduleMixedRel_of_replaySeq)

/-- **`append(7)`, `append(8)`, `done()` relates `[7, 8]` to `(8 7)`.** -/
theorem stackParse_relates_78 :
    ([7, 8], SExp2.ofAtoms [8, 7]) ∈ moduleMixedRel P stackParse twoIx stackPix pol ppol :=
  mem_moduleMixedRel_of_replaySeq stackParse_instance hP twoIx stackPix
    (bad := fun r => decide (r = 0)) (fun r h => by simp [hs r h]) (by simp [h0])
    stackScript refFuel 8
    [⟨⟨0, by decide +kernel⟩, ⟨[.i64 7], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩,
     ⟨⟨0, by decide +kernel⟩, ⟨[.i64 8], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩,
     ⟨⟨1, by decide +kernel⟩, ⟨[], Silmaril.Wasm.Spec.typedB_sound (by decide +kernel)⟩⟩]
    (by rw [hc]; decide +kernel)

end Positive

/-- **The relation at the input `[7, 8]`** is exactly `([7, 8], (8 7))`. -/
theorem stackParse_rel_eq_78 {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)} (h0 : ppol.sentinel = 0)
    (hc : ppol.doneClears = true) (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    {t | ([7, 8], t) ∈ moduleMixedRel P stackParse twoIx stackPix pol ppol} =
      {SExp2.ofAtoms [8, 7]} :=
  Set.eq_singleton_iff_unique_mem.2
    ⟨stackParse_relates_78 hP (fun r h => by simp [hsen] at h) h0 hc,
      fun _ h => stackParse_rel P hsen hw ha hc hb ho h⟩

/-! ### At the specification profiles -/

theorem stackParse_relates_78_spec (nd : Bool) {pol : Policy (BitVec 32)}
    (hs : ∀ r, pol.sentinel = some r → r = 0) {ppol : PPolicy (BitVec 32)}
    (h0 : ppol.sentinel = 0) (hc : ppol.doneClears = true) :
    ([7, 8], SExp2.ofAtoms [8, 7]) ∈
      moduleMixedRel (Profile.spec nd {}) stackParse twoIx stackPix pol ppol :=
  stackParse_relates_78 (fun _ _ h => Step.deterministic_refines_spec nd h) hs h0 hc

end Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack
