module

public import Silmaril.Wasi.Component.Consequence.Signed.Spec.Defs
public import Silmaril.Wasi.Component.Consequence.Signed.Thms
public import Silmaril.Wasi.Component.Consequence.Checkers.Thms
import Silmaril.Proofs.Wasi.Component.Consequence.Signed.Spec

/-! # Specification components for the signed protocols: theorems

About **specification strategies** only (no compiled component, no core module):

* `batches_batchEmitter`: at the call boundary, the batches of `batchEmitter enc L` are exactly
  `L`, for a decoder inverting `enc`. So the emitter is a sound UNSAT emitter exactly when every
  list of `L` is unsatisfiable, and then its UNSAT reading is valid
  (`batchUnsat_batchEmitter_le_valid`).
* `seqOf_idChecker`: the identity checker accepts `Γ ⊢ Δ` exactly when `Γ` and `Δ` share a
  formula. Its relation is `Gentzen.Reflexive` (`reflexive_idChecker`) and valid for every
  satisfaction relation (`idChecker_le_valid`).

Proofs: `Silmaril.Proofs.Wasi.Component.Consequence.Signed.Spec`.
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence

open Silmaril.Consequence (Signed)
open Silmaril.Consequence.Gentzen
open Silmaril.Consequence.Refutation (Unsat CheckSound)
open Silmaril.Wasi.Accept (Traces)
open Silmaril.Wasm.Component (Val)

variable {V M : Type} {enc : V → Val} {decV : List Val → Option V}

/-- **The batches of the emitter are exactly `L`.** -/
theorem batches_batchEmitter (hdec : ∀ args a, decV args = some a ↔ args = [enc a])
    (td : TrapDone) (L : Set (List (Signed V))) (l : List (Signed V)) :
    batches (Traces (batchEmitter enc L)) (importBatch .call specBatchFns decV td) l ↔ l ∈ L :=
  Proofs.Wasi.Component.Consequence.SignedSpec.batches_batchEmitter hdec td L l

/-- An emitter of unsatisfiable batches has a valid UNSAT reading. -/
theorem batchUnsat_batchEmitter_le_valid (hdec : ∀ args a, decV args = some a ↔ args = [enc a])
    (td : TrapDone) {L : Set (List (Signed V))} {sat : M → Signed V → Prop}
    (hL : ∀ l ∈ L, Unsat sat l) (hn : NegComplete sat (-·)) :
    batchUnsat (Traces (batchEmitter enc L)) (importBatch .call specBatchFns decV td) (-·) ≤
      Valid sat :=
  batchUnsat_le_valid (fun l h => hL l ((batches_batchEmitter hdec td L l).1 h)) hn

theorem signedPairDec_iff (args : List Val)
    (q : List (Signed (BitVec 32)) × List (Signed (BitVec 32))) :
    args2 signedList? signedList? args = some q ↔ args = signedPairEnc q :=
  Proofs.Wasi.Component.Consequence.SignedSpec.signedPairDec_iff args q

/-- **The identity checker accepts exactly the sequents sharing a formula.** -/
theorem seqOf_idChecker (Γ Δ : List (Signed (BitVec 32))) :
    seqOf (Traces idChecker) (seqCheck checkFn signedList? signedList?) Γ Δ ↔ ∃ x ∈ Γ, x ∈ Δ :=
  (accepted_answerChecker (enc := signedPairEnc) signedPairDec_iff Γ Δ).trans (by simp)

theorem reflexive_idChecker :
    Reflexive (seqOf (Traces idChecker) (seqCheck checkFn signedList? signedList?)) :=
  fun _ _ c hΓ hΔ => (seqOf_idChecker _ _).2 ⟨c, hΓ, hΔ⟩

/-- Valid for every satisfaction relation. -/
theorem idChecker_le_valid (sat : M → Signed (BitVec 32) → Prop) :
    seqOf (Traces idChecker) (seqCheck checkFn signedList? signedList?) ≤ Valid sat := by
  intro Γ Δ h m hm
  obtain ⟨x, hΓ, hΔ⟩ := (seqOf_idChecker Γ Δ).1 h
  exact ⟨x, hΔ, hm x hΓ⟩

end Silmaril.Wasi.Consequence
