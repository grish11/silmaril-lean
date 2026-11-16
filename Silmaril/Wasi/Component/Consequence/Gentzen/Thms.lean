module

public import Silmaril.Wasi.Component.Consequence.Gentzen.Defs
public import Silmaril.Wasi.Component.Consequence.Checkers.Thms
public import Silmaril.Logic.Consequence.Gentzen.Thms
import Silmaril.Proofs.Wasi.Component.Consequence.Gentzen

/-! # Gentzen sequents from component UNSAT and TAUTO checkers: theorems

* **Adapters, for any component**. If the component's list predicate is a sound UNSAT checker
  (`CheckSound`, a hypothesis) and negation satisfies `NegComplete`, its UNSAT reading is valid
  (`unsatSeq_le_valid`), and so is the Gentzen closure of that reading (`derives_unsatSeq_le_valid`).
  The TAUTO reading needs `TautSound` and `NegSound` (`tautSeq_le_valid`,
  `derives_tautSeq_le_valid`). Completeness goes the other way, with the other negation law
  (`valid_le_unsatSeq`, `valid_le_tautSeq`).
* **Signed formulas**: the sign flip satisfies both negation laws for `signedSat`
  (`signed_negSound`, `signed_negComplete`).
* **The clash checker** (a specification strategy, not a compiled component) accepts exactly
  the lists with a clash (`checkerOf_clashU32`). It is sound **both** as an UNSAT checker and as
  a TAUTO checker, for every valuation, for different reasons (`clashU32_checkSound`,
  `clashU32_tautSound`), so both Gentzen readings are valid (`unsatSeq_clashU32_le_valid`,
  `tautSeq_clashU32_le_valid`). Its UNSAT reading is `Reflexive` (`unsatSeq_clashU32_reflexive`).
  Its execution status for a list is `STH` when the list clashes and `SCT` otherwise
  (`status_clashU32`). That status is about plays, and it is not the SZS status of the formula.

Proofs: `Silmaril.Proofs.Wasi.Component.Consequence.Gentzen`.
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence

open Silmaril.Consequence (Signed)
open Silmaril.Consequence.Gentzen
open Silmaril.Consequence.Refutation (CheckSound CheckComplete)
open Silmaril.Wasi.Accept (Traces)
open Silmaril.Wasm.Component (Val)

variable {F M : Type} {T : Set (List WEv)} {r : Reading Unit (List F)} {neg : F → F}
  {sat : M → F → Prop}

/-! ## Adapters -/

/-- **A sound UNSAT component gives valid sequents.** -/
theorem unsatSeq_le_valid (hs : CheckSound sat (checkerOf T r)) (hn : NegComplete sat neg) :
    unsatSeq T r neg ≤ Valid sat :=
  viaUnsat_le_valid hs hn

theorem derives_unsatSeq_le_valid (hs : CheckSound sat (checkerOf T r))
    (hn : NegComplete sat neg) : Derives defaultRules (unsatSeq T r neg) ≤ Valid sat :=
  derives_viaUnsat_le_valid hs hn

theorem valid_le_unsatSeq (hc : CheckComplete sat (checkerOf T r)) (hn : NegSound sat neg) :
    Valid sat ≤ unsatSeq T r neg :=
  valid_le_viaUnsat hc hn

/-- **A sound TAUTO component gives valid sequents.** -/
theorem tautSeq_le_valid (hs : TautSound sat (checkerOf T r)) (hn : NegSound sat neg) :
    tautSeq T r neg ≤ Valid sat :=
  viaTauto_le_valid hs hn

theorem derives_tautSeq_le_valid (hs : TautSound sat (checkerOf T r)) (hn : NegSound sat neg) :
    Derives defaultRules (tautSeq T r neg) ≤ Valid sat :=
  derives_viaTauto_le_valid hs hn

theorem valid_le_tautSeq (hc : TautComplete sat (checkerOf T r)) (hn : NegComplete sat neg) :
    Valid sat ≤ tautSeq T r neg :=
  valid_le_viaTauto hc hn

/-! ## Signed formulas -/

variable {A : Type} {v : M → A → Prop}

theorem signed_negSound : NegSound (signedSat v) (-·) := fun m x h =>
  (Proofs.Wasi.Component.Consequence.signedSat_neg v m x).1 h

theorem signed_negComplete : NegComplete (signedSat v) (-·) := fun m x h =>
  (Proofs.Wasi.Component.Consequence.signedSat_neg v m x).2 h

/-! ## The clash checker -/

/-- **The clash checker accepts exactly the lists with a clash.** -/
theorem checkerOf_clashU32 (Γ : List (Signed (BitVec 32))) :
    checkerOf (Traces clashU32) (listCheck checkFn clashDec) Γ ↔ Clash Γ := by
  have := accepted_answerChecker (ans := fun q => decide (Clash q.2)) (enc := clashEnc)
    Proofs.Wasi.Component.Consequence.clashDec_iff () Γ
  simp only [decide_eq_true_eq] at this
  exact this

/-- As an UNSAT checker, it is sound for every valuation. -/
theorem clashU32_checkSound {v : M → BitVec 32 → Prop} :
    CheckSound (signedSat v) (checkerOf (Traces clashU32) (listCheck checkFn clashDec)) :=
  fun Γ h => Proofs.Wasi.Component.Consequence.clash_unsat v Γ ((checkerOf_clashU32 Γ).1 h)

/-- As a TAUTO checker, it is sound for every valuation too. -/
theorem clashU32_tautSound {v : M → BitVec 32 → Prop} :
    TautSound (signedSat v) (checkerOf (Traces clashU32) (listCheck checkFn clashDec)) :=
  fun Δ h => Proofs.Wasi.Component.Consequence.clash_taut v Δ ((checkerOf_clashU32 Δ).1 h)

theorem unsatSeq_clashU32_le_valid {v : M → BitVec 32 → Prop} :
    unsatSeq (Traces clashU32) (listCheck checkFn clashDec) (-·) ≤ Valid (signedSat v) :=
  unsatSeq_le_valid clashU32_checkSound signed_negComplete

theorem tautSeq_clashU32_le_valid {v : M → BitVec 32 → Prop} :
    tautSeq (Traces clashU32) (listCheck checkFn clashDec) (-·) ≤ Valid (signedSat v) :=
  tautSeq_le_valid clashU32_tautSound signed_negSound

/-- **The UNSAT reading of the clash checker is reflexive**: `c ∈ Γ` and `c ∈ Δ` put `c` and
`-c` in `Γ ++ Δ.map (-·)`. -/
theorem unsatSeq_clashU32_reflexive :
    Reflexive (unsatSeq (Traces clashU32) (listCheck checkFn clashDec) (-·)) :=
  fun _ _ c hΓ hΔ => (checkerOf_clashU32 _).2
    ⟨c, List.mem_append_left _ hΓ, List.mem_append_right _ (List.mem_map_of_mem hΔ)⟩

/-- **The execution status of the clash checker on a list**: `STH` iff the list clashes. -/
theorem status_clashU32 (Γ : List (Signed (BitVec 32))) :
    (status (Traces clashU32) (listCheck checkFn clashDec) () Γ).exec =
      if Clash Γ then .STH else .SCT := by
  have := status_answerChecker (ans := fun q => decide (Clash q.2)) (enc := clashEnc)
    Proofs.Wasi.Component.Consequence.clashDec_iff () Γ
  simp only [decide_eq_true_eq] at this
  exact this

end Silmaril.Wasi.Consequence
