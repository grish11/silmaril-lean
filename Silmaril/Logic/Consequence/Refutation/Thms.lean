module

public import Silmaril.Logic.Consequence.Refutation.Defs
public import Silmaril.Logic.Consequence.Structural.Thms
import Silmaril.Proofs.Logic.Consequence.Refutation.Basic

/-!
# Entailment from UNSAT checks: the theorems, with their exact hypotheses

* `entails_closed`: `Entails sat` is closed under reflexivity, weakening along `⊆` and
  multi-cut (`tarskiRules`), for every `sat`.
* `entails_iff_unsat`: `Entails sat Γ c ↔ Unsat sat (Γ ++ neg c)` given `NegSound` and
  `NegComplete`; each direction needs only one of them (`entails_of_unsat`, `unsat_of_entails`).
* `viaUnsat_le_entails` (checker sound, `NegComplete`), `entails_le_viaUnsat` (checker
  complete, `NegSound`), `viaUnsat_eq_entails` (all four).
* `viaUnsat_closed`: under all four, `viaUnsat check neg` is closed under the Tarski rules.
  With only the soundness hypotheses, its closure is still sound (`derives_viaUnsat_le_entails`),
  but `viaUnsat` itself need not be cut-closed (`Silmaril.Logic.Consequence.Refutation.Examples`).
* SZS: `entails_iff_thm` (`Current.THM` and `V2007.THM` of `problem sat Γ c`) and
  `unsat_iff_cax` (`Unsat sat Γ` is `CAX` of any problem with axioms `Γ`).
-/

@[expose] public section

namespace Silmaril.Consequence.Refutation

open Structural

universe u v

variable {M : Type v} {C : Type u} {sat : M → C → Prop} {neg : C → List C}
  {check : List C → Prop}

theorem satAll_append {m : M} {Γ Δ : List C} :
    SatAll sat m (Γ ++ Δ) ↔ SatAll sat m Γ ∧ SatAll sat m Δ :=
  Proofs.Logic.Consequence.Refutation.satAll_append

/-- Semantic entailment is closed under the Tarski rules, unconditionally. -/
theorem entails_closed : Closed tarskiRules (Entails sat) :=
  Proofs.Logic.Consequence.Refutation.entails_closed

theorem entails_of_unsat (hn : NegComplete sat neg) {Γ : List C} {c : C}
    (h : Unsat sat (Γ ++ neg c)) : Entails sat Γ c :=
  Proofs.Logic.Consequence.Refutation.entails_of_unsat hn h

theorem unsat_of_entails (hn : NegSound sat neg) {Γ : List C} {c : C}
    (h : Entails sat Γ c) : Unsat sat (Γ ++ neg c) :=
  Proofs.Logic.Consequence.Refutation.unsat_of_entails hn h

theorem entails_iff_unsat (hs : NegSound sat neg) (hc : NegComplete sat neg) {Γ : List C}
    {c : C} : Entails sat Γ c ↔ Unsat sat (Γ ++ neg c) :=
  ⟨unsat_of_entails hs, entails_of_unsat hc⟩

/-- A sound checker with a `NegComplete` negation only derives entailments. -/
theorem viaUnsat_le_entails (hs : CheckSound sat check) (hn : NegComplete sat neg) :
    viaUnsat check neg ≤ Entails sat :=
  fun _ _ h => entails_of_unsat hn (hs _ h)

/-- A complete checker with a `NegSound` negation derives every entailment. -/
theorem entails_le_viaUnsat (hc : CheckComplete sat check) (hn : NegSound sat neg) :
    Entails sat ≤ viaUnsat check neg :=
  fun _ _ h => hc _ (unsat_of_entails hn h)

theorem viaUnsat_eq_entails (hs : CheckSound sat check) (hc : CheckComplete sat check)
    (hns : NegSound sat neg) (hnc : NegComplete sat neg) : viaUnsat check neg = Entails sat :=
  le_antisymm (viaUnsat_le_entails hs hnc) (entails_le_viaUnsat hc hns)

/-- A sound and complete checker, with an exact negation, computes a Tarski consequence
relation: reflexive, monotone along `⊆`, and cut-closed. -/
theorem viaUnsat_closed (hs : CheckSound sat check) (hc : CheckComplete sat check)
    (hns : NegSound sat neg) (hnc : NegComplete sat neg) :
    Closed tarskiRules (viaUnsat check neg) :=
  viaUnsat_eq_entails hs hc hns hnc ▸ entails_closed

/-- Closing a sound checker's relation under the Tarski rules stays sound. -/
theorem derives_viaUnsat_le_entails (hs : CheckSound sat check) (hn : NegComplete sat neg) :
    Derives tarskiRules (viaUnsat check neg) ≤ Entails sat :=
  derives_le (viaUnsat_le_entails hs hn) entails_closed

/-! ## SZS statuses -/

theorem entails_iff_thm {Γ : List C} {c : C} :
    Entails sat Γ c ↔ Logic.Szs.Current.THM (problem sat Γ c) := Iff.rfl

theorem entails_iff_thm_v2007 {Γ : List C} {c : C} :
    Entails sat Γ c ↔ Logic.Szs.V2007.THM (problem sat Γ c) := Iff.rfl

theorem unsat_iff_cax {Γ : List C} {c : C} :
    Unsat sat Γ ↔ Logic.Szs.Current.CAX (problem sat Γ c) :=
  ⟨fun h => Set.eq_empty_of_forall_notMem h, fun h m hm => (h ▸ hm : m ∈ (∅ : Set M))⟩

theorem unsat_iff_cax_v2007 {Γ : List C} {c : C} :
    Unsat sat Γ ↔ Logic.Szs.V2007.CAX (problem sat Γ c) :=
  unsat_iff_cax

end Silmaril.Consequence.Refutation
