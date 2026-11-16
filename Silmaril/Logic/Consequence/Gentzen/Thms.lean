module

public import Silmaril.Logic.Consequence.Gentzen.Defs
public import Silmaril.Logic.Consequence.Refutation.Thms
import Silmaril.Proofs.Logic.Consequence.Gentzen.Basic

/-!
# Gentzen sequents: closures, validity, and conversions to UNSAT and TAUTO

* Closure: `le_derives`, `derives_closed`, `derives_le` (least closed relation above `S`),
  `derives_iff_forall_closed`, `derives_derives`, and the Mathlib `ClosureOperator` `closure`.
* `valid_closed`: `Valid sat` is closed under the default rules, for every `sat`. Hence the
  closure of any relation below `Valid sat` is below it (`derives_le_valid`): a Gentzen closure is
  sound as soon as its base is.
* Conversions; every direction names the one negation law it uses, and both are classical
  (excluded middle on `sat m c`, no decidability assumed):
  - `valid_of_unsat` (`NegComplete`) and `unsat_of_valid` (`NegSound`): `valid_iff_unsat`,
    `Γ ⊢ Δ` valid iff `Γ ++ [neg d | d ∈ Δ]` is unsatisfiable;
  - `valid_of_taut` (`NegSound`) and `taut_of_valid` (`NegComplete`): `valid_iff_taut`,
    iff `[neg g | g ∈ Γ] ++ Δ` is a tautology.
* Raw checkers: `viaUnsat_le_valid` (checker sound, `NegComplete`) and `valid_le_viaUnsat`
  (checker complete, `NegSound`); likewise `viaTauto_le_valid`, `valid_le_viaTauto`. A sound raw
  relation has a sound closure (`derives_viaUnsat_le_valid`, `derives_viaTauto_le_valid`);
  completeness is a separate hypothesis, and no structural rule of the raw relation is claimed.
* Consistency: `unsat_iff_valid_nil` (`Γ ⊢ []` valid iff `Γ` unsatisfiable, no hypothesis);
  `unsat_of_viaUnsat_nil` (a sound checker's `Γ ⊢ []` proves `Γ` inconsistent). The converse
  needs completeness.
* Single conclusions: `entails_iff_valid` (`Refutation.Entails sat Γ c ↔ Valid sat Γ [c]`).
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen

open Refutation (SatAll Unsat CheckSound CheckComplete)

universe u v

variable {C : Type u} {M : Type v}

/-! ## Closure -/

theorem le_derives (rs : Rules C) (S : Seq C) : S ≤ Derives rs S := fun _ _ => .base

theorem derives_closed (rs : Rules C) (S : Seq C) : Closed rs (Derives rs S) :=
  ⟨fun h _ _ _ hΓ hΔ => .refl h hΓ hΔ, fun _ _ _ _ h₁ h₂ hd => .weak h₁ h₂ hd,
    fun h _ _ _ _ _ h₁ h₂ => .cut h h₁ h₂⟩

theorem derives_le {rs : Rules C} {R S : Seq C} (hRS : R ≤ S) (hS : Closed rs S) :
    Derives rs R ≤ S :=
  Proofs.Logic.Consequence.Gentzen.derives_least hRS hS

theorem derives_iff_forall_closed {rs : Rules C} {R : Seq C} {Γ Δ : List C} :
    Derives rs R Γ Δ ↔ ∀ S, R ≤ S → Closed rs S → S Γ Δ :=
  ⟨fun h _ hRS hS => derives_le hRS hS Γ Δ h, fun h => h _ (le_derives rs R) (derives_closed rs R)⟩

theorem derives_derives (rs : Rules C) (S : Seq C) : Derives rs (Derives rs S) = Derives rs S :=
  le_antisymm (derives_le le_rfl (derives_closed rs S)) (le_derives rs _)

/-- The Gentzen closure as a Mathlib closure operator; closed elements are `Closed rs`. -/
def closure (rs : Rules C) : ClosureOperator (Seq C) :=
  .ofPred (Derives rs) (Closed rs) (le_derives rs) (derives_closed rs)
    fun _ _ h hS => derives_le h hS

/-! ## Validity -/

theorem valid_closed {sat : M → C → Prop} : Closed defaultRules (Valid sat) :=
  Proofs.Logic.Consequence.Gentzen.valid_closed

/-- A Gentzen closure (default rules) of a sound relation is sound. -/
theorem derives_le_valid {sat : M → C → Prop} {S : Seq C} (h : S ≤ Valid sat) :
    Derives defaultRules S ≤ Valid sat :=
  derives_le h valid_closed

theorem unsat_iff_valid_nil {sat : M → C → Prop} {Γ : List C} :
    Unsat sat Γ ↔ Valid sat Γ [] := by
  simp [Unsat, Valid]

theorem entails_iff_valid {sat : M → C → Prop} {Γ : List C} {c : C} :
    Refutation.Entails sat Γ c ↔ Valid sat Γ [c] := by
  simp [Refutation.Entails, Valid]

/-! ## UNSAT and TAUTO -/

variable {sat : M → C → Prop} {neg : C → C} {Γ Δ : List C}

theorem valid_of_unsat (hn : NegComplete sat neg) (h : Unsat sat (Γ ++ Δ.map neg)) :
    Valid sat Γ Δ :=
  Proofs.Logic.Consequence.Gentzen.valid_of_unsat hn h

theorem unsat_of_valid (hn : NegSound sat neg) (h : Valid sat Γ Δ) :
    Unsat sat (Γ ++ Δ.map neg) :=
  Proofs.Logic.Consequence.Gentzen.unsat_of_valid hn h

theorem valid_iff_unsat (hs : NegSound sat neg) (hc : NegComplete sat neg) :
    Valid sat Γ Δ ↔ Unsat sat (Γ ++ Δ.map neg) :=
  ⟨unsat_of_valid hs, valid_of_unsat hc⟩

theorem valid_of_taut (hn : NegSound sat neg) (h : Taut sat (Γ.map neg ++ Δ)) :
    Valid sat Γ Δ :=
  Proofs.Logic.Consequence.Gentzen.valid_of_taut hn h

theorem taut_of_valid (hn : NegComplete sat neg) (h : Valid sat Γ Δ) :
    Taut sat (Γ.map neg ++ Δ) :=
  Proofs.Logic.Consequence.Gentzen.taut_of_valid hn h

theorem valid_iff_taut (hs : NegSound sat neg) (hc : NegComplete sat neg) :
    Valid sat Γ Δ ↔ Taut sat (Γ.map neg ++ Δ) :=
  ⟨taut_of_valid hc, valid_of_taut hs⟩

/-! ## Raw checkers -/

variable {check taut : List C → Prop}

theorem viaUnsat_le_valid (hs : CheckSound sat check) (hn : NegComplete sat neg) :
    viaUnsat check neg ≤ Valid sat :=
  fun _ _ h => valid_of_unsat hn (hs _ h)

theorem valid_le_viaUnsat (hc : CheckComplete sat check) (hn : NegSound sat neg) :
    Valid sat ≤ viaUnsat check neg :=
  fun _ _ h => hc _ (unsat_of_valid hn h)

theorem viaTauto_le_valid (hs : TautSound sat taut) (hn : NegSound sat neg) :
    viaTauto taut neg ≤ Valid sat :=
  fun _ _ h => valid_of_taut hn (hs _ h)

theorem valid_le_viaTauto (hc : TautComplete sat taut) (hn : NegComplete sat neg) :
    Valid sat ≤ viaTauto taut neg :=
  fun _ _ h => hc _ (taut_of_valid hn h)

theorem derives_viaUnsat_le_valid (hs : CheckSound sat check) (hn : NegComplete sat neg) :
    Derives defaultRules (viaUnsat check neg) ≤ Valid sat :=
  derives_le_valid (viaUnsat_le_valid hs hn)

theorem derives_viaTauto_le_valid (hs : TautSound sat taut) (hn : NegSound sat neg) :
    Derives defaultRules (viaTauto taut neg) ≤ Valid sat :=
  derives_le_valid (viaTauto_le_valid hs hn)

/-- A sound checker's `Γ ⊢ []` proves `Γ` inconsistent; no negation law is needed. -/
theorem unsat_of_viaUnsat_nil (hs : CheckSound sat check) (h : viaUnsat check neg Γ []) :
    Unsat sat Γ := by
  simpa [viaUnsat] using hs _ h

/-- The single-conclusion refutation relation is the Gentzen one at `[c]`. -/
theorem refutation_viaUnsat_iff {c : C} :
    Refutation.viaUnsat check (fun c => [neg c]) Γ c ↔ viaUnsat check neg Γ [c] := Iff.rfl

end Silmaril.Consequence.Gentzen
