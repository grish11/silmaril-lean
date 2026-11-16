module

public import Silmaril.Logic.FirstOrder.FiniteConnectives.Defs
public import Mathlib.Data.List.Basic

@[expose] public section
namespace Silmaril.Logic.FirstOrder.FiniteConnectives
open Silmaril.Logic.Institution.Examples
variable {Sg : FOL.Signature} {k : Nat} {Γ : Fin k → Sg.S}
variable (M : FOL.Structure Sg) (a : (i : Fin k) → M.carrier (Γ i))

theorem disj_holds (p q : FOL.Formula Sg Γ) :
    FOL.Formula.Holds M (disj p q) a ↔
      FOL.Formula.Holds M p a ∨ FOL.Formula.Holds M q a := by
  classical
  simp only [disj, FOL.Formula.Holds, not_and_or, not_not]

/-- Exact finite-family semantics, including the false empty family. -/
theorem finiteOr_holds (ps : List (FOL.Formula Sg Γ)) :
    FOL.Formula.Holds M (finiteOr ps) a ↔
      ∃ p ∈ ps, FOL.Formula.Holds M p a := by
  induction ps with
  | nil => simp [finiteOr, FOL.Formula.Holds]
  | cons p ps ih =>
    rw [finiteOr, disj_holds, ih]
    constructor
    · intro h
      rcases h with h | ⟨q, hq, h⟩
      · exact ⟨p, List.mem_cons_self, h⟩
      · exact ⟨q, List.mem_cons_of_mem p hq, h⟩
    · rintro ⟨q, hq, h⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inl h
      · exact Or.inr ⟨q, hq, h⟩

/-- Exact finite-family semantics, including the true empty family. -/
theorem finiteAnd_holds (ps : List (FOL.Formula Sg Γ)) :
    FOL.Formula.Holds M (finiteAnd ps) a ↔
      ∀ p ∈ ps, FOL.Formula.Holds M p a := by
  induction ps with
  | nil => simp [finiteAnd, FOL.Formula.Holds]
  | cons p ps ih =>
    change (FOL.Formula.Holds M p a ∧ FOL.Formula.Holds M (finiteAnd ps) a) ↔ _
    rw [ih]
    constructor
    · rintro ⟨hp, hps⟩ q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp
      · exact hps q hq
    · intro h
      exact ⟨h p List.mem_cons_self, fun q hq => h q (List.mem_cons_of_mem p hq)⟩

theorem finiteOr_empty : ¬ FOL.Formula.Holds M (finiteOr ([] : List (FOL.Formula Sg Γ))) a := by
  intro h
  exact h trivial

theorem finiteAnd_empty : FOL.Formula.Holds M (finiteAnd ([] : List (FOL.Formula Sg Γ))) a := trivial

end Silmaril.Logic.FirstOrder.FiniteConnectives
