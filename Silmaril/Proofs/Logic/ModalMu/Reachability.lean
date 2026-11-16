module

public import Silmaril.Logic.ModalMu.Reachability.Defs

@[expose] public section
namespace Silmaril.Logic.ModalMu

/-- The least fixed point is exactly finite-path reachability on every frame. -/
theorem reach_iff {S : Signature} (M : Model S) (a : S.Action) (p : S.Atom)
    (w : M.World) : w ∈ (reach a p).denote M emptyEnv ↔
      FiniteReach (M.step a) (M.valuation p) w := by
  constructor
  · apply Formula.mu_le M _ emptyEnv {v | FiniteReach (M.step a) (M.valuation p) v}
    intro v hv
    change v ∈ M.valuation p ∨ ∃ u, M.step a v u ∧
      FiniteReach (M.step a) (M.valuation p) u at hv
    rcases hv with h | ⟨u, hstep, hu⟩
    · exact .here h
    · exact .next hstep hu
  · intro h
    induction h with
    | here hv =>
        rw [reach, Formula.mu_unfold]
        exact Or.inl hv
    | next hstep _ ih =>
        rw [reach, Formula.mu_unfold]
        exact Or.inr ⟨_, hstep, ih⟩

/-- Any successor-closed witness with a successor at each state lies in ν◇. -/
theorem forever_of_postfixed {S : Signature} (M : Model S) (a : S.Action)
    (X : Set M.World) (h : ∀ w ∈ X, ∃ v, M.step a w v ∧ v ∈ X) :
    X ⊆ (forever a).denote M emptyEnv :=
  Formula.le_nu M _ emptyEnv X h

/-- Deadlocks never satisfy ν◇, even though boxes at deadlocks are vacuously true. -/
theorem not_forever_of_deadlock {S : Signature} (M : Model S) (a : S.Action)
    (w : M.World) (h : ∀ v, ¬ M.step a w v) :
    w ∉ (forever a).denote M emptyEnv := by
  intro hw
  rw [forever, Formula.nu_unfold] at hw
  obtain ⟨v, hv, _⟩ := hw
  exact h v hv

end Silmaril.Logic.ModalMu
