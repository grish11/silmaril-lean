module

public import Silmaril.Logic.Consequence.Gentzen.Finitary.Thms

/-!
# Examples: finitary versus infinitary validity

Models and formulas are natural numbers, and `m` satisfies `n` iff `m ≠ n`. No model satisfies
every formula, so `ℕ ⊢ ∅` is infinitarily valid (`infValid_univ`), but every finite list of
formulas has a model (any number above their sum), so no finite sub-sequent is valid
(`not_onSet_valid`): the finitary reading of validity is strictly weaker without compactness.
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen.Finitary.Examples

/-- `m` satisfies `n` iff `m ≠ n`. -/
def neq (m n : ℕ) : Prop := m ≠ n

theorem infValid_univ : InfValid neq Set.univ ∅ := fun m hm => absurd rfl (hm m trivial)

theorem le_sum_of_mem {l : List ℕ} {n : ℕ} (h : n ∈ l) : n ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := ih h; simp; omega

theorem not_onSet_valid : ¬ onSet (Valid neq) Set.univ ∅ := by
  rintro ⟨Γ, Δ, -, hΔ, h⟩
  obtain ⟨d, hd, -⟩ := h (Γ.sum + 1) fun n hn => by
    have := le_sum_of_mem hn
    simp only [neq]; omega
  exact hΔ d hd

end Silmaril.Consequence.Gentzen.Finitary.Examples
