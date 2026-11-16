module

public import Silmaril.Logic.Consequence.Gentzen.Profiles.Thms

/-!
# Examples: profiles

Weakening along sub-permutations on both sides (`⟨False, List.Subperm, False⟩`) gives exchange
but not contraction: the closure of `[0, 0] ⊢ [1]` never derives `[0] ⊢ [1]`
(`subperm_not_contractionL`).
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen.Profiles.Examples

/-- Only sub-permutation weakening. -/
def subpermRules : Rules ℕ := ⟨False, List.Subperm, False⟩

/-- `[0, 0] ⊢ [1]`, nothing else. -/
def twice : Seq ℕ := fun Γ Δ => Γ = [0, 0] ∧ Δ = [1]

theorem twice_subperm {Γ Δ : List ℕ} (h : Derives subpermRules twice Γ Δ) :
    [0, 0].Subperm Γ := by
  induction h with
  | base h => exact h.1 ▸ List.Subperm.refl _
  | refl h => exact h.elim
  | weak h₁ _ _ ih => exact ih.trans h₁
  | cut h => exact h.elim

theorem subperm_exchangeL : ExchangeL (Derives subpermRules twice) :=
  fun _ _ _ hp hd => .weak (rs := subpermRules) hp.subperm (List.Subperm.refl _) hd

theorem subperm_not_contractionL : ¬ ContractionL (Derives subpermRules twice) := fun h =>
  absurd (twice_subperm (@h 0 [] [1] (.base ⟨rfl, rfl⟩))).length_le (by decide)

end Silmaril.Consequence.Gentzen.Profiles.Examples
