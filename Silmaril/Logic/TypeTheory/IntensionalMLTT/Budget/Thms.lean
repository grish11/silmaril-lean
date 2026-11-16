module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Budget.Defs
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Rules

@[expose] public section

/-! Every explicit proof has a finite cap containing its entire final judgment. -/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

theorem Conversion.endpoints_le_budget {n : ℕ} {t u : Term n} (d : Conversion t u) :
    max t.universeBound u.universeBound ≤ d.universeBudget := by
  cases d <;> exact Nat.le_max_left _ _

theorem Derivation.judgment_le_budget {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : Derivation Γ t A) :
    max Γ.universeBound (max t.universeBound A.universeBound) ≤ d.universeBudget := by
  cases d <;> exact Nat.le_max_left _ _

/-- Every declaration occurrence is included in its original context proof budget. -/
theorem ContextDerivation.context_le_budget {n : ℕ} {Γ : Context n}
    (d : ContextDerivation Γ) : Γ.universeBound ≤ d.universeBudget := by
  cases d with
  | nil => exact Nat.le_refl _
  | @snoc n i Γ A hΓ hA =>
    have hBounds : Γ.universeBound ≤ hA.universeBudget ∧
        A.universeBound ≤ hA.universeBudget ∧ i + 1 ≤ hA.universeBudget := by
      simpa only [max_le_iff, Term.universeBound] using hA.judgment_le_budget
    exact (max_le hBounds.1 hBounds.2.1).trans (Nat.le_max_right _ _)

/-- A finite proof tree belongs to the stage given by its computed budget. -/
def Derivation.atOwnBudget {n : ℕ} {Γ : Context n} {t A : Term n} (d : Derivation Γ t A) :
    BoundedDerivation d.universeBudget Γ t A := ⟨d, Nat.le_refl _⟩

/-- Every derivable judgment has an actual whole-proof-bounded witness. -/
theorem finite_proof_capture {n : ℕ} {Γ : Context n} {t A : Term n} (h : Typing Γ t A) :
    ∃ levels, Nonempty (BoundedDerivation levels Γ t A) := by
  obtain ⟨d⟩ := h
  exact ⟨d.universeBudget, ⟨d.atOwnBudget⟩⟩

/-- Increasing a budget preserves the proof tree exactly. -/
@[simp] theorem BoundedDerivation.include_val {levels more n : ℕ} {Γ : Context n}
    {t A : Term n} (h : levels ≤ more) (d : BoundedDerivation levels Γ t A) :
    (d.include h).val = d.val := rfl

/-- Identity inclusions preserve a bounded proof as a subtype value. -/
@[simp] theorem BoundedDerivation.include_refl {levels n : ℕ} {Γ : Context n}
    {t A : Term n} (d : BoundedDerivation levels Γ t A) :
    d.include (Nat.le_refl levels) = d := rfl

/-- Consecutive budget inclusions agree with direct inclusion. -/
@[simp] theorem BoundedDerivation.include_comp {levels more most n : ℕ} {Γ : Context n}
    {t A : Term n} (h : levels ≤ more) (k : more ≤ most)
    (d : BoundedDerivation levels Γ t A) :
    (d.include h).include k = d.include (h.trans k) := rfl

/-- The natural identity example's whole derivation uses only universe level zero. -/
theorem natIdentity_budget : natIdentity_derivation.universeBudget = 1 := rfl

/-- The recursion example's entire derivation fits the same one-level budget. -/
theorem natRecOne_budget : natRecOne_derivation.universeBudget = 1 := rfl

/-- The J example's whole derivation uses only universe level zero. -/
theorem jZero_budget : jZero_derivation.universeBudget = 1 := rfl

end Silmaril.Logic.TypeTheory.IntensionalMLTT
