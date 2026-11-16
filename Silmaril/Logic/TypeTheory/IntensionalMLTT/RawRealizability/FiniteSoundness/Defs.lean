module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalHypotheses

@[expose] public section

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

/-- Realizing assignments whose declaration codes use the actual finite stage cap. -/
noncomputable def RealizesContextAt (cap : ℕ) : {n : ℕ} → Context n → Environment n 0 → Prop
  | _, .nil, _ => True
  | _, .snoc Γ A, ρ => RealizesContextAt cap Γ (Fin.tail ρ) ∧
      ∃ X, Code cap (eval A (Fin.tail ρ)) X ∧ ρ 0 ∈ X

/-- Actual membership at a carrier code in the specified concrete finite code stage. -/
noncomputable def RealizesAt (cap : ℕ) {n : ℕ} (t A : Term n) (ρ : Environment n 0) : Prop :=
  ∃ X, Code cap (eval A ρ) X ∧ eval t ρ ∈ X

/-- Validity over actual assignments and carrier codes in a specified finite stage. -/
noncomputable def ValidAt (cap : ℕ) {n : ℕ} (Γ : Context n) (t A : Term n) : Prop :=
  ∀ ρ, RealizesContextAt cap Γ ρ → RealizesAt cap t A ρ

end Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability
