module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Codes.Inversion
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Environment.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

/-- A closed quotient assignment realizes each dependent declaration by an actual code and member.
This predicate contains no typing-soundness hypothesis or derivation interpretation field. -/
noncomputable def RealizesContext : {n : ℕ} → Context n → Environment n 0 → Prop
  | _, .nil, _ => True
  | _, .snoc Γ A, ρ => RealizesContext Γ (Fin.tail ρ) ∧
      ∃ i X, Code i (eval A (Fin.tail ρ)) X ∧ ρ 0 ∈ X

/-- Actual quotient membership at an interpreted carrier, at some finite code level. -/
noncomputable def Realizes {n : ℕ} (t A : Term n) (ρ : Environment n 0) : Prop :=
  ∃ i X, Code i (eval A ρ) X ∧ eval t ρ ∈ X

/-- A source typing judgment is valid at every actually realizing closed assignment. -/
noncomputable def Valid {n : ℕ} (Γ : Context n) (t A : Term n) : Prop :=
  ∀ ρ, RealizesContext Γ ρ → Realizes t A ρ

end Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability
