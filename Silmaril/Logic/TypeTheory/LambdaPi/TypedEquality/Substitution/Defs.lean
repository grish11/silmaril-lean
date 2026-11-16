module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Structural.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality

open Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Every source declaration is assigned an actually source-typed target term. -/
def TypedSubstitution {n l m : ℕ} (Γ : Context n) (T : Context l) (Δ : Context m)
    (σ : Fin n → Term m) : Prop :=
  ∀ {i A}, Lookup Γ i A → Equality T Δ (σ i) (σ i) (A.subst σ)

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
