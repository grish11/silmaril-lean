module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.LambdaCongruence.Thms

@[expose] public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
open Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Coherent source-equal variable images, at each declaration's left substituted
carrier. Every premise is an actual independent source equality. -/
def EqualSubstitution {n l m : ℕ} (Γ : Context n) (T : Context l) (Δ : Context m)
    (σ τ : Fin n → Term m) : Prop :=
  ∀ {i A}, Lookup Γ i A → Equality T Δ (σ i) (τ i) (A.subst σ)

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
