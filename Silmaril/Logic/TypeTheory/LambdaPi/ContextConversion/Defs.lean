module

public import Silmaril.Logic.TypeTheory.LambdaPi.Substitution.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.LambdaPi

/-- Paired contexts with convertible, actually Type-sorted declarations at every position. -/
inductive ContextConversion (C : Calculus) : List Term → List Term → Prop where
  | nil : ContextConversion C [] []
  | cons {Γ Δ A B} : ContextConversion C Γ Δ →
      Derives C ∅ ⟨Γ, A, Term.univ .type⟩ → Derives C ∅ ⟨Δ, B, Term.univ .type⟩ →
      C.Conversion A B → ContextConversion C (A :: Γ) (B :: Δ)

end Silmaril.Logic.TypeTheory.LambdaPi
