module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Derivation

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- Every declared variable of the source has the same type in the target context. -/
def Ctx.LookupLE (Γ Δ : Ctx) : Prop :=
  ∀ {x : String} {A : Tm 0}, Γ.Lookup x A → Δ.Lookup x A

/-- Only the original theory leaves require a separate context-transport contract. -/
def HypothesisTransport (levels : RuleBudget) (H H' : Set Jdg) : Prop :=
  ∀ {Γ Δ : Ctx} {A a b : Tm 0}, (⟨Γ, A, a, b⟩ : Jdg) ∈ H → Γ.LookupLE Δ →
    Δ.JEqB levels H' .unit .star .star → Δ.JEqB levels H' A a b

/-- Close actual hypothesis membership under lookup-preserving context extension.

This is an explicitly larger theory, not an assertion that arbitrary hypotheses
can be used unchanged in other source contexts.
-/
def ContextClosure (H : Set Jdg) : Set Jdg :=
  {j | ∃ Γ, (⟨Γ, j.A, j.a, j.b⟩ : Jdg) ∈ H ∧ Γ.LookupLE j.Γ}

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
