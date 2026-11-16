module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Structure
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SimultaneousSubstitution

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Every lookup image has an actual target typing at the common rule budget. -/
def ECtx.AssignmentB (levels : ℕ) (σ : String → ETm 0) (Γ Δ : ECtx) : Prop :=
  ∀ {y B}, Γ.Lookup y B → ECtx.JEqB levels ∅ Δ (B.fmap σ) (σ y) (σ y)

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
