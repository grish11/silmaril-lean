module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional.Syntax.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Derivation.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Every scoped source lookup has an actual typing image in the target context. -/
def TypedAssignment {n : ℕ} (Γ : Context n) (Δ : ECtx) (σ : Fin n → ETm 0) : Prop :=
  ∀ {i A}, Lookup Γ i A → ECtx.JEqH ∅ Δ (term σ A) (σ i) (σ i)


end Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional
