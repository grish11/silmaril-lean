module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Derivation

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Preserve every typed free-variable lookup, without changing terms or declaration types. -/
def ECtx.Embeds (Γ Δ : ECtx) : Prop := ∀ {x A}, Γ.Lookup x A → Δ.Lookup x A

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
