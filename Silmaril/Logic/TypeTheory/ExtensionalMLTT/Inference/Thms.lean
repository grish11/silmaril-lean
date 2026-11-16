module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inference.Defs

public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Packaging adds no target derivations. -/
theorem closedInferenceSystem_derivable (j : EJdg) :
    Nonempty (closedInferenceSystem.Derivation j) ↔ ECtx.JEqH ∅ j.Γ j.A j.a j.b :=
  ⟨fun ⟨h⟩ => h.down, fun h => ⟨⟨h⟩⟩⟩

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
