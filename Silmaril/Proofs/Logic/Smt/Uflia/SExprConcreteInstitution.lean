module

public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete.Institution.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete
open Silmaril.Logic.Institution

/-- At each fixed signature the decoder model translation is the identity;
this does not assert model expansion along arbitrary symbol-identifying arrows. -/
theorem decodeComorphism_modelExpansive : ∀ S,
    Corridor.ModelExpansive (decodeComorphism.ρ.app S) := fun _ M => ⟨M, rfl⟩

/-- The same fixed-signature decoder model expansion holds with prefix evidence. -/
theorem declarationDecodeComorphism_modelExpansive : ∀ S,
    Corridor.ModelExpansive (declarationDecodeComorphism.ρ.app S) := fun _ M => ⟨M, rfl⟩

/-- Prefix evidence does not change the available models at a fixed signature. -/
theorem prefixForgetComorphism_modelExpansive : ∀ S,
    Corridor.ModelExpansive (prefixForgetComorphism.ρ.app S) := fun _ M => ⟨M, rfl⟩

end Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete
