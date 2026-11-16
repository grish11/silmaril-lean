module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Derivation
public import Silmaril.Logic.Metatheory.InferenceSystemCat

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

open Silmaril.Logic.Metatheory

/-- The actual unbounded closed extensional rules, lifted only from `Prop` to `Type`. -/
def closedInferenceSystem : InferenceSystemCat where
  Conclusion := EJdg
  Derivation j := PLift (ECtx.JEqH ∅ j.Γ j.A j.a j.b)

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
