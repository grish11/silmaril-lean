module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Defs

/-! # Primitive interpretation in the abort-extended LetIter model -/

@[expose] public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

/-- Interpret primitives by projecting their exact syntactic computation arrows. -/
@[instance_reducible] noncomputable def repairedInstructionModel (pe : ε) :
    InstructionModel (repairedValues (τ := τ) (Φ := Φ) pe) (typeModel pe) Φ where
  denote f := (repairedProjection pe).map ((instructionModel pe).denote f)

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
