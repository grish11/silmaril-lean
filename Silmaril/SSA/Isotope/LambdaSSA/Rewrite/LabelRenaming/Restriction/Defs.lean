module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Defs

/-! # Scope of the written branch targets of a region -/

@[expose] public section

universe u

namespace Silmaril.Isotope.LambdaSSA

variable {Φ : Type u}

/-- Every branch is within the available label prefix. A CFG extends the
prefix by its own local labels in the entry and in every block. Both case
arms and even untargeted block bodies contribute written targets. -/
def Region.LabelsBound (bound : Nat) : Region Φ → Prop
  | .br i _ => i < bound
  | .case _ left right => left.LabelsBound bound ∧ right.LabelsBound bound
  | .let₁ _ body | .let₂ _ body => body.LabelsBound bound
  | .cfg entry n blocks =>
      entry.LabelsBound (n + bound) ∧ ∀ i, (blocks i).LabelsBound (n + bound)

end Silmaril.Isotope.LambdaSSA
