module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Model.Defs

/-! # Typed exit routing for flat CFG composition -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)

universe u
variable {τ : Type u} [TypeFormers τ] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {P Q M E D : τ}

def ExitTarget.select : {X : τ} → ExitTarget M E D X → TyDen X → LabelDen [E,D] ⊕ TyDen M
  | _, .consumer, x => .inr x
  | _, .first, x => .inl (.inl x)
  | _, .second, x => .inl (.inr (.inl x))

/-- Interpret the producer's label and its dependent payload at the cut. -/
def ExitRouting.select (routing : ExitRouting P Q M E D) :
    LabelDen [P,Q] → LabelDen [E,D] ⊕ TyDen M
  | .inl x => routing.first.select x
  | .inr (.inl x) => routing.second.select x
  | .inr (.inr impossible) => nomatch impossible

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat
