module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Defs
public import Mathlib.Data.List.ProdSigma

/-! # Counterexamples for the native finite refinement decision -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native

open Syntax (Primitives)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {X : Syntax.Ty} {R L : List Syntax.Ty}
variable {captures seeds results states : Nat}

/-- Search the same supported starts as `check`. A witness names the
capture and initial machine state, using each CFG's own entry packet. -/
def counterexample (left right : Readback Φ X R L) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) : Option (Fin captures × Fin states) :=
  ((List.finRange captures).product (List.finRange states)).find? fun (c, s) =>
    !decide ((left.execute C prim c s).refines (right.execute C prim c s))

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native
