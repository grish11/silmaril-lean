module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCall.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallITree

/-! # Observe the original quotient arrow in the free ITree model -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample

open CategoryTheory
open Paper.WithComputedCallReturns.Example.ITree (PayloadValue)

/-- The original guarded arrow makes the two distinct requests once and in
order, passes the first reply to the second request, and returns the capture. -/
theorem source_visible (x : PayloadValue) :
    (treeInterpretation.map sourceArrow).of x = expected x :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallITree.source_visible x

/-- The explicit sequence has the same interpretation at the retained pair
boundary. -/
theorem retained_images_eq : treeInterpretation.map sourceArrow = treeInterpretation.map explicitArrow :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallITree.retained_images_eq

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample
