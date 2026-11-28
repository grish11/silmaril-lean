module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingUnaryProducer.Separation
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingUnaryProducer.ITree

/-! # Unary lowering separates on the existing two-request producer -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Example

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open Paper.WithComputedCallReturns.Example (sequenced_typed)
open Paper.WithComputedCallReturns.Example.ITree (PayloadValue)
open Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample (expected)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example
  (Seed sourceArrow explicitArrow treeInterpretation)
open Paper.Extension.Singleton (ofRegion)
open Paper.RetainedLet (returnOnce_typed)
open CfgEta.TypeCategory (returnRegion_typed)

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example (retained_eq explicit_visible)

/-- The exact lowered and single-bind producer returns are distinct in the
unchanged computed-call quotient. -/
theorem root_ne :
    ofRegion Seed (returnRegion_typed sequenced_typed) ≠ ofRegion Seed (returnOnce_typed sequenced_typed) :=
  TriplingUnaryProducer.root_ne

/-- The distinction survives the same typed continuation that keeps the input. -/
theorem retained_ne : explicitArrow ≠ singleBindArrow :=
  TriplingUnaryProducer.retained_ne

/-- The original source arrow is consequently distinct from the written
single-bind arrow, although the computed-call seed identifies it with the
lowered one. -/
theorem source_ne : sourceArrow ≠ singleBindArrow :=
  fun h => retained_ne (retained_eq.symm.trans h)

/-- The two exact arrows agree in the supported free ITree interpretation. -/
theorem retained_images_eq : treeInterpretation.map explicitArrow = treeInterpretation.map singleBindArrow :=
  TriplingUnaryProducer.retained_images_eq

/-- The original computed-call source and the written single bind have
the same ITree denotation at their retained interface. -/
theorem source_images_eq : treeInterpretation.map sourceArrow = treeInterpretation.map singleBindArrow :=
  (congrArg treeInterpretation.map retained_eq).trans retained_images_eq

/-- The actual single-bind arrow makes the same two requests as the original
source. The first reply is the second operand, and the original input is kept. -/
theorem single_bind_visible (x : PayloadValue) : (treeInterpretation.map singleBindArrow).of x = expected x :=
  retained_images_eq ▸ explicit_visible x

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Example
