module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Capture.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Iteration.Capture.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Iteration.Preservation
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Representatives

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Iteration

open Silmaril Silmaril.Isotope
open CategoryTheory
open LambdaSSA.Region (ValueBranches)
open LambdaSSA.Region.Paper.TypeCategory (ofRegion)
open LambdaSSA.Region.SyntacticCategory (iterateRegion_valueBranches)
open LambdaSSA.UB.Overlay
open Shape.Category (arrow_ext iterateCaptured pairPayload pair_split singlePayload splitPair)
open Shape.Paper (singletonInterpretation unpackCapture_typed)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category (unpack_outcomes)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {X A B : Ty κ} {r : LambdaSSA.Region Φ}
variable (M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ)))

theorem map_unpacked_iterateRegion (hr : ValueBranches [A, X] r [.coprod B A]) :
    (singletonInterpretation M).map (ofRegion (unpackCapture_typed (iterateRegion_valueBranches hr))) =
      iterateCaptured M (.native ⟨r, hr.hasType⟩) := by
  apply arrow_ext
  intro i p s
  obtain rfl := Fin.eq_zero i
  let parts := splitPair p
  have packed : pairPayload parts.1 parts.2 = p := pair_split p
  rw [← packed]
  have unpacked := unpack_outcomes M.raw (iterateRegion_valueBranches hr).hasType
    (unpackCapture_typed (iterateRegion_valueBranches hr)).hasType parts.1.val parts.2.val s
  exact (congrArg WithTop.some unpacked).trans
    (native_iterateRegion (M.extend parts.1.property) hr parts.2 s)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Iteration
