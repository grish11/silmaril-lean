module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Capture.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Iteration.Capture.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Iteration.Capture
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Iteration.Preservation

/-! # Native agreement for fixed-capture iteration -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open CategoryTheory
open LambdaSSA.Region (ValueBranches ContinuationContext)
open LambdaSSA.Region.Paper.TypeCategory (ofRegion)
open LambdaSSA.Region.SyntacticCategory (iterateRegion_valueBranches)
open Shape.Category (iterateCaptured)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {Γ : List (Ty κ)} {X A B : Ty κ}

/-- Interpret the installed fixed-capture CFG η iterator through the guarded
Paper quotient. The same model supplies the captures at each invocation. -/
theorem interpretCfgEta_iterateSum (M : Shape.Model.{u,v,w,x} Φ Γ)
    (f : LambdaSSA.Region.CfgEta.TypeCategory.ofType (Φ := Φ) (Γ := Γ) A ⟶
      LambdaSSA.Region.CfgEta.TypeCategory.ofType (.coprod B A)) :
    interpretHom M (LambdaSSA.Region.Paper.Hom.ofCfgEta
      (LambdaSSA.Region.CfgEta.TypeCategory.iterateSum f).hom) =
      Shape.Category.iterateSum (interpretHom M (LambdaSSA.Region.Paper.Hom.ofCfgEta f.hom)) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Iteration.interpretCfgEta_iterateSum M f

/-- The guarded Paper feedback operation with the installed exact-sum
dispatcher is sound at a fixed capture environment. -/
theorem interpret_guarded_feedback (M : Shape.Model.{u,v,w,x} Φ Γ)
    (f : (LambdaSSA.Region.Paper.fromNative (Φ := Φ) (Γ := Γ)).obj (ContinuationContext.single A) ⟶
      LambdaSSA.Region.Paper.fromNative.obj (ContinuationContext.single (.coprod B A))) :
    interpretHom M (LambdaSSA.Region.Paper.feedback (X := ContinuationContext.single A)
      (Y := ContinuationContext.single B)
      (f ≫ LambdaSSA.Region.Paper.fromNative.map (LambdaSSA.Region.SyntacticCategory.iterationDispatchHom A B))) =
      Shape.Category.iterateSum (interpretHom M f) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Iteration.interpret_guarded_feedback M f

/-- On a product input, unpack once around the native iterator representative.
The resulting empty-capture Paper arrow agrees with packed overlay iteration. -/
theorem singleton_map_unpacked_iterateRegion (M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ)))
    {r : LambdaSSA.Region Φ} (hr : ValueBranches [A, X] r [.coprod B A]) :
    (singletonInterpretation M).map (ofRegion (unpackCapture_typed (iterateRegion_valueBranches hr))) =
      iterateCaptured M (.native ⟨r, hr.hasType⟩) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Iteration.map_unpacked_iterateRegion M hr

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
