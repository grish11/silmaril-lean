module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.ThreeCycle.MatrixBoundary.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldMatrixBoundary

/-! # The three-cycle scalar witness misses a native constructor equation -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.MatrixBoundary

open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open Paper.TypeCategory.UnitThreeCycle (step forget)

theorem nativeRound_project :
    projectStep Seed nativeRound = request ≫ (sumIso Seed U U).hom :=
  BinaryFoldMatrixBoundary.nativeRound_project

/-- Tag erasure is a single native branch-value return of literal Unit. -/
theorem native_forget_constructor : Paper.TypeCategory.ConstructorReturn
    (forget (τ := Ty Empty) (Φ := Op)) :=
  ⟨.unit, .unit, rfl⟩

/-- The model must preserve this square with the constant Unit constructor. -/
theorem native_poll_square :
    step nativeRound ≫ coprod.map (𝟙 (Native U)) forget = forget ≫ nativeRound :=
  Paper.TypeCategory.UnitThreeCycle.native_square _ BinaryFoldMatrixBoundary.reset_input
    BinaryFoldMatrixBoundary.reset_output

/-- Native constructor uniformity already identifies these feedback arrows. -/
theorem native_poll_uniformity :
    Paper.TypeCategory.iterate (step nativeRound) = forget ≫ Paper.TypeCategory.iterate nativeRound :=
  Paper.TypeCategory.UnitThreeCycle.native_iterate _ BinaryFoldMatrixBoundary.reset_input
    BinaryFoldMatrixBoundary.reset_output

theorem typed_tripling :
    iterateSum Seed (chain request (chain request request)) = iterateSum Seed request :=
  BinaryFoldMatrixBoundary.typed_tripling

/-- The local model's scalar evaluation of doubling is valid for every
pair of recurrence and exit weights on the Unit-state fragment. -/
theorem scalar_doubling_compatible (lift : Lift) (f : Obj U ⟶ Obj Reply) :
    lift.map (iterateSum Seed (chain f f)) 0 0 = lift.map (iterateSum Seed f) 0 0 :=
  BinaryFoldMatrixBoundary.scalar_doubling_compatible lift f

/-- The candidate's square already commutes at the step matrices. -/
theorem matrix_square :
    cycleMatrix * forgetOutputMatrix = forgetMatrix * pollMatrix :=
  BinaryFoldMatrixBoundary.matrix_square

/-- The failed comparison is at feedback, where the candidate gives
the three-copy cycle and the folded step different weights. -/
theorem matrix_uniformity_ne :
    cycleFeedback cycleMatrix ≠ forgetMatrix * feedbackMatrix pollMatrix :=
  BinaryFoldMatrixBoundary.matrix_uniformity_ne

/-- All one-state step matrices agree with their doubled feedback. -/
theorem matrix_doubling (a : Weight U Reply) :
    feedbackMatrix (sequenceMatrix a a) = feedbackMatrix a :=
  BinaryFoldMatrixBoundary.matrix_doubling a

/-- BinaryFold doubling also holds on the candidate's concrete three-state matrix. -/
theorem matrix_cycle_doubling :
    cycleFeedback (cycleMatrix * cycleContinuation cycleMatrix) = cycleFeedback cycleMatrix :=
  BinaryFoldMatrixBoundary.matrix_cycle_doubling

/-- The candidate assignments cannot preserve the typed fragment. -/
theorem no_lift : IsEmpty Lift := BinaryFoldMatrixBoundary.no_lift

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.MatrixBoundary
