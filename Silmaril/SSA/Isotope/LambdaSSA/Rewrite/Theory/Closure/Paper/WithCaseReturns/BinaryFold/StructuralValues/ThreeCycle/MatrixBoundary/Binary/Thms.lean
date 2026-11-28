module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.ThreeCycle.MatrixBoundary.Binary.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrix

/-! # The matrix equation for alternating feedback on Bit -/

public section

namespace Silmaril.Calco2019.CounterSemiring.ThreeCycle.Binary

/-- The pure constructor fold preserves the local exits and commutes with
the repeat block of the candidate's matrix square. -/
theorem matrix_square {E : Type} (r : Weight) (e : Matrix Bit E Scalar) :
    duplicate e = foldMatrix * e ∧ alternating r * foldMatrix = foldMatrix * r :=
  ⟨(Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrix.fold_output e).symm,
    Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrix.fold_recurrence r⟩

/-- The model candidate validates two-round grouping for every weighted
Bit row, with any set of exit columns. -/
theorem feedback_double {E : Type} (r : Weight) (e : Matrix Bit E Scalar) :
    feedback (r * r) (e + r * e) = feedback r e :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrix.feedback_double r e

/-- Actual four-state elimination agrees with the two-state feedback
when both phases run the retained row and only recurrence switches phase. -/
theorem phase_feedback {E : Type} (r : Weight) (e : Matrix Bit E Scalar) :
    phaseFeedback r e = duplicate (feedback r e) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrix.phase_feedback r e

/-- The two written matrix feedback endpoints of the alternating seed
agree under the function matrix of the pure fold. -/
theorem phase_fold {E : Type} (r : Weight) (e : Matrix Bit E Scalar) :
    phaseFeedback r e = foldMatrix * feedback r e :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrix.phase_fold r e

end Silmaril.Calco2019.CounterSemiring.ThreeCycle.Binary
