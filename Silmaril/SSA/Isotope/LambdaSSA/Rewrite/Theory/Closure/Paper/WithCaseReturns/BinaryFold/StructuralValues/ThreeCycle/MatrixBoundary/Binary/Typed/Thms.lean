module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.ThreeCycle.MatrixBoundary.Binary.Typed.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.ThreeCycle.MatrixBoundary.Binary.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrixTyped

/-! # The exact BinaryFold seed applied to an arbitrary Bit request -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.MatrixBoundary.Binary

open Paper.BoundSimulation (stepArrow boundLocalMap)
open Silmaril.Calco2019.CounterSemiring.ThreeCycle (Scalar)
open Silmaril.Calco2019.CounterSemiring.ThreeCycle.Binary
  (PhaseState Weight phaseFeedback phase_feedback)

/-- The typed seed's entry forwards the same Bit after dropping its phase,
as does the candidate's function matrix for the fold. -/
theorem entry_after_fold (initial : PhaseState) :
    Paper.WithCaseReturns.Eqv false ([] : VCtx (Ty Empty))
      ((entry initial).lsubst (boundLocalMap foldTerm))
      (.br 0 (bitValue (initial.elim id id))) [BitTy, ExitTy] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrixTyped.entry_after_fold initial

/-- The candidate's matrix evaluations agree from the exact entry indices
of the typed alternating fold, for arbitrary assignments to the request row. -/
theorem matrix_entry_eq {E : Type} (r : Weight) (e : Matrix (Fin 2) E Scalar)
    (initial : PhaseState) (exit : E) :
    phaseFeedback r e initial exit =
      Silmaril.Calco2019.CounterSemiring.ThreeCycle.Binary.feedback r e (initial.elim id id) exit := by
  rw [phase_feedback]
  rfl

/-- The native step representatives admit the actual seed at every closed
initial phase and retained Bit, with a local proof in WithCaseReturns. -/
theorem alternating_instance :
    ∃ (p q : Region Op) (hp : ValueBranches [PhaseTy] p [PhaseTy, ExitTy])
      (hq : ValueBranches [BitTy] q [BitTy, ExitTy]),
      stepArrow hp = alternatingStep round ∧ stepArrow hq = round ∧
      ∀ initial, FoldStep false [] (.cfg (entry initial) 1 (fun _ => p))
        (.cfg ((entry initial).lsubst (boundLocalMap foldTerm)) 1 (fun _ => q)) [ExitTy] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrixTyped.alternating_instance

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.MatrixBoundary.Binary
