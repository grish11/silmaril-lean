module

public import Silmaril.SSA.MLIR.SCF.For.Defs
import Silmaril.Proofs.SSA.MLIR.SCF.For.Lowering

public section

namespace Silmaril.MLIR.SCF.For

open Arith (Width Env)
open Silmaril.MLIR.Pure (Eval OpSignature)

variable {Op : OpSignature} {Input Result : List Width}

/-- With positive step, precisely the indices before the trip count produce
induction values below the exclusive upper bound. -/
theorem body_index_iff (loop : For Op Input Result) (input : Env Input)
    (positive : 0 < (input.get loop.step).toNat) (j : Nat) :
    j < loop.tripCount input ↔ loop.inductionAt input j < (input.get loop.upperBound).toNat :=
  Proofs.MLIR.SCF.For.body_index_iff loop input positive j

/-- Admission ensures representability of all body induction values and the
final value used to exit the loop. -/
theorem inductionAt_fits (loop : For Op Input Result) (input : Env Input)
    (admitted : loop.Admitted input) {j : Nat} (hj : j ≤ loop.tripCount input) :
    loop.inductionAt input j < 2 ^ loop.width.val :=
  Proofs.MLIR.SCF.For.inductionAt_fits loop input admitted hj

/-- The entry uses one block, every trip uses a test and a body, and the
final test and exit consume two more blocks. At or above that budget the
CFG returns the finite denotation. -/
theorem lower_run (loop : For Op Input Result) (evalOp : Eval Op) (input : Env Input)
    (admitted : loop.Admitted input) (fuel : Nat) :
    loop.lower.run (For.lowerEval evalOp) fuel input =
      if 2 * loop.tripCount input + 3 ≤ fuel then some (loop.denote evalOp input) else none :=
  Proofs.MLIR.SCF.For.lower_run loop evalOp input admitted fuel

/-- At its first sufficient budget the CFG agrees with the executable source. -/
theorem lower_run_at (loop : For Op Input Result) (evalOp : Eval Op) (input : Env Input)
    (admitted : loop.Admitted input) :
    loop.lower.run (For.lowerEval evalOp) (2 * loop.tripCount input + 3) input =
      loop.run evalOp input := by
  rw [loop.lower_run evalOp input admitted]
  simp [For.run, admitted]

end Silmaril.MLIR.SCF.For
