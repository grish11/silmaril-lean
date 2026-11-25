module

public import Silmaril.SSA.MLIR.SCF.While.Defs
import Silmaril.Proofs.SSA.MLIR.SCF.While.Lowering

public section

namespace Silmaril.MLIR.SCF

open Arith (Width Env)
open Silmaril.MLIR.Pure (Eval OpSignature)

variable {Op : OpSignature} {Input Result : List Width}

/-- The entry costs one CFG step. Each source tick costs two CFG steps,
including the final step through the parent continuation. An unpaired
step after the entry and complete pairs cannot return a value. -/
theorem While.lower_run_succ (loop : While Op Input Result) (evalOp : Eval Op)
    (fuel : Nat) (input : Env Input) :
    loop.lower.run evalOp (fuel + 1) input = loop.run evalOp (fuel / 2) input :=
  Proofs.MLIR.SCF.lower_run_succ loop evalOp fuel input

/-- Lowering preserves and reflects each possible returned value. -/
theorem While.lower_returns_iff (loop : While Op Input Result) (evalOp : Eval Op)
    (input : Env Input) (result : Env Result) :
    (∃ fuel, loop.lower.run evalOp fuel input = some result) ↔
      (∃ fuel, loop.run evalOp fuel input = some result) :=
  Proofs.MLIR.SCF.lower_returns_iff loop evalOp input result

/-- Source and target agree on failure to return at all finite budgets. -/
theorem While.lower_diverges_iff (loop : While Op Input Result) (evalOp : Eval Op)
    (input : Env Input) :
    loop.lower.Diverges evalOp input ↔ loop.Diverges evalOp input :=
  Proofs.MLIR.SCF.lower_diverges_iff loop evalOp input

end Silmaril.MLIR.SCF
