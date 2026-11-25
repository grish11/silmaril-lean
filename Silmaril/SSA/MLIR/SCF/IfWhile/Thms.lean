module

public import Silmaril.SSA.MLIR.SCF.IfWhile.Defs
import Silmaril.Proofs.SSA.MLIR.SCF.IfWhile.Lowering

public section

namespace Silmaril.MLIR.SCF.IfWhile

open Arith (Width Env)
open Silmaril.MLIR.Pure (Eval OpSignature)

variable {Op : OpSignature} {Input Result : List Width}

/-- Source and target return the same optional tuple at every budget.
The test, selected arm entry, and shared continuation each cost one tick.
A before visit and its selected successor together cost two ticks. -/
theorem Program.lower_run (program : Program Op Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel : Nat) :
    program.lower.run evalOp fuel input = program.run evalOp input fuel :=
  Proofs.MLIR.SCF.IfWhile.lower_run program evalOp input fuel

/-- A result tuple is returned at some finite budget on either side exactly
when it is returned on the other side. -/
theorem Program.lower_returns_iff (program : Program Op Input Result) (evalOp : Eval Op)
    (input : Env Input) (result : Env Result) :
    (∃ fuel, program.lower.run evalOp fuel input = some result) ↔
      (∃ fuel, program.run evalOp input fuel = some result) := by
  simp only [program.lower_run]

/-- Lowering preserves and reflects failure to return at every finite budget. -/
theorem Program.lower_diverges_iff (program : Program Op Input Result) (evalOp : Eval Op)
    (input : Env Input) :
    program.lower.Diverges evalOp input ↔ program.Diverges evalOp input := by
  simp only [CF.Cfg.Diverges, Program.Diverges, program.lower_run]

end Silmaril.MLIR.SCF.IfWhile
