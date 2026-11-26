module

public import Silmaril.SSA.MLIR.SCF.IndexSwitch.Defs
import Silmaril.Proofs.SSA.MLIR.SCF.IndexSwitch.Lowering

public section

namespace Silmaril.MLIR.SCF.IndexSwitch

open Arith (Width Env)
open Silmaril.MLIR.Pure (Eval OpSignature)
open CF.SwitchAssert (Outcome)

variable {Op : OpSignature} {Input Result : List Width}

/-- The flat CFG agrees with structured execution at every fuel budget,
including exhaustion before the continuation. -/
theorem Program.lower_run (program : Program Op Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel : Nat) :
    program.lower.run evalOp fuel input = (program.run evalOp input fuel).map Outcome.returned :=
  Proofs.MLIR.SCF.IndexSwitch.lower_run program evalOp input fuel

/-- Every finite return has exactly the same tuple at the same budget. -/
theorem Program.lower_returns_iff (program : Program Op Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel : Nat) (result : Env Result) :
    program.lower.run evalOp fuel input = some (.returned result) ↔
      program.run evalOp input fuel = some result := by
  simp [program.lower_run]

/-- Total straight-line operations and typed edges cannot abort. -/
theorem Program.lower_ne_aborted (program : Program Op Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel : Nat) :
    program.lower.run evalOp fuel input ≠ some .aborted := by
  simp [program.lower_run]

/-- All supported switches return after three blocks, so divergence is impossible. -/
theorem Program.lower_not_diverges (program : Program Op Input Result) (evalOp : Eval Op)
    (input : Env Input) : ¬ program.lower.Diverges evalOp input := by
  intro h
  simpa [program.lower_run, Program.run] using h 3

end Silmaril.MLIR.SCF.IndexSwitch
