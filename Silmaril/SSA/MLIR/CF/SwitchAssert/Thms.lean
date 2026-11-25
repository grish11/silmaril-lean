module

public import Silmaril.SSA.MLIR.CF.SwitchAssert.Defs
import Silmaril.Proofs.SSA.MLIR.CF.SwitchAssert.Execution

public section

namespace Silmaril.MLIR.CF.SwitchAssert

open Arith (Width Env)
open Silmaril.MLIR.Pure (Eval OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}

/-- A return or abort observed at a finite budget persists at larger budgets. -/
theorem Cfg.run_add_of_some (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel extra : Nat) (outcome : Outcome Result)
    (h : cfg.run evalOp fuel input = some outcome) :
    cfg.run evalOp (fuel + extra) input = some outcome :=
  Proofs.MLIR.CF.SwitchAssert.run_add_of_some cfg evalOp input fuel extra outcome h

/-- The embedding agrees with Basic at every fuel budget. Its only possible
terminal outcomes are the original returned tuples. -/
theorem Cfg.embed_run (cfg : CF.Cfg Op Label Input Result) (evalOp : Eval Op)
    (fuel : Nat) (input : Env Input) :
    (Cfg.embed cfg).run evalOp fuel input = (cfg.run evalOp fuel input).map Outcome.returned :=
  Proofs.MLIR.CF.SwitchAssert.embed_run cfg evalOp fuel input

/-- The embedding preserves and reflects divergence. -/
theorem Cfg.embed_diverges_iff (cfg : CF.Cfg Op Label Input Result) (evalOp : Eval Op)
    (input : Env Input) :
    (Cfg.embed cfg).Diverges evalOp input ↔ cfg.Diverges evalOp input := by
  simp only [Cfg.Diverges, CF.Cfg.Diverges, Cfg.embed_run, Option.map_eq_none_iff]

end Silmaril.MLIR.CF.SwitchAssert
