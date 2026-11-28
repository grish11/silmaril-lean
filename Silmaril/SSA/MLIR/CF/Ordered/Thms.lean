module

public import Silmaril.SSA.MLIR.CF.Ordered.Defs
import Silmaril.Proofs.SSA.MLIR.CF.Ordered.Correctness

/-! The shared-monad scheduler specializes to existing pure CF execution. -/

public section

namespace Silmaril.MLIR.CF.Ordered

open Arith (Env Width)
open Silmaril.MLIR.Pure (Eval OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result Γ : List Width}

/-- Instantiating the scheduler with `Id` and the original pure block
interpreter reproduces pure CF at every fuel and current block. -/
theorem runBlock_id (cfg : CF.Cfg Op Label Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel : Nat) (block : CF.Block Op Label Γ Result) (env : Env Γ) :
    runBlock (M := Id) cfg.block (fun code values => code.eval evalOp (fun t e => Terminator.eval e t) values)
        input fuel block env = cfg.runBlock evalOp input fuel block env :=
  Proofs.runBlock_id cfg evalOp input fuel block env

end Silmaril.MLIR.CF.Ordered
