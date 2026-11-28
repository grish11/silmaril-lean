module

public import Silmaril.SSA.MLIR.CF.Ordered.Defs

public section

namespace Silmaril.MLIR.CF.Ordered.Proofs

open Arith (Env Width)
open Silmaril.MLIR.Pure (Eval OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result Γ : List Width}

theorem runBlock_id (cfg : CF.Cfg Op Label Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel : Nat) (block : CF.Block Op Label Γ Result) (env : Env Γ) :
    runBlock (M := Id) cfg.block (fun code values => code.eval evalOp (fun t e => Terminator.eval e t) values)
        input fuel block env = cfg.runBlock evalOp input fuel block env := by
  induction fuel generalizing Γ with
  | zero => rfl
  | succ fuel ih =>
    change
      (match block.eval evalOp (fun t e => Terminator.eval e t) env with
      | .inl frame => runBlock (M := Id) cfg.block
          (fun code values => code.eval evalOp (fun t e => Terminator.eval e t) values)
          input fuel (cfg.block frame.label) (frame.args.append input)
      | .inr result => some result) = _
    rw [CF.Cfg.runBlock]
    cases block.eval evalOp (fun term vals => Terminator.eval vals term) env with
    | inl frame => exact ih (cfg.block frame.label) (frame.args.append input)
    | inr _ => rfl

end Silmaril.MLIR.CF.Ordered.Proofs
