module

public import Silmaril.SSA.MLIR.CF.SwitchAssert.Defs

public section

namespace Silmaril.Proofs.MLIR.CF.SwitchAssert

open Silmaril.MLIR
open Arith (Width Env)
open Silmaril.MLIR.Pure (Eval OpSignature)
open CF.SwitchAssert (Block Cfg Outcome)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result Γ : List Width}

private theorem eval_embed (evalOp : Eval Op) (block : CF.Block Op Label Γ Result)
    (env : Env Γ) :
    (Block.embed block).eval evalOp env =
      some (block.eval evalOp (fun term vals => term.eval vals) env) := by
  induction block with
  | terminator => rfl
  | letOp _ _ _ ih => exact ih _

private theorem runBlock_embed (cfg : CF.Cfg Op Label Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel : Nat) (block : CF.Block Op Label Γ Result) (env : Env Γ) :
    (Cfg.embed cfg).runBlock evalOp input fuel (Block.embed block) env =
      (cfg.runBlock evalOp input fuel block env).map Outcome.returned := by
  induction fuel generalizing Γ with
  | zero => rfl
  | succ _ ih =>
      simp only [Cfg.runBlock, CF.Cfg.runBlock, eval_embed]
      cases block.eval evalOp (fun term vals => term.eval vals) env with
      | inl next => exact ih (cfg.block next.label) (next.args.append input)
      | inr _ => rfl

theorem embed_run (cfg : CF.Cfg Op Label Input Result) (evalOp : Eval Op)
    (fuel : Nat) (input : Env Input) :
    (Cfg.embed cfg).run evalOp fuel input = (cfg.run evalOp fuel input).map Outcome.returned :=
  runBlock_embed cfg evalOp input fuel cfg.entry input

private theorem runBlock_add_of_some (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel extra : Nat) (block : Block Op Label Result Γ) (env : Env Γ)
    (outcome : Outcome Result) (h : cfg.runBlock evalOp input fuel block env = some outcome) :
    cfg.runBlock evalOp input (fuel + extra) block env = some outcome := by
  induction fuel generalizing Γ with
  | zero => simp [Cfg.runBlock] at h
  | succ _ ih =>
      simp only [Nat.succ_add, Cfg.runBlock] at h ⊢
      cases step : block.eval evalOp env with
      | none => simpa only [step] using h
      | some branch =>
          cases branch with
          | inl next =>
              simp only [step] at h
              exact ih (cfg.block next.label) (next.args.append input) h
          | inr _ => simpa only [step] using h

theorem run_add_of_some (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel extra : Nat) (outcome : Outcome Result)
    (h : cfg.run evalOp fuel input = some outcome) :
    cfg.run evalOp (fuel + extra) input = some outcome :=
  runBlock_add_of_some cfg evalOp input fuel extra cfg.entry input outcome h

end Silmaril.Proofs.MLIR.CF.SwitchAssert
