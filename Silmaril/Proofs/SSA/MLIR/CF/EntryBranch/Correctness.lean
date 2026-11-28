module

public import Silmaril.SSA.MLIR.CF.EntryBranch.Defs

public section

namespace Silmaril.MLIR.CF.EntryBranch.Proofs

open Arith (Width Env)
open Silmaril.MLIR.Pure (OpSignature Eval)

variable {Op : OpSignature} {Arms : Bool → List Width → Type} {Input Result Γ : List Width}

private def liftFrame (side : Bool) (frame : Frame (Arms side)) : Frame (Label Arms) :=
  ⟨.body side frame.label, frame.args⟩

private theorem eval_term (side : Bool) (term : Terminator (Arms side) Result Γ) (env : Env Γ) :
    (terminator side term).eval env = (term.eval env).map (liftFrame side) id := by
  cases term with
  | br dest => rfl
  | ret values => rfl
  | condBr test yes no =>
    cases read : (env.get test).getLsbD 0 <;> simp [terminator, Terminator.eval, read] <;> rfl

private theorem eval_block (evalOp : Eval Op) (side : Bool)
    (block : Block Op (Arms side) Γ Result) (env : Env Γ) :
    (block.mapTerm (terminator side)).eval evalOp (fun term vals => Terminator.eval vals term) env =
      (block.eval evalOp (fun term vals => Terminator.eval vals term) env).map (liftFrame side) id := by
  induction block with
  | terminator term => exact eval_term side term env
  | letOp op operands rest ih => exact ih _

private theorem run_block (guard : Block Op (Label Arms) Input Result)
    (arms : ∀ side, Cfg Op (Arms side) Input Result) (evalOp : Eval Op)
    (input : Env Input) (side : Bool) (fuel : Nat)
    (block : Block Op (Arms side) Γ Result) (env : Env Γ) :
    (link guard arms).runBlock evalOp input fuel (block.mapTerm (terminator side)) env =
      (arms side).runBlock evalOp input fuel block env := by
  induction fuel generalizing Γ with
  | zero => rfl
  | succ fuel ih =>
    rw [Cfg.runBlock, Cfg.runBlock, eval_block]
    cases observed : block.eval evalOp (fun term vals => Terminator.eval vals term) env with
    | inl next => exact ih ((arms side).block next.label) (next.args.append input)
    | inr result => rfl

theorem run_entry (guard : Block Op (Label Arms) Input Result)
    (arms : ∀ side, Cfg Op (Arms side) Input Result) (evalOp : Eval Op)
    (input : Env Input) (side : Bool)
    (selected : guard.eval evalOp (fun term vals => Terminator.eval vals term) input = .inl ⟨.entry side, .nil⟩)
    (fuel : Nat) :
    (link guard arms).run evalOp (fuel + 1) input = (arms side).run evalOp fuel input := by
  rw [Cfg.run, Cfg.runBlock]
  have entry : (link guard arms).entry = guard := rfl
  rw [entry, selected]
  exact run_block guard arms evalOp input side fuel (arms side).entry input

end Silmaril.MLIR.CF.EntryBranch.Proofs
