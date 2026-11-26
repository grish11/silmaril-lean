module

public import Silmaril.SSA.MLIR.SCF.IndexSwitch.Defs

public section

namespace Silmaril.Proofs.MLIR.SCF.IndexSwitch

open Silmaril.MLIR
open Arith (Width Env)
open Silmaril.MLIR.Pure (Code Eval Operands OpSignature)
open SCF.IndexSwitch (Arm CaseValue Program)
open CF.SwitchAssert (Block Cfg Outcome Switch Terminator)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result Γ Yielded : List Width}

private theorem eval_arm (arm : Arm Op Γ Yielded) (join : Label Yielded)
    (evalOp : Eval Op) (env : Env Γ) :
    (Block.embed (arm.mapTerm (fun args => .br ⟨join, args⟩)) : Block Op Label Result Γ).eval
        evalOp env =
      some (.inl ⟨join, arm.eval evalOp (fun args scope => args.eval scope) env⟩) := by
  induction arm with
  | terminator => rfl
  | letOp _ _ _ ih => exact ih _

private theorem eval_cont (cont : Code Op (fun Δ => Operands Δ Result) Γ)
    (evalOp : Eval Op) (env : Env Γ) :
    (Block.embed (cont.mapTerm CF.Terminator.ret) : Block Op Label Result Γ).eval evalOp env =
      some (.inr (cont.eval evalOp (fun args scope => args.eval scope) env)) := by
  induction cont with
  | terminator => rfl
  | letOp _ _ _ ih => exact ih _

private theorem run_dispatch (program : Program Op Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel : Nat) :
    program.lower.run evalOp (fuel + 1) input =
      program.lower.runBlock evalOp input fuel
        (Block.embed ((program.selectArm input).mapTerm (fun args => .br ⟨.join, args⟩))) input := by
  let flag := input.get program.selector
  let caseTest := fun (entry : CaseValue × Arm Op Input program.Yielded) =>
    decide (entry.1.toInt = flag.toInt)
  have sourceFind : program.cases.find? caseTest =
      (program.cases.attach.find? (caseTest ∘ Subtype.val)).map Subtype.val := by
    rw [← List.find?_map, List.attach_map_subtype_val]
  have sameTest : (fun entry : {entry // entry ∈ program.cases} => entry.val.1 == flag) =
      caseTest ∘ Subtype.val := by
    funext entry
    simp [caseTest, Bool.beq_eq_decide_eq, BitVec.toInt_inj]
  simp only [Cfg.run, Cfg.runBlock, Program.lower, Block.eval, Terminator.eval, Switch.select,
    Program.selectArm, List.find?_map, Function.comp_def]
  rw [sourceFind, sameTest]
  cases program.cases.attach.find? (caseTest ∘ Subtype.val) <;> rfl

theorem lower_run (program : Program Op Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel : Nat) :
    program.lower.run evalOp fuel input = (program.run evalOp input fuel).map Outcome.returned := by
  match fuel with
  | 0 => rfl
  | 1 => rw [run_dispatch]; rfl
  | 2 => rw [run_dispatch, Cfg.runBlock, eval_arm]; rfl
  | k + 3 =>
      rw [run_dispatch]
      simp only [Cfg.runBlock, eval_arm, Program.lower, eval_cont, Program.run, Program.eval,
        Option.map_some]

end Silmaril.Proofs.MLIR.SCF.IndexSwitch
