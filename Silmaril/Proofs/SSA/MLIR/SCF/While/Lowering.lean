module

public import Silmaril.SSA.MLIR.SCF.While.Defs

public section

namespace Silmaril.Proofs.MLIR.SCF

open Silmaril.MLIR
open Arith (Width Env)
open Silmaril.MLIR.Pure (Code Eval OpSignature)
open Silmaril.MLIR.SCF

variable {Op : OpSignature} {Input Result Γ State Payload : List Width}

private theorem eval_before (evalOp : Eval Op) (code : Code Op (Condition Payload) Γ)
    (env : Env Γ) :
    (code.mapTerm (Condition.lower (State := State) (Result := Result))).eval evalOp
        (fun term vals => term.eval vals) env =
      let outcome := code.eval evalOp Condition.eval env
      .inl (if outcome.1 then ⟨.after, outcome.2⟩ else ⟨.exit, outcome.2⟩) := by
  induction code with
  | terminator term => cases term <;> rfl
  | letOp _ _ _ ih => exact ih _

private theorem eval_after (evalOp : Eval Op) (code : Code Op (Yield State) Γ)
    (env : Env Γ) :
    (code.mapTerm (Yield.lower (Payload := Payload) (Result := Result))).eval evalOp
        (fun term vals => term.eval vals) env =
      .inl ⟨.before, code.eval evalOp Yield.eval env⟩ := by
  induction code with
  | terminator term => cases term <;> rfl
  | letOp _ _ _ ih => exact ih _

private theorem eval_exit (evalOp : Eval Op) (code : Code Op (Return Result) Γ)
    (env : Env Γ) :
    (code.mapTerm (Return.lower (State := State) (Payload := Payload))).eval evalOp
        (fun term vals => term.eval vals) env =
      .inr (code.eval evalOp Return.eval env) := by
  induction code with
  | terminator term => cases term <;> rfl
  | letOp _ _ _ ih => exact ih _

private theorem lower_runFrom_add_two (loop : While Op Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel : Nat) (state : Env loop.State) :
    loop.lower.runFrom evalOp (fuel + 2) input ⟨.before, state⟩ =
      let outcome := loop.before.eval evalOp Condition.eval (state.append input)
      if outcome.1 then
        let next := loop.after.eval evalOp Yield.eval (outcome.2.append input)
        loop.lower.runFrom evalOp fuel input ⟨.before, next⟩
      else
        some (loop.cont.eval evalOp Return.eval (outcome.2.append input)) := by
  simp only [CF.Cfg.runFrom, CF.Cfg.runBlock, While.lower, eval_before]
  cases (loop.before.eval evalOp Condition.eval (state.append input)) with
  | mk test payload =>
    cases test <;> simp [eval_after, eval_exit]

private theorem lower_runFrom (loop : While Op Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel slack : Nat) (hslack : slack ≤ 1) (state : Env loop.State) :
    loop.lower.runFrom evalOp (2 * fuel + slack) input ⟨.before, state⟩ =
      loop.runFrom evalOp input fuel state := by
  induction fuel generalizing state with
  | zero =>
    have h : slack = 0 ∨ slack = 1 := by omega
    rcases h with rfl | rfl
    · rfl
    · simp only [While.runFrom, CF.Cfg.runFrom, CF.Cfg.runBlock, While.lower, eval_before]
  | succ fuel ih =>
    rw [show 2 * (fuel + 1) + slack = (2 * fuel + slack) + 2 by omega,
      lower_runFrom_add_two, While.runFrom]
    cases (loop.before.eval evalOp Condition.eval (state.append input)) with
    | mk test payload =>
      cases test
      · rfl
      · exact ih _

theorem lower_run_succ (loop : While Op Input Result) (evalOp : Eval Op)
    (fuel : Nat) (input : Env Input) :
    loop.lower.run evalOp (fuel + 1) input = loop.run evalOp (fuel / 2) input := by
  have h : fuel = 2 * (fuel / 2) + fuel % 2 := by omega
  let frame : CF.Frame (Label loop.State loop.Payload) := ⟨.before, loop.init.eval input⟩
  calc
    _ = loop.lower.runFrom evalOp fuel input frame := rfl
    _ = loop.lower.runFrom evalOp (2 * (fuel / 2) + fuel % 2) input frame :=
      congrArg (fun n => loop.lower.runFrom evalOp n input frame) h
    _ = _ := lower_runFrom loop evalOp input (fuel / 2) (fuel % 2) (by omega) _

theorem lower_returns_iff (loop : While Op Input Result) (evalOp : Eval Op)
    (input : Env Input) (result : Env Result) :
    (∃ fuel, loop.lower.run evalOp fuel input = some result) ↔
      (∃ fuel, loop.run evalOp fuel input = some result) := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => cases h
    | succ fuel => exact ⟨fuel / 2, (lower_run_succ loop evalOp fuel input).symm.trans h⟩
  · rintro ⟨fuel, h⟩
    refine ⟨2 * fuel + 1, (lower_run_succ loop evalOp (2 * fuel) input).trans ?_⟩
    simpa only [Nat.mul_comm 2 fuel, Nat.mul_div_cancel _ (by decide : 0 < 2)] using h

theorem lower_diverges_iff (loop : While Op Input Result) (evalOp : Eval Op)
    (input : Env Input) :
    loop.lower.Diverges evalOp input ↔ loop.Diverges evalOp input := by
  constructor
  · intro h fuel
    have heq := (lower_run_succ loop evalOp (2 * fuel) input).symm.trans (h (2 * fuel + 1))
    simpa only [Nat.mul_comm 2 fuel, Nat.mul_div_cancel _ (by decide : 0 < 2)] using heq
  · intro h fuel
    cases fuel with
    | zero => rfl
    | succ fuel => exact (lower_run_succ loop evalOp fuel input).trans (h (fuel / 2))

end Silmaril.Proofs.MLIR.SCF
