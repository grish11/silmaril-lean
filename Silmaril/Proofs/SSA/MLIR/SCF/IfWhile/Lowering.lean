module

public import Silmaril.SSA.MLIR.SCF.IfWhile.Defs

public section

namespace Silmaril.Proofs.MLIR.SCF.IfWhile

open Silmaril.MLIR
open Silmaril.MLIR.SCF hiding Label
open Silmaril.MLIR.SCF.IfWhile
open Arith (Width Env)
open Silmaril.MLIR.Pure (Code Eval Operands OpSignature)

variable {Op : OpSignature} {Input Joined Result Γ Δ Θ : List Width}
variable {Dest : List Width → Type}

private theorem eval_weaken {w : Width} (vals : Operands Γ Δ) (env : Env Γ) (word : BitVec w.val) :
    (weakenOperands vals).eval (.cons word env) = vals.eval env := by
  induction vals with
  | nil => rfl
  | cons _ _ ih => simp only [weakenOperands, Operands.eval, Env.get, ih]

private theorem eval_append (head : Operands Γ Δ) (tail : Operands Γ Θ) (env : Env Γ) :
    (appendOperands head tail).eval env = (head.eval env).append (tail.eval env) := by
  induction head with
  | nil => rfl
  | cons _ _ ih => simp only [appendOperands, Operands.eval, Env.append, ih]

private theorem eval_front (head : Env Δ) (tail : Env Γ) :
    (frontOperands Δ).eval (head.append tail) = head := by
  induction head with
  | nil => rfl
  | cons _ _ ih => simp only [frontOperands, Env.append, Operands.eval, Env.get, eval_weaken, ih]

private theorem eval_capture (head : Env Δ) (captures : Env Θ) (input : Env Γ) :
    (captureOperands Δ Θ).eval ((head.append captures).append input) = captures := by
  induction head with
  | nil => exact eval_front captures input
  | cons _ _ ih => simp only [captureOperands, Env.append, eval_weaken, ih]

private theorem eval_map {Term : List Width → Type} {α : Type} (evalOp : Eval Op)
    (trans : ∀ {Ξ}, Term Ξ → CF.Terminator Dest Result Ξ)
    (evalTerm : ∀ {Ξ}, Term Ξ → Env Ξ → α) (finish : α → CF.Frame Dest ⊕ Env Result)
    (h : ∀ {Ξ} (term : Term Ξ) (scope : Env Ξ),
      (trans term).eval scope = finish (evalTerm term scope))
    (code : Code Op Term Γ) (env : Env Γ) :
    (code.mapTerm trans).eval evalOp (fun term scope => term.eval scope) env =
      finish (code.eval evalOp evalTerm env) := by
  induction code with
  | terminator term => exact h term env
  | letOp _ _ _ ih => exact ih _

private theorem eval_map_captures {Term : List Width → Type} {α : Type} (evalOp : Eval Op)
    (trans : ∀ {Ξ}, Term Ξ → Operands Ξ Δ → CF.Terminator Dest Result Ξ)
    (evalTerm : ∀ {Ξ}, Term Ξ → Env Ξ → α)
    (finish : Env Δ → α → CF.Frame Dest ⊕ Env Result)
    (h : ∀ {Ξ} (term : Term Ξ) (vals : Operands Ξ Δ) (scope : Env Ξ),
      (trans term vals).eval scope = finish (vals.eval scope) (evalTerm term scope))
    (code : Code Op Term Γ) (vals : Operands Γ Δ) (env : Env Γ) :
    (mapWithCaptures trans code vals).eval evalOp (fun term scope => term.eval scope) env =
      finish (vals.eval env) (code.eval evalOp evalTerm env) := by
  induction code with
  | terminator term => exact h term vals env
  | letOp op args _ ih =>
    simpa only [mapWithCaptures, Code.eval, eval_weaken] using
      ih (weakenOperands vals) (.cons (evalOp op (args.eval env)) env)

private theorem eval_yield (evalOp : Eval Op) (code : Code Op (Yield Δ) Γ)
    (dest : Dest Δ) (env : Env Γ) :
    (code.mapTerm (lowerYield (Result := Result) dest)).eval evalOp
        (fun term scope => term.eval scope) env =
      .inl ⟨dest, code.eval evalOp Yield.eval env⟩ := by
  refine eval_map evalOp (lowerYield dest) Yield.eval (fun values => .inl ⟨dest, values⟩) ?_ code env
  intro _ term scope
  cases term <;> rfl

private theorem eval_enter (evalOp : Eval Op) (code : Code Op (Enter Δ Θ) Γ)
    (dest : Dest (Δ ++ Θ)) (env : Env Γ) :
    (code.mapTerm (lowerEnter (Result := Result) dest)).eval evalOp
        (fun term scope => term.eval scope) env =
      let values := code.eval evalOp Enter.eval env
      .inl ⟨dest, values.1.append values.2⟩ := by
  refine eval_map evalOp (lowerEnter dest) Enter.eval
    (fun pair => .inl ⟨dest, pair.1.append pair.2⟩) ?_ code env
  intro _ term scope
  simp only [lowerEnter, CF.Terminator.eval, CF.Edge.eval, Enter.eval, eval_append]

private theorem eval_condition (evalOp : Eval Op) (code : Code Op (Condition Δ) Γ)
    (yes no : Dest (Δ ++ Θ)) (vals : Operands Γ Θ) (env : Env Γ) :
    (mapWithCaptures (lowerCondition (Result := Result) yes no) code vals).eval evalOp
        (fun term scope => term.eval scope) env =
      let outcome := code.eval evalOp Condition.eval env
      let args := outcome.2.append (vals.eval env)
      .inl (if outcome.1 then ⟨yes, args⟩ else ⟨no, args⟩) := by
  refine eval_map_captures evalOp (lowerCondition yes no) Condition.eval
    (fun captures outcome =>
      .inl (if outcome.1 then ⟨yes, outcome.2.append captures⟩
        else ⟨no, outcome.2.append captures⟩)) ?_ code vals env
  intro _ term captures scope
  cases term
  simp only [lowerCondition, CF.Terminator.eval, CF.Edge.eval, Condition.eval, eval_append]
  split <;> simp_all

private theorem eval_backedge (evalOp : Eval Op) (code : Code Op (Yield Δ) Γ)
    (dest : Dest (Δ ++ Θ)) (vals : Operands Γ Θ) (env : Env Γ) :
    (mapWithCaptures (lowerBackedge (Result := Result) dest) code vals).eval evalOp
        (fun term scope => term.eval scope) env =
      .inl ⟨dest, (code.eval evalOp Yield.eval env).append (vals.eval env)⟩ := by
  refine eval_map_captures evalOp (lowerBackedge dest) Yield.eval
    (fun captures values => .inl ⟨dest, values.append captures⟩) ?_ code vals env
  intro _ term captures scope
  cases term
  simp only [lowerBackedge, CF.Terminator.eval, CF.Edge.eval, Yield.eval, eval_append]

private theorem eval_return (evalOp : Eval Op) (code : Code Op (Return Result) Γ) (env : Env Γ) :
    (code.mapTerm (lowerReturn (Dest := Dest))).eval evalOp (fun term scope => term.eval scope) env =
      .inr (code.eval evalOp Return.eval env) := by
  refine eval_map evalOp lowerReturn Return.eval Sum.inr ?_ code env
  intro _ term scope
  cases term <;> rfl

private theorem step (cfg : CF.Cfg Op Dest Input Result) (evalOp : Eval Op) (input : Env Input)
    (fuel : Nat) (frame : CF.Frame Dest) :
    cfg.runFrom evalOp (fuel + 1) input frame =
      match (cfg.block frame.label).eval evalOp (fun term scope => term.eval scope)
          (frame.args.append input) with
      | .inl next => cfg.runFrom evalOp fuel input next
      | .inr result => some result := by
  simp only [CF.Cfg.runFrom, CF.Cfg.runBlock]
  cases (cfg.block frame.label).eval evalOp (fun term scope => term.eval scope)
    (frame.args.append input) <;> rfl

private theorem lower_loop (cfg : CF.Cfg Op Dest Input Result) (evalOp : Eval Op)
    (input : Env Input) (body : LoopArm Op Input Joined)
    (inject : ∀ {args}, (Arm.loop body).layout.Label args → Dest args) (join : Dest Joined)
    (hblock : ∀ {args} (label : (Arm.loop body).layout.Label args),
      cfg.block (inject label) = (Arm.loop body).lowerBlock inject join label)
    (captures : Env body.Captures) (fuel : Nat) (state : Env body.State) :
    cfg.runFrom evalOp fuel input ⟨inject .before, state.append captures⟩ =
      (body.runLoop evalOp input captures fuel state).bind
        (fun (values, rest) => cfg.runFrom evalOp rest input ⟨join, values⟩) := by
  induction fuel using Nat.strongRecOn generalizing state with
  | ind fuel ih =>
    cases fuel with
    | zero => rfl
    | succ remaining =>
      simp only [step, hblock, Arm.lowerBlock, eval_condition, eval_capture]
      cases h : (body.before.eval evalOp Condition.eval ((state.append captures).append input)) with
      | mk test payload =>
        cases remaining with
        | zero => cases test <;> rfl
        | succ fuel =>
          cases test
          · simp only [Bool.false_eq_true, ↓reduceIte, LoopArm.runLoop, h, step, hblock,
              Arm.lowerBlock, eval_yield, Option.bind_some]
          · simp only [↓reduceIte, LoopArm.runLoop, h, step, hblock, Arm.lowerBlock,
              eval_backedge, eval_capture]
            exact ih fuel (by omega) _

private theorem lower_arm (cfg : CF.Cfg Op Dest Input Result) (evalOp : Eval Op)
    (input : Env Input) (arm : Arm Op Input Joined)
    (inject : ∀ {args}, arm.layout.Label args → Dest args) (join : Dest Joined)
    (hblock : ∀ {args} (label : arm.layout.Label args),
      cfg.block (inject label) = arm.lowerBlock inject join label) (fuel : Nat) :
    cfg.runFrom evalOp fuel input ⟨inject .entry, .nil⟩ =
      (arm.run evalOp input fuel).bind
        (fun (values, rest) => cfg.runFrom evalOp rest input ⟨join, values⟩) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp only [step, hblock]
    cases arm with
    | straight body => simp only [Env.append, Arm.lowerBlock, eval_yield, Arm.run, Option.bind_some]
    | loop body =>
      simp only [Env.append, Arm.lowerBlock, eval_enter, Arm.run]
      cases (body.setup.eval evalOp Enter.eval input) with
      | mk state captures => exact lower_loop cfg evalOp input body inject join hblock captures fuel state

private theorem lower_join (program : Program Op Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel : Nat) (values : Env program.Joined) :
    program.lower.runFrom evalOp fuel input ⟨.join, values⟩ =
      program.runJoin evalOp input values fuel := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [step, Program.lower, eval_return, Program.runJoin]

theorem lower_run (program : Program Op Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel : Nat) :
    program.lower.run evalOp fuel input = program.run evalOp input fuel := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    change program.lower.runFrom evalOp fuel input
      (if (input.get program.test).getLsbD 0 then ⟨.onTrue .entry, .nil⟩ else ⟨.onFalse .entry, .nil⟩) = _
    rw [Program.run]
    split
    · rw [lower_arm program.lower evalOp input program.onTrue Label.onTrue .join (fun _ => rfl)]
      simp only [lower_join]
    · rw [lower_arm program.lower evalOp input program.onFalse Label.onFalse .join (fun _ => rfl)]
      simp only [lower_join]

end Silmaril.Proofs.MLIR.SCF.IfWhile
