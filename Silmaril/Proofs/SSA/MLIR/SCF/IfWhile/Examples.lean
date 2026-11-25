module

import Silmaril.SSA.MLIR.SCF.IfWhile.Thms

/-! Closed checks for both branches, arm-local captures, and nested divergence. -/

namespace Silmaril.MLIR.SCF.IfWhile.Examples

open Arith (Width Env)
open Silmaril.MLIR.Pure (Eval i1)

private def i8 : Width := ⟨8, by decide⟩
private def i16 : Width := ⟨16, by decide⟩

private inductive Op : List Width → Width → Type where
  | double : Op [i8] i8
  | zero : Op [] i8
  | lt : Op [i8, i8] i1
  | trueBit : Op [] i1
  | widen : Op [i8] i16
  | step : Op [i16, i8] i8
  | add : Op [i16, i8] i16

private def evalOp : Eval Op
  | _, _, .double, .cons n .nil => n + n
  | _, _, .zero, .nil => 0
  | _, _, .lt, .cons x (.cons y .nil) => if x.toNat < y.toNat then 1 else 0
  | _, _, .trueBit, .nil => 1
  | _, _, .widen, .cons n .nil => BitVec.ofNat 16 n.toNat
  | _, _, .step, .cons n (.cons limit .nil) =>
    BitVec.ofNat 8 (n.toNat + (if limit.toNat % 2 = 0 then 1 else 2))
  | _, _, .add, .cons n (.cons offset .nil) => n + BitVec.ofNat i16.val offset.toNat

/-- Bind the capture to twice the parent's input. Compare the counter against
this limit, forward a wider payload, and use the capture in the after
region and the arm tail. -/
private def count : LoopArm Op [i1, i8] [i16] where
  State := [i8]
  Payload := [i16]
  Captures := [i8]
  setup :=
    .letOp .double (.cons (.there .here) .nil) <|
    .letOp .zero .nil <|
    .terminator ⟨.cons .here .nil, .cons (.there .here) .nil⟩
  before :=
    .letOp .lt (.cons .here (.cons (.there .here) .nil)) <|
    .letOp .widen (.cons (.there .here) .nil) <|
    .terminator (.condition (.there .here) (.cons .here .nil))
  after :=
    .letOp .step (.cons .here (.cons (.there .here) .nil)) <|
    .terminator (.yield (.cons .here .nil))
  tail :=
    .letOp .add (.cons .here (.cons (.there .here) .nil)) <|
    .terminator (.yield (.cons .here .nil))

private def loopForever : LoopArm Op [i1, i8] [i16] := { count with
  before :=
    .letOp .trueBit .nil <|
    .letOp .widen (.cons (.there .here) .nil) <|
    .terminator (.condition (.there .here) (.cons .here .nil))
}

private def mixed : Program Op [i1, i8] [i16] where
  Joined := [i16]
  test := .here
  onTrue := .loop count
  onFalse := .straight
    (.letOp .widen (.cons (.there .here) .nil) (.terminator (.yield (.cons .here .nil))))
  cont :=
    .letOp .add (.cons .here (.cons (.there (.there .here)) .nil)) <|
    .terminator (.ret (.cons .here .nil))

private def bothLoops : Program Op [i1, i8] [i16] := { mixed with
  onFalse := .loop loopForever
}

private def trueInput : Env [i1, i8] := .cons 1 (.cons 1 .nil)
private def falseInput : Env [i1, i8] := .cons 0 (.cons 1 .nil)

/-- The terminating loop takes two backedges. One final tick is needed
after the arm yields to execute the shared continuation. -/
example : mixed.run evalOp trueInput 8 = none := rfl
example : mixed.lower.run evalOp 8 trueInput = none := rfl
example : mixed.run evalOp trueInput 9 = some (.cons 5 .nil) := rfl
example : mixed.lower.run evalOp 9 trueInput = some (.cons 5 .nil) := rfl

example : mixed.run evalOp falseInput 3 = some (.cons 2 .nil) := rfl
example : mixed.lower.run evalOp 3 falseInput = some (.cons 2 .nil) := rfl

/-- The two arms can allocate the same loop profiles independently.
Selecting the terminating arm still returns with a divergent sibling. -/
example : bothLoops.run evalOp trueInput 9 = some (.cons 5 .nil) := rfl
example : bothLoops.lower.run evalOp 9 trueInput = some (.cons 5 .nil) := rfl

private theorem loopForever_noYield (fuel : Nat) (state : Env loopForever.State)
    (captures : Env loopForever.Captures) :
    loopForever.runLoop evalOp falseInput captures fuel state = none := by
  induction fuel using Nat.strongRecOn generalizing state with
  | ind fuel ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
        have htrue :
            (loopForever.before.eval evalOp SCF.Condition.eval
              ((state.append captures).append falseInput)).1 = true := by
          simp only [loopForever, Pure.Code.eval, SCF.Condition.eval, evalOp, Env.get, Pure.Operands.eval]
          decide
        rw [LoopArm.runLoop]
        cases h : (loopForever.before.eval evalOp SCF.Condition.eval
          ((state.append captures).append falseInput)) with
        | mk test payload =>
          have htest : test = true := (congrArg Prod.fst h).symm.trans htrue
          simp only [htest, ↓reduceIte]
          exact ih fuel (by omega) _

private theorem bothLoops_false_diverges : bothLoops.Diverges evalOp falseInput := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      let captures : Env loopForever.Captures := .cons 2 .nil
      let state : Env loopForever.State := .cons 0 .nil
      change (loopForever.runLoop evalOp falseInput captures fuel state).bind _ = none
      rw [loopForever_noYield fuel state captures]
      rfl

example : bothLoops.lower.Diverges evalOp falseInput :=
  (bothLoops.lower_diverges_iff evalOp falseInput).2 bothLoops_false_diverges

end Silmaril.MLIR.SCF.IfWhile.Examples
