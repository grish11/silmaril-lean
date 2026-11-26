module

public import Silmaril.SSA.MLIR.SCF.For.Defs

public section

namespace Silmaril.Proofs.MLIR.SCF.For

open Silmaril.MLIR
open Arith (Width Var Env)
open Silmaril.MLIR.Pure (Code Eval Operands OpSignature)
open Silmaril.MLIR.SCF (For Yield Return)

variable {Op : OpSignature} {Input Result Γ Δ Carried : List Width} {w : Width}

theorem body_index_iff (loop : For Op Input Result) (input : Env Input)
    (positive : 0 < (input.get loop.step).toNat) (j : Nat) :
    j < loop.tripCount input ↔ loop.inductionAt input j < (input.get loop.upperBound).toNat := by
  change j + 1 ≤ loop.tripCount input ↔ _
  simp only [For.tripCount, For.inductionAt]
  rw [Nat.le_div_iff_mul_le positive, Nat.add_mul, Nat.one_mul]
  omega

theorem inductionAt_fits (loop : For Op Input Result) (input : Env Input)
    (admitted : loop.Admitted input) {j : Nat} (hj : j ≤ loop.tripCount input) :
    loop.inductionAt input j < 2 ^ loop.width.val :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _) admitted.2

private theorem inductionBits_toNat (loop : For Op Input Result) (input : Env Input)
    (admitted : loop.Admitted input) {j : Nat} (hj : j ≤ loop.tripCount input) :
    (BitVec.ofNat loop.width.val (loop.inductionAt input j)).toNat = loop.inductionAt input j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (inductionAt_fits loop input admitted hj)]

private theorem inductionBits_succ (loop : For Op Input Result) (input : Env Input)
    (admitted : loop.Admitted input) {j : Nat} (hj : j < loop.tripCount input) :
    BitVec.ofNat loop.width.val (loop.inductionAt input j) + input.get loop.step =
      BitVec.ofNat loop.width.val (loop.inductionAt input (j + 1)) := by
  apply BitVec.toNat_eq.mpr
  have hnext : j + 1 ≤ loop.tripCount input := hj
  rw [BitVec.toNat_add, inductionBits_toNat loop input admitted (Nat.le_of_lt hj),
    inductionBits_toNat loop input admitted hnext]
  rw [show loop.inductionAt input j + (input.get loop.step).toNat =
    loop.inductionAt input (j + 1) by simp [For.inductionAt, Nat.add_mul, Nat.add_assoc]]
  exact Nat.mod_eq_of_lt (inductionAt_fits loop input admitted hnext)

private theorem get_weakenVar (args : Env Δ) (input : Env Γ) (ref : Var Γ w) :
    (args.append input).get (For.weakenVar ref Δ) = input.get ref := by
  induction args with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem eval_renameOperands (rename : ∀ {w}, Var Γ w → Var Δ w)
    (source : Env Γ) (target : Env Δ)
    (hget : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    (values : Operands Γ Carried) :
    (For.renameOperands rename values).eval target = values.eval source := by
  induction values with
  | nil => rfl
  | cons _ _ ih => simp only [For.renameOperands, Operands.eval, hget, ih]

private theorem eval_rename_cons (value : BitVec w.val) (env : Env Γ) (values : Operands Γ Carried) :
    (For.renameOperands Var.there values).eval (.cons value env) = values.eval env :=
  eval_renameOperands Var.there env (.cons value env) (fun _ => rfl) values

private theorem eval_argumentOperands (args : Env Carried) (input : Env Input) :
    (For.argumentOperands Input Carried).eval (args.append input) = args := by
  induction args with
  | nil => rfl
  | cons _ _ ih =>
      simp only [For.argumentOperands, Env.append, Operands.eval, Env.get, eval_rename_cons, ih]

private theorem eval_ult (evalOp : Eval Op) (lhs rhs : BitVec w.val) :
    (For.lowerEval evalOp (.ult w) (.cons lhs (.cons rhs .nil))).getLsbD 0 = lhs.ult rhs := by
  change (BitVec.ofBool (lhs.ult rhs)).getLsbD 0 = _
  simp

private theorem eval_test (loop : For Op Input Result) (evalOp : Eval Op) (input : Env Input)
    (iv : BitVec loop.width.val) (carried : Env loop.Carried) :
    loop.lowerTest.eval (For.lowerEval evalOp) (fun term env => term.eval env)
        (.cons iv (carried.append input)) =
      .inl (if iv.ult (input.get loop.upperBound) then ⟨.body, .cons iv carried⟩ else ⟨.exit, carried⟩) := by
  have hUpper := get_weakenVar (Env.cons iv carried) input loop.upperBound
  change (Env.cons iv (carried.append input)).get
    (For.weakenVar loop.upperBound (loop.width :: loop.Carried)) = _ at hUpper
  simp only [For.lowerTest, Code.eval, Operands.eval, Env.get, hUpper,
    CF.Terminator.eval, eval_ult, CF.Edge.eval, eval_rename_cons]
  cases hTest : iv.ult (input.get loop.upperBound)
  · simp only [Bool.false_eq_true, ite_false]
    rw [eval_renameOperands (fun ref => .there (.there ref)) (carried.append input) _ (fun _ => rfl),
      eval_argumentOperands]
  · simp only [ite_true]
    exact congrArg (fun args => Sum.inl (CF.Frame.mk For.Label.body args))
      (eval_argumentOperands (Env.cons iv carried) input)

private theorem eval_body (evalOp : Eval Op) (code : Code Op (Yield Carried) Γ)
    (iv step : Var Γ w) (env : Env Γ) :
    (For.lowerBody (Result := Result) iv step code).eval (For.lowerEval evalOp)
        (fun term vals => term.eval vals) env =
      .inl ⟨.test, .cons (env.get iv + env.get step) (code.eval evalOp Yield.eval env)⟩ := by
  induction code with
  | terminator term =>
      cases term
      simp only [For.lowerBody, Code.eval, For.lowerEval, Operands.eval, Env.get, CF.Terminator.eval,
        CF.Edge.eval, Yield.eval, eval_rename_cons] <;> rfl
  | letOp _ _ _ ih => exact ih _ _ _

private theorem eval_cont (evalOp : Eval Op) (code : Code Op (Return Result) Γ) (env : Env Γ) :
    (For.lowerCont (w := w) (Carried := Carried) code).eval (For.lowerEval evalOp)
        (fun term vals => term.eval vals) env = .inr (code.eval evalOp Return.eval env) := by
  induction code with
  | terminator term => cases term <;> rfl
  | letOp _ _ _ ih => exact ih _

private theorem runFrom_one (loop : For Op Input Result) (evalOp : Eval Op) (input : Env Input)
    (iv : BitVec loop.width.val) (carried : Env loop.Carried) :
    loop.lower.runFrom (For.lowerEval evalOp) 1 input ⟨.test, .cons iv carried⟩ = none := by
  simp only [CF.Cfg.runFrom, CF.Cfg.runBlock, For.lower, Env.append, eval_test]

private theorem runFrom_add_two (loop : For Op Input Result) (evalOp : Eval Op) (input : Env Input)
    (fuel : Nat) (iv : BitVec loop.width.val) (carried : Env loop.Carried) :
    loop.lower.runFrom (For.lowerEval evalOp) (fuel + 2) input ⟨.test, .cons iv carried⟩ =
      if iv.ult (input.get loop.upperBound) then
        let next := loop.body.eval evalOp Yield.eval (.cons iv (carried.append input))
        loop.lower.runFrom (For.lowerEval evalOp) fuel input
          ⟨.test, .cons (iv + input.get loop.step) next⟩
      else some (loop.cont.eval evalOp Return.eval (carried.append input)) := by
  have hStep := get_weakenVar (Env.cons iv carried) input loop.step
  change (Env.cons iv (carried.append input)).get
    (For.weakenVar loop.step (loop.width :: loop.Carried)) = _ at hStep
  cases hTest : iv.ult (input.get loop.upperBound) <;>
    simp only [CF.Cfg.runFrom, CF.Cfg.runBlock, For.lower, Env.append, eval_test, hTest,
      Bool.false_eq_true, ite_false, ite_true, eval_body, eval_cont, Env.get, hStep]

private theorem runFrom_count (loop : For Op Input Result) (evalOp : Eval Op) (input : Env Input)
    (admitted : loop.Admitted input) (remaining j fuel : Nat) (carried : Env loop.Carried)
    (hj : j + remaining = loop.tripCount input) :
    loop.lower.runFrom (For.lowerEval evalOp) fuel input
        ⟨.test, .cons (BitVec.ofNat loop.width.val (loop.inductionAt input j)) carried⟩ =
      if 2 * remaining + 2 ≤ fuel then some (loop.denoteFrom evalOp input remaining j carried)
      else none := by
  induction remaining generalizing j fuel carried with
  | zero =>
      match fuel with
      | 0 => rfl
      | 1 => rw [runFrom_one]; rfl
      | fuel + 2 =>
          have hIndex : j ≤ loop.tripCount input := by omega
          have hBound : ¬ loop.inductionAt input j < (input.get loop.upperBound).toNat :=
            fun bound => by
              have active := (body_index_iff loop input admitted.1 j).mpr bound
              omega
          have hTest : (BitVec.ofNat loop.width.val (loop.inductionAt input j)).ult
              (input.get loop.upperBound) = false := by
            simp only [BitVec.ult, inductionBits_toNat loop input admitted hIndex, decide_eq_false hBound]
          rw [runFrom_add_two, hTest]
          simp [For.denoteFrom]
  | succ remaining ih =>
      match fuel with
      | 0 => rfl
      | 1 => rw [runFrom_one]; rfl
      | fuel + 2 =>
          have hIndex : j < loop.tripCount input := by omega
          have hBound := (body_index_iff loop input admitted.1 j).mp hIndex
          have hTest : (BitVec.ofNat loop.width.val (loop.inductionAt input j)).ult
              (input.get loop.upperBound) = true := by
            simp only [BitVec.ult, inductionBits_toNat loop input admitted (Nat.le_of_lt hIndex),
              decide_eq_true hBound]
          rw [runFrom_add_two, hTest, ite_eq_left (rfl : true = true),
            inductionBits_succ loop input admitted hIndex]
          rw [ih (j + 1) fuel _ (by omega), For.denoteFrom]
          simp only [show 2 * (remaining + 1) + 2 ≤ fuel + 2 ↔ 2 * remaining + 2 ≤ fuel by omega]

theorem lower_run (loop : For Op Input Result) (evalOp : Eval Op) (input : Env Input)
    (admitted : loop.Admitted input) (fuel : Nat) :
    loop.lower.run (For.lowerEval evalOp) fuel input =
      if 2 * loop.tripCount input + 3 ≤ fuel then some (loop.denote evalOp input) else none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      have initial : BitVec.ofNat loop.width.val (loop.inductionAt input 0) =
          input.get loop.lowerBound := by simp [For.inductionAt]
      have execution := runFrom_count loop evalOp input admitted (loop.tripCount input) 0 fuel
        (loop.init.eval input) (Nat.zero_add _)
      rw [initial] at execution
      change loop.lower.runFrom (For.lowerEval evalOp) fuel input
        ⟨.test, .cons (input.get loop.lowerBound) (loop.init.eval input)⟩ = _
      rw [execution, For.denote]
      simp only [show 2 * loop.tripCount input + 3 ≤ fuel + 1 ↔
        2 * loop.tripCount input + 2 ≤ fuel by omega]

end Silmaril.Proofs.MLIR.SCF.For
