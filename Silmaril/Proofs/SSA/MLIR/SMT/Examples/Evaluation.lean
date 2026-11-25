module

public import Silmaril.SSA.MLIR.SMT.Examples.Defs

@[expose] public section

namespace Silmaril.MLIR.SMT.Examples.Proofs

set_option backward.isDefEq.respectTransparency false in
theorem captured_eval (p : Bool) : captured.eval (.cons p .nil) = false := by
  classical
  simp only [captured, Block.eval, Context.bind, Quantifier.eval, Rhs.eval, Rhs.evalEq, Env.get,
    decide_eq_true_eq, decide_eq_false_iff_not, Bool.and_eq_true]
  intro h
  obtain ⟨y, hy, hs⟩ := h p
  change decide (y = p) = true at hy
  change y = !p at hs
  rw [decide_eq_true_eq] at hy
  rw [hy] at hs
  cases p <;> contradiction

theorem successor_eval : successor.eval .nil = true := by
  classical
  simp only [successor, Block.eval, Context.bind, Quantifier.eval, Rhs.eval, Rhs.evalEq, Env.get,
    decide_eq_true_eq, Bool.and_eq_true]
  intro n
  exact ⟨n + 1, true, rfl, rfl⟩

theorem chainedEquality_eval_iff (x y z : Int) :
    chainedEquality.eval (.cons x (.cons y (.cons z .nil))) = true ↔ x = y ∧ y = z := by
  classical
  simp only [chainedEquality, Block.eval, Rhs.eval, Rhs.evalEq, Env.get,
    Bool.and_eq_true, decide_eq_true_eq]
  rfl

theorem orderedBounds_eval (n : Int) : orderedBounds.eval (.cons n .nil) = true := by
  classical
  simp only [orderedBounds, Block.eval, Context.bind, Quantifier.eval, Rhs.eval, Rhs.evalEq,
    IntPredicate.eval, Env.get, Bool.and_eq_true, decide_eq_true_eq]
  intro x
  have h : n < x ↔ n + 1 ≤ x := by omega
  have same : decide (n < x) = decide (n + 1 ≤ x) :=
    Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using h)
  exact ⟨same.symm, same, same.symm⟩

end Silmaril.MLIR.SMT.Examples.Proofs
