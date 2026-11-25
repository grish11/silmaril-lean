module

public import Silmaril.SSA.MLIR.SMT.Examples.Defs

@[expose] public section

namespace Silmaril.MLIR.SMT.Examples.Proofs

set_option backward.isDefEq.respectTransparency false in
theorem captured_eval (p : Bool) : captured.eval (.cons p .nil) = false := by
  classical
  simp only [captured, Block.eval, Context.bind, Quantifier.eval, Rhs.eval, Env.get,
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
  simp only [successor, Block.eval, Context.bind, Quantifier.eval, Rhs.eval, Env.get,
    decide_eq_true_eq, Bool.and_eq_true]
  intro n
  exact ⟨n + 1, true, rfl, rfl⟩

end Silmaril.MLIR.SMT.Examples.Proofs
