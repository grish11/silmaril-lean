module

public import Silmaril.SSA.MLIR.SMT.Examples.Defs
public import Silmaril.SSA.MLIR.SMT.Thms
import Silmaril.Proofs.SSA.MLIR.SMT.Examples.Evaluation

@[expose] public section

namespace Silmaril.MLIR.SMT.Examples

open Silmaril.Logic.Smt.Uflia

theorem captured_eval (p : Bool) : captured.eval (.cons p .nil) = false :=
  Proofs.captured_eval p

theorem captured_not_holds (p : Bool) :
    ¬ Quantified.Formula.Holds captured.toFormula model (Env.cons p .nil).toSmt := by
  rw [captured.toFormula_holds_iff, captured_eval]
  decide

theorem successor_eval : successor.eval .nil = true := Proofs.successor_eval

theorem successor_holds : Quantified.Sentence.Holds successor.toFormula model :=
  (successor.toFormula_holds_iff .nil).mpr successor_eval

theorem chainedEquality_holds_iff (x y z : Int) :
    Quantified.Formula.Holds chainedEquality.toFormula model
      (Env.cons x (.cons y (.cons z .nil))).toSmt ↔ x = y ∧ y = z :=
  (chainedEquality.toFormula_holds_iff _).trans (Proofs.chainedEquality_eval_iff x y z)

theorem orderedBounds_holds (n : Int) :
    Quantified.Formula.Holds orderedBounds.toFormula model (Env.cons n .nil).toSmt :=
  (orderedBounds.toFormula_holds_iff _).mpr (Proofs.orderedBounds_eval n)

/-- An integer argument cannot be used as a Boolean reference. -/
theorem wrong_sort_unavailable : IsEmpty (Var [.int] .bool) :=
  ⟨fun | .there x => nomatch x⟩

end Silmaril.MLIR.SMT.Examples
