module

public import Silmaril.Logic.Smt.Uflia.SExpr.Defs

/-! Integer coefficient normalization preserves evaluation in every actual sorted
model. It changes neither carriers nor uninterpreted operation interpretations. -/

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SExpr

/-- Scaling has an effect only at the standard integer carrier. -/
def scaleValue {E : Environment} (M : Model E.signature) (coefficient : Int)
    {sort : SortCode String} (value : M.carriers.value sort) : M.carriers.value sort :=
  match sort with
  | .int => coefficient * value
  | _ => value

theorem eval_scaleLinear {E : Environment} (M : Model E.signature)
    {sort : SortCode String} (coefficient : Int) (term : Uflia.Term E.signature sort) :
    M.eval (scaleLinear coefficient term) = scaleValue M coefficient (M.eval term) := by
  induction term generalizing coefficient with
  | var i => exact Fin.elim0 i
  | app op args ih =>
    show M.eval (scaleLinear coefficient (.app op args)) =
      scaleValue M coefficient (M.eval (.app op args))
    cases op <;> try rfl
    case uf n inputs output symbol =>
      cases output <;> simp [scaleLinear, scaleValue, Model.eval, Model.algebra,
        Algebraic.ManySorted.Model.eval, Model.apply]
    case add =>
      show M.eval (scaleLinear coefficient (args 0)) +
          M.eval (scaleLinear coefficient (args 1)) =
        coefficient * (M.eval (args 0) + M.eval (args 1))
      rw [ih 0, ih 1]
      exact (Int.mul_add _ _ _).symm
    case sub =>
      show M.eval (scaleLinear coefficient (args 0)) -
          M.eval (scaleLinear coefficient (args 1)) =
        coefficient * (M.eval (args 0) - M.eval (args 1))
      rw [ih 0, ih 1]
      exact (Int.mul_sub _ _ _).symm
    case scale k =>
      show M.eval (scaleLinear (coefficient * k) (args 0)) =
        coefficient * (k * M.eval (args 0))
      rw [ih 0]
      exact Int.mul_assoc _ _ _
    case ite sort => cases sort <;> rfl

theorem eval_scaleLinear_int {E : Environment} (M : Model E.signature)
    (coefficient : Int) (term : Uflia.Term E.signature .int) :
    M.eval (scaleLinear coefficient term) = coefficient * M.eval term :=
  eval_scaleLinear M coefficient term

end Silmaril.Logic.Smt.Uflia.SExpr
