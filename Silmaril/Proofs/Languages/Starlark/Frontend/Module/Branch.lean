module

public import Silmaril.Languages.Starlark.Functions.Denotation.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Frontend.Module

open Silmaril.Languages.Starlark
open Functions Functions.Lowering
open Lists (Outcome)

theorem denoteBranchExpr_order (program : Program) (available : List DeclarationId)
    (test : Expr) (yes no : Body) (state : Lists.State) :
    denoteBody program available (.branchExpr test yes no) state =
      match denoteExprWith program available
          (fun plan next => denoteBody program (withoutDeclaration available plan.id) plan.body next)
          test state with
      | .ok value next =>
        match Lists.Iteration.truth value next with
        | .ok flag after => denoteBody program available (if flag then yes else no) after
        | .error error after => .error error after
      | .error error next => .error error next := by
  rw [denoteBody.eq_def program available (.branchExpr test yes no)]
  change Outcome.resume (Outcome.resume (denoteExprWith program available
      (fun plan next => denoteBody program (withoutDeclaration available plan.id) plan.body next)
      test state) Lists.Iteration.truth) (fun flag next =>
        if flag then denoteBody program available yes next else denoteBody program available no next) = _
  cases denoteExprWith program available
      (fun plan next => denoteBody program (withoutDeclaration available plan.id) plan.body next)
      test state with
  | error _ _ => rfl
  | ok value next =>
    dsimp only [Outcome.resume]
    cases Lists.Iteration.truth value next with
    | error _ _ => rfl
    | ok flag _ => cases flag <;> rfl

end Silmaril.Proofs.Languages.Starlark.Frontend.Module
