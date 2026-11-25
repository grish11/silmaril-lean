module

public import Silmaril.Languages.Starlark.Functions.Denotation.Defs
public import Silmaril.Languages.Starlark.Functions.Operational.Defs
public import Silmaril.Languages.Starlark.Functions.Builtins.Thms
public import Silmaril.Languages.Starlark.Lists.Thms
public import Silmaril.Languages.Starlark.Lists.Iteration.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions

open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration (Flow Runs runs_iff_denoteSuite truth)

private theorem branch_apply (program : Program) (available : List DeclarationId)
    (flag : Bool) (yes no : Body) (state : State) :
    (if flag then denoteBody program available yes state else denoteBody program available no state) =
      denoteBody program available (if flag then yes else no) state := by
  cases flag <;> rfl

theorem denote_eq_of_exec {program : Program} {available : List DeclarationId} {state : State}
    {body : Body} {out : Outcome Flow} (h : Exec program available state body out) :
    denoteBody program available body state = out := by
  induction h <;>
    (try have evaluated := (eval_iff_denote _ _ _).mp (by assumption)) <;>
    (try have total := (runs_iff_denoteSuite _ _ _).mp (by assumption)) <;>
    (try have invoked := (Builtins.invokes_iff_invoke _ _ _ _).mp (by assumption)) <;>
    simp_all [denoteBody, Outcome.resume]
  case seqStop signal _ _ _ =>
    cases signal <;> simp_all <;> rfl
  case branch =>
    rw [branch_apply]
    assumption

theorem exec_denote (program : Program) (available : List DeclarationId) (body : Body)
    (state : State) : Exec program available state body (denoteBody program available body state) := by
  cases body with
  | total code =>
    rw [denoteBody]
    exact .total ((runs_iff_denoteSuite _ _ _).mpr rfl)
  | seq first rest =>
    rw [denoteBody]
    have firstRun := exec_denote program available first state
    cases h : denoteBody program available first state with
    | error error next => exact .seqError (h ▸ firstRun)
    | ok flow next =>
      cases flow with
      | next => exact .seq (h ▸ firstRun) (exec_denote program available rest next)
      | breakLoop => exact .seqStop (h ▸ firstRun) (by intro equality; cases equality)
      | continueLoop => exact .seqStop (h ▸ firstRun) (by intro equality; cases equality)
      | returned result => exact .seqStop (h ▸ firstRun) (by intro equality; cases equality)
  | branch test yes no =>
    rw [denoteBody]
    have evaluated := (eval_iff_denote test state _).mpr rfl
    cases h : Outcome.resume (denote test state) truth with
    | error error next => exact .branchError evaluated h
    | ok flag next =>
      cases flag
      · exact .branch evaluated h (exec_denote program available no next)
      · exact .branch evaluated h (exec_denote program available yes next)
  | define target id =>
    rw [denoteBody]
    exact .define ((eval_iff_denote _ _ _).mpr rfl)
  | call target callee arguments =>
    rw [denoteBody]
    have evaluated := (eval_iff_denote (Arguments.operands callee arguments) state _).mpr rfl
    cases h : Outcome.resume (denote (Arguments.operands callee arguments) state) (prepare program available arguments) with
    | error error next => exact .callError evaluated h
    | ok plan next =>
      cases plan with
      | closure plan =>
        exact .call evaluated h (exec_denote program (withoutDeclaration available plan.id) plan.body next)
      | builtin id actual =>
        exact .callBuiltin evaluated h ((Builtins.invokes_iff_invoke _ _ _ _).mpr rfl)
termination_by (available.length, sizeOf body)
decreasing_by
  all_goals first
    | apply Prod.Lex.right; simp_wf; omega
    | apply Prod.Lex.left
      exact List.length_filter_lt_length_iff_exists.mpr ⟨plan.id, plan.permitted, by simp⟩

end Silmaril.Proofs.Languages.Starlark.Functions
