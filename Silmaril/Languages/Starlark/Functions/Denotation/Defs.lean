module

public import Silmaril.Languages.Starlark.Functions.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions

open Lists
open Lists.Iteration (Flow denoteSuite truth)

/-- Structural evaluation within a frame and strict descent through the
finite set of declarations not on the call stack on invocation. -/
def denoteBody (program : Program) (available : List DeclarationId) (body : Body)
    (state : State) : Outcome Flow :=
  match body with
  | .total suite => denoteSuite suite state
  | .seq first rest =>
    Outcome.resume (denoteBody program available first state) fun
      | .next => denoteBody program available rest
      | signal => pure signal
  | .branch test yes no =>
    Outcome.resume (Outcome.resume (denote test state) truth) fun flag next =>
      if flag then denoteBody program available yes next else denoteBody program available no next
  | .define target id =>
    Outcome.resume (denote (defaultOperands program id) state) (define program target id)
  | .call target callee arguments =>
    match Outcome.resume (denote (Arguments.operands callee arguments) state) (prepare program available arguments) with
    | .error error next => .error error next
    | .ok (.closure plan) next =>
      completeCall state target (denoteBody program (withoutDeclaration available plan.id) plan.body next)
    | .ok (.builtin id actual) next =>
      Outcome.resume (Builtins.invoke id actual next) (writeCallResult target)
termination_by (available.length, sizeOf body)
decreasing_by
  all_goals first
    | apply Prod.Lex.right; simp_wf; omega
    | apply Prod.Lex.left
      exact List.length_filter_lt_length_iff_exists.mpr ⟨plan.id, plan.permitted, by simp⟩

/-- Run closed core code with every declaration initially available.
Install the root block's slots before entry when they can be captured. -/
def run (program : Program) (body : Body) (state : State := {}) : Outcome Flow :=
  denoteBody program (List.range program.size) body state

/-- Reject malformed resolved signatures and explicit duplicate keywords before running. -/
def runChecked (program : Program) (body : Body) (state : State := {}) :
    Except CallStaticError (Outcome Flow) := do
  validate program body
  return run program body state

end Silmaril.Languages.Starlark.Functions
