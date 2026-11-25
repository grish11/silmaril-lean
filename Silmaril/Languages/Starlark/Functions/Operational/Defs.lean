module

public import Silmaril.Languages.Starlark.Functions.Defs
public import Silmaril.Languages.Starlark.Functions.Builtins.Operational.Defs
public import Silmaril.Languages.Starlark.Lists.Iteration.Operational.Defs

public section

namespace Silmaril.Languages.Starlark.Functions

open Lists
open Lists.Iteration (Flow Suite Runs truth)

/-- Big-step rules over the available declarations. The same declaration may
be invoked again after a call completes, but not while it is active. -/
inductive Exec (program : Program) : List DeclarationId → State → Body → Outcome Flow → Prop where
  | total {available : List DeclarationId} {s : State} {suite : Suite 0} {out : Outcome Flow} :
      Runs s (.suite suite) out → Exec program available s (.total suite) out
  | seq {available : List DeclarationId} {s t : State} {first rest : Body} {out : Outcome Flow} :
      Exec program available s first (.ok .next t) → Exec program available t rest out →
      Exec program available s (.seq first rest) out
  | seqStop {available : List DeclarationId} {s t : State} {first rest : Body} {signal : Flow} :
      Exec program available s first (.ok signal t) → signal ≠ .next →
      Exec program available s (.seq first rest) (.ok signal t)
  | seqError {available : List DeclarationId} {s t : State} {first rest : Body} {error : Error} :
      Exec program available s first (.error error t) →
      Exec program available s (.seq first rest) (.error error t)
  | branch {available : List DeclarationId} {s t : State} {test : Lists.Expr} {yes no : Body}
      {value : Outcome Lists.Value} {flag : Bool} {out : Outcome Flow} :
      Eval s test value → Outcome.resume value truth = .ok flag t →
      Exec program available t (if flag then yes else no) out →
      Exec program available s (.branch test yes no) out
  | branchError {available : List DeclarationId} {s t : State} {test : Lists.Expr} {yes no : Body}
      {value : Outcome Lists.Value} {error : Error} :
      Eval s test value → Outcome.resume value truth = .error error t →
      Exec program available s (.branch test yes no) (.error error t)
  | define {available : List DeclarationId} {s : State} {target : Binding} {id : DeclarationId}
      {defaults : Outcome (List Lists.Value)} :
      Eval s (defaultOperands program id) defaults →
      Exec program available s (.define target id) (Outcome.resume defaults (define program target id))
  | call {available : List DeclarationId} {s t : State} {target : Option Binding}
      {callee : Lists.Expr} {arguments : Arguments} {operands : Outcome (List Lists.Value)}
      {plan : Prepared available} {out : Outcome Flow} :
      Eval s (Arguments.operands callee arguments) operands →
      Outcome.resume operands (prepare program available arguments) = .ok (.closure plan) t →
      Exec program (withoutDeclaration available plan.id) t plan.body out →
      Exec program available s (.call target callee arguments) (completeCall s target out)
  | callBuiltin {available : List DeclarationId} {s t : State} {target : Option Binding}
      {callee : Lists.Expr} {arguments : Arguments} {operands : Outcome (List Lists.Value)}
      {id : Builtin} {actual : Actual} {out : Outcome Lists.Value} :
      Eval s (Arguments.operands callee arguments) operands →
      Outcome.resume operands (prepare program available arguments) = .ok (.builtin id actual) t →
      Builtins.Invokes t id actual out →
      Exec program available s (.call target callee arguments)
        (Outcome.resume out (writeCallResult target))
  | callError {available : List DeclarationId} {s t : State} {target : Option Binding}
      {callee : Lists.Expr} {arguments : Arguments} {operands : Outcome (List Lists.Value)}
      {error : Error} :
      Eval s (Arguments.operands callee arguments) operands →
      Outcome.resume operands (prepare program available arguments) = .error error t →
      Exec program available s (.call target callee arguments) (.error error t)

end Silmaril.Languages.Starlark.Functions
