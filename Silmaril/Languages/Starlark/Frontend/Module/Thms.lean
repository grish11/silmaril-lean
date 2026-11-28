module

public import Silmaril.Languages.Starlark.Frontend.Module.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Thms
import Silmaril.Proofs.Languages.Starlark.Frontend.Module.Branch
import Silmaril.Proofs.Languages.Starlark.Frontend.Module.CallArguments
import Silmaril.Proofs.Languages.Starlark.Frontend.Module.SequenceDisplay

public section

namespace Silmaril.Languages.Starlark.Frontend.Module

/-- Existing module agreement applies to the normalized commands produced by the frontend. -/
theorem initializes_iff_run (parsed : ParsedModule) (out : Modules.Resolve.Result) :
    Modules.Resolve.Initializes parsed.toCommands (fun _ => none) {} #[] out ↔ parsed.run = out :=
  Modules.Resolve.initializes_iff_runModule parsed.toCommands (fun _ => none) {} #[] out

/-- Successful lowering preserves explicit keyword names in source order,
including any repetitions for normalized validation. -/
theorem lowerNamedArguments_names {arguments : List LocatedNamedArgument}
    {lowered : List (String × Functions.Lowering.Resolve.SourceExpr)}
    (lowering : lowerNamedArguments arguments = .ok lowered) :
    lowered.map Prod.fst = arguments.map LocatedNamedArgument.name :=
  Silmaril.Proofs.Languages.Starlark.Frontend.Module.lowerNamedArguments_names lowering

/-- The normalized call and its source spans have the same positional count,
ordered explicit names, and presence of each spread. -/
theorem lowerCall_operands {callee : String} {arguments : LocatedCallArguments}
    {result : LoweredCall} (lowering : lowerCall callee arguments = .ok result) :
    ∃ positional named star starStar,
      result.expression = .call (.scalar (.read callee)) positional named star starStar ∧
      result.spans = arguments.spans ∧
      callShape result.spans = Functions.Lowering.argumentShape positional named star starStar :=
  Silmaril.Proofs.Languages.Starlark.Frontend.Module.lowerCall_operands lowering

/-- Successful application lowering uses exactly the lowered callee and preserves
the application's span, callee span, and grouped operand locations. -/
theorem lowerApplication_parts {span : Span} {callee : CallOperand}
    {arguments : LocatedCallArguments} {result : LoweredOperand}
    (lowering : lowerOperand (.call span callee arguments) = .ok result) :
    ∃ callable positional named star starStar,
      lowerOperand callee = .ok callable ∧
      result.expression = .call callable.expression positional named star starStar ∧
      result.applications.head? = some ⟨span, callee.span, arguments.spans⟩ ∧
      callShape arguments.spans = Functions.Lowering.argumentShape positional named star starStar :=
  Silmaril.Proofs.Languages.Starlark.Frontend.Module.lowerApplication_parts lowering

open Functions.Lowering

/-- Evaluate the resolved callee once, then evaluate operands from its resulting state. -/
theorem denoteCall_calleeFirst (program : Functions.Program) (available : List Functions.DeclarationId)
    (bodyMeaning : ClosureMeaning available) (callee : Functions.Lowering.Expr)
    (positional : List Functions.Lowering.Expr) (keywords : List (String × Functions.Lowering.Expr))
    (star starStar : Option Functions.Lowering.Expr) (state : Lists.State) :
    denoteExprWith program available bodyMeaning (.call callee positional keywords star starStar) state =
      match denoteExprWith program available bodyMeaning callee state with
      | .ok value next =>
        (do
          let operands ← (argumentExprs positional keywords star starStar).mapM
            (denoteExprWith program available bodyMeaning)
          denoteApplicationWith program available bodyMeaning
            (argumentShape positional keywords star starStar) (value :: operands)) next
      | .error error next => .error error next :=
  Silmaril.Proofs.Languages.Starlark.Frontend.Module.denoteCall_calleeFirst
    program available bodyMeaning callee positional keywords star starStar state

/-- A failed callee bypasses operand evaluation and preserves its error state. -/
theorem denoteCall_calleeError {program : Functions.Program} {available : List Functions.DeclarationId}
    {bodyMeaning : ClosureMeaning available} {callee : Functions.Lowering.Expr} {positional : List Functions.Lowering.Expr}
    {keywords : List (String × Functions.Lowering.Expr)} {star starStar : Option Functions.Lowering.Expr}
    {state next : Lists.State}
    {error : Lists.Error} (failure : denoteExprWith program available bodyMeaning callee state = .error error next) :
    denoteExprWith program available bodyMeaning (.call callee positional keywords star starStar) state =
      .error error next := by
  rw [denoteCall_calleeFirst, failure]

/-- A logical expression tests the left result before evaluating the right.
The skipped or failing branch returns the exact state reached so far. -/
theorem denoteLogical_order (program : Functions.Program) (available : List Functions.DeclarationId)
    (bodyMeaning : ClosureMeaning available) (op : LogicalOp)
    (left right : Functions.Lowering.Expr) (state : Lists.State) :
    denoteExprWith program available bodyMeaning (.logical op left right) state =
      match denoteExprWith program available bodyMeaning left state with
      | .ok value next =>
        match Lists.Iteration.truth value next with
        | .ok flag after =>
          if (if op = .and then flag else !flag) then
            denoteExprWith program available bodyMeaning right after
          else .ok value after
        | .error error after => .error error after
      | .error error next => .error error next :=
  Silmaril.Proofs.Languages.Starlark.Frontend.Module.denoteLogical_order
    program available bodyMeaning op left right state

/-- Run the condition and its truth test, then evaluate only the selected
arm from the resulting state. Condition failures retain their exact state. -/
theorem denoteConditional_order (program : Functions.Program) (available : List Functions.DeclarationId)
    (bodyMeaning : ClosureMeaning available) (test yes no : Functions.Lowering.Expr) (state : Lists.State) :
    denoteExprWith program available bodyMeaning (.branch test yes no) state =
      match denoteExprWith program available bodyMeaning test state with
      | .ok value next =>
        match Lists.Iteration.truth value next with
        | .ok flag after => denoteExprWith program available bodyMeaning (if flag then yes else no) after
        | .error error after => .error error after
      | .error error next => .error error next :=
  Silmaril.Proofs.Languages.Starlark.Frontend.Module.denoteConditional_order
    program available bodyMeaning test yes no state

/-- A resolved statement tests its expression once, then executes only the
selected suite from the resulting state. An `elif` lives in the false suite,
so an earlier true or failing test skips it. -/
theorem denoteBranchExpr_order (program : Functions.Program) (available : List Functions.DeclarationId)
    (test : Functions.Lowering.Expr) (yes no : Functions.Body) (state : Lists.State) :
    Functions.denoteBody program available (.branchExpr test yes no) state =
      match denoteExprWith program available
          (fun plan next => Functions.denoteBody program
            (Functions.withoutDeclaration available plan.id) plan.body next)
          test state with
      | .ok value next =>
        match Lists.Iteration.truth value next with
        | .ok flag after => Functions.denoteBody program available (if flag then yes else no) after
        | .error error after => .error error after
      | .error error next => .error error next :=
  Silmaril.Proofs.Languages.Starlark.Frontend.Module.denoteBranchExpr_order program available test yes no state

/-- Evaluate the elements in list order. Allocate the display only after every
element succeeds, and preserve the exact prefix state on failure. -/
theorem denoteList_order (program : Functions.Program) (available : List Functions.DeclarationId)
    (bodyMeaning : ClosureMeaning available) (elements : List Functions.Lowering.Expr) (state : Lists.State) :
    denoteExprWith program available bodyMeaning (.list elements) state =
      match (elements.mapM (denoteExprWith program available bodyMeaning)) state with
      | .ok values next => Lists.allocate values next
      | .error error next => .error error next :=
  Silmaril.Proofs.Languages.Starlark.Frontend.Module.denoteList_order program available bodyMeaning elements state

/-- Evaluate the first element once and start the remaining elements in its
resulting state. Either failure returns directly to the caller. -/
theorem denoteList_cons (program : Functions.Program) (available : List Functions.DeclarationId)
    (bodyMeaning : ClosureMeaning available) (first : Functions.Lowering.Expr)
    (rest : List Functions.Lowering.Expr) (state : Lists.State) :
    denoteExprWith program available bodyMeaning (.list (first :: rest)) state =
      match denoteExprWith program available bodyMeaning first state with
      | .ok value next =>
        match (rest.mapM (denoteExprWith program available bodyMeaning)) next with
        | .ok values after => Lists.allocate (value :: values) after
        | .error error after => .error error after
      | .error error next => .error error next :=
  Silmaril.Proofs.Languages.Starlark.Frontend.Module.denoteList_cons program available bodyMeaning first rest state

/-- Evaluate the elements in tuple order. Allocate the display only after every
element succeeds, and preserve the exact prefix state on failure. -/
theorem denoteTuple_order (program : Functions.Program) (available : List Functions.DeclarationId)
    (bodyMeaning : ClosureMeaning available) (elements : List Functions.Lowering.Expr) (state : Lists.State) :
    denoteExprWith program available bodyMeaning (.tuple elements) state =
      match (elements.mapM (denoteExprWith program available bodyMeaning)) state with
      | .ok values next => Lists.allocateTuple values next
      | .error error next => .error error next :=
  Silmaril.Proofs.Languages.Starlark.Frontend.Module.denoteTuple_order program available bodyMeaning elements state

/-- Evaluate the first element once and start the remaining elements in its
resulting state. Either failure returns directly to the caller. -/
theorem denoteTuple_cons (program : Functions.Program) (available : List Functions.DeclarationId)
    (bodyMeaning : ClosureMeaning available) (first : Functions.Lowering.Expr)
    (rest : List Functions.Lowering.Expr) (state : Lists.State) :
    denoteExprWith program available bodyMeaning (.tuple (first :: rest)) state =
      match denoteExprWith program available bodyMeaning first state with
      | .ok value next =>
        match (rest.mapM (denoteExprWith program available bodyMeaning)) next with
        | .ok values after => Lists.allocateTuple (value :: values) after
        | .error error after => .error error after
      | .error error next => .error error next :=
  Silmaril.Proofs.Languages.Starlark.Frontend.Module.denoteTuple_cons program available bodyMeaning first rest state

end Silmaril.Languages.Starlark.Frontend.Module
