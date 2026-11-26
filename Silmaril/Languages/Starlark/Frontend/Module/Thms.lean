module

public import Silmaril.Languages.Starlark.Frontend.Module.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Thms
import Silmaril.Proofs.Languages.Starlark.Frontend.Module.CallArguments

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

end Silmaril.Languages.Starlark.Frontend.Module
