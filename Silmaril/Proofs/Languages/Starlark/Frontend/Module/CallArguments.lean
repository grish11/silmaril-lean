module

public import Silmaril.Languages.Starlark.Frontend.Module.Defs
import all Silmaril.Languages.Starlark.Frontend.Module.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Frontend.Module

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Frontend
open Silmaril.Languages.Starlark.Frontend.Module
  (lowerNamedArguments lowerArgument lowerGroupedCall lowerOperand lowerOperand_call
    lowerCall lowerCallWithCallee LoweredCall LoweredOperand callShape)

private theorem namedMapM_names {α β : Type} (lower : α → Except Diagnostic β)
    {arguments : List (LocatedNamedArgument α)} {lowered : List (String × β)}
    (mapped : (arguments.mapM fun argument => do
      return (argument.name, ← lower argument.value)) = .ok lowered) :
    lowered.map Prod.fst = arguments.map LocatedNamedArgument.name := by
  induction arguments generalizing lowered with
  | nil => cases mapped; rfl
  | cons argument rest ih =>
    rw [List.mapM_cons] at mapped
    cases value : lower argument.value with
    | error _ => simp [value, bind, Except.bind] at mapped
    | ok expr =>
      cases tail : (rest.mapM fun item => do return (item.name, ← lower item.value)) with
      | error _ => rw [tail] at mapped; simp [value, bind, Except.bind, pure, Except.pure] at mapped
      | ok result =>
        rw [tail] at mapped
        simp [value, bind, Except.bind, pure, Except.pure] at mapped
        subst lowered
        simp [ih tail]

theorem lowerNamedArguments_names {arguments : List LocatedNamedArgument}
    {lowered : List (String × Functions.Lowering.Resolve.SourceExpr)}
    (lowering : lowerNamedArguments arguments = .ok lowered) :
    lowered.map Prod.fst = arguments.map LocatedNamedArgument.name :=
  namedMapM_names lowerArgument lowering

private theorem listMapM_length {α β ε : Type} {f : α → Except ε β} {input : List α}
    {output : List β} (mapped : input.mapM f = .ok output) : output.length = input.length := by
  induction input generalizing output with
  | nil => cases mapped; rfl
  | cons head rest ih =>
    rw [List.mapM_cons] at mapped
    cases first : f head with
    | error _ => simp [first, bind, Except.bind] at mapped
    | ok value =>
      cases tail : rest.mapM f with
      | error _ => simp [first, tail, bind, Except.bind] at mapped
      | ok values =>
        simp [first, tail, bind, Except.bind, pure, Except.pure] at mapped
        subst output
        simp [ih tail]

private theorem optionMapM_isSome {α β ε : Type} {f : α → Except ε β} {input : Option α}
    {output : Option β} (mapped : input.mapM f = .ok output) : output.isSome = input.isSome := by
  cases input with
  | none => cases mapped; rfl
  | some value =>
    cases result : f value <;> rw [Option.mapM, result] at mapped <;> cases mapped
    rfl

private theorem mapM_optionAttach {α β : Type} (input : Option α)
    (f : α → Except Diagnostic β) :
    input.attach.mapM (fun item => f item.val) = input.mapM f := by
  cases input <;> rfl

theorem lowerCallWithCallee_operands {callee : Functions.Lowering.Resolve.SourceExpr}
    {arguments : LocatedCallArguments} {result : LoweredCall}
    (lowering : lowerCallWithCallee callee arguments = .ok result) :
    ∃ positional named star starStar,
      result.expression = .call callee positional named star starStar ∧
      result.spans = arguments.spans ∧
      callShape result.spans = Functions.Lowering.argumentShape positional named star starStar := by
  let lowerNamed (argument : LocatedNamedArgument CallOperand) : Except Diagnostic (String × LoweredOperand) := do
    return (argument.name, ← lowerOperand argument.value)
  let lowerSpread (spread : LocatedSpread CallOperand) := lowerOperand spread.operand
  unfold lowerCallWithCallee lowerGroupedCall at lowering
  rw [List.mapM_subtype (g := lowerOperand) (fun _ _ => rfl), List.unattach_attach,
    List.mapM_subtype (g := lowerNamed) (fun _ _ => rfl), List.unattach_attach,
    mapM_optionAttach arguments.star lowerSpread, mapM_optionAttach arguments.starStar lowerSpread] at lowering
  cases positions : arguments.positional.mapM lowerOperand with
  | error _ => rw [positions] at lowering; cases lowering
  | ok positional =>
    rw [positions] at lowering
    cases names : arguments.named.mapM lowerNamed with
    | error _ => rw [names] at lowering; cases lowering
    | ok named =>
      rw [names] at lowering
      cases spread : arguments.star.mapM lowerSpread with
      | error _ => rw [spread] at lowering; cases lowering
      | ok star =>
        rw [spread] at lowering
        cases mapping : arguments.starStar.mapM lowerSpread with
        | error _ => rw [mapping] at lowering; cases lowering
        | ok starStar =>
          have orderedNames : named.map Prod.fst = arguments.named.map LocatedNamedArgument.name :=
            namedMapM_names lowerOperand names
          rw [mapping] at lowering
          cases lowering
          refine ⟨_, _, _, _, rfl, rfl, ?_⟩
          simp [callShape, Functions.Lowering.argumentShape, LocatedCallArguments.spans,
            listMapM_length positions, ← orderedNames, List.map_map, Function.comp_def,
            optionMapM_isSome spread, optionMapM_isSome mapping]

theorem lowerCall_operands {callee : String} {arguments : LocatedCallArguments}
    {result : LoweredCall} (lowering : lowerCall callee arguments = .ok result) :
    ∃ positional named star starStar,
      result.expression = .call (.scalar (.read callee)) positional named star starStar ∧
      result.spans = arguments.spans ∧
      callShape result.spans = Functions.Lowering.argumentShape positional named star starStar :=
  lowerCallWithCallee_operands lowering

theorem lowerApplication_parts {span : Span} {callee : CallOperand}
    {arguments : LocatedCallArguments} {result : LoweredOperand}
    (lowering : lowerOperand (.call span callee arguments) = .ok result) :
    ∃ callable positional named star starStar,
      lowerOperand callee = .ok callable ∧
      result.expression = .call callable.expression positional named star starStar ∧
      result.applications.head? = some ⟨span, callee.span, arguments.spans⟩ ∧
      callShape arguments.spans = Functions.Lowering.argumentShape positional named star starStar := by
  rw [lowerOperand_call] at lowering
  cases calleeLowering : lowerOperand callee with
  | error _ => rw [calleeLowering] at lowering; cases lowering
  | ok callable =>
    cases callLowering : lowerCallWithCallee callable.expression arguments with
    | error _ =>
      simp only [calleeLowering, bind, Except.bind, callLowering] at lowering
      cases lowering
    | ok call =>
      simp only [calleeLowering, bind, Except.bind, callLowering, pure, Except.pure] at lowering
      obtain ⟨positional, named, star, starStar, expression, spans, shape⟩ :=
        lowerCallWithCallee_operands callLowering
      cases lowering
      exact ⟨callable, positional, named, star, starStar, rfl, expression, by simp [spans], spans ▸ shape⟩

open Functions.Lowering

theorem denoteCall_calleeFirst (program : Functions.Program) (available : List Functions.DeclarationId)
    (bodyMeaning : ClosureMeaning available) (callee : Expr) (positional : List Expr)
    (keywords : List (String × Expr)) (star starStar : Option Expr) (state : Lists.State) :
    denoteExprWith program available bodyMeaning (.call callee positional keywords star starStar) state =
      match denoteExprWith program available bodyMeaning callee state with
      | .ok value next =>
        (do
          let operands ← (argumentExprs positional keywords star starStar).mapM
            (denoteExprWith program available bodyMeaning)
          denoteApplicationWith program available bodyMeaning
            (argumentShape positional keywords star starStar) (value :: operands)) next
      | .error error next => .error error next := by
  rw [denoteExprWith.eq_7]
  rw [List.mapM_subtype (g := denoteExprWith program available bodyMeaning) (fun _ _ => rfl), List.unattach_attach]
  simp only [bind, EStateM.bind]
  cases denoteExprWith program available bodyMeaning callee state <;> rfl

end Silmaril.Proofs.Languages.Starlark.Frontend.Module
