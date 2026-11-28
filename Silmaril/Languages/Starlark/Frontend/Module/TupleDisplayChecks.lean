module

public import Silmaril.Languages.Starlark.Frontend.Module.Checks
import all Silmaril.Languages.Starlark.Frontend.Module.Checks

namespace Silmaril.Languages.Starlark.Frontend.Module

private def setup :=
  "# 雪\nxs=[1]\nys=[2]\nzs=[3]\ndef take(x):\n  return 7\ndef id(x):\n  return x\n" ++
  "def truthy(x):\n  return True\ndef need(x, required):\n  return x\n"
private def nested := setup ++
  "saved=(take(list(xs)), (take(list(ys)) if truthy(list(zs)) else need(list(xs)),), take(()),)\n" ++
  "out=len(saved)"
private def suite := setup ++
  "def relay(pick):\n  saved=(pick(4), ())\n  return len((saved, pick(5)))\nout=relay(id)"
private def failure := setup ++
  "out=((take(list(xs)),), need(list(ys)), take(list(zs)))\nmarker=99"

/-- Shared execution controls for tuple displays and parenthesized calls. -/
public def tupleDisplayControls : List Control := [
  ⟨"tuple-nested-elements-and-conditional", nested, .exportedInt 3⟩,
  ⟨"tuple-function-assignment-and-return-without-trailing-comma", suite, .exportedInt 2⟩,
  ⟨"tuple-singleton-as-explicit-spread", setup ++ "out=id(*(take(1),))", .exportedInt 7⟩,
  ⟨"tuple-parenthesized-call-is-grouped", setup ++ "out=(take(1))", .exportedInt 7⟩,
  ⟨"tuple-singleton-has-one-element", setup ++ "out=len((take(1),))", .exportedInt 1⟩,
  ⟨"tuple-middle-element-masks-later-elements", failure, .missingArgument "required"⟩]

#guard tupleDisplayControls.all fun control => decide (observe control.source = some control.expected)

private inductive Allocation where
  | list (values : List (Option Int))
  | tuple (values : List (Option Int))
  deriving DecidableEq

private def allocations (state : Lists.State) : List Allocation :=
  let project (values : List Lists.Value) := values.map fun
    | .scalar (.int n) => some n
    | _ => none
  state.heap.toList.filterMap fun cell =>
    match cell.contents with
    | .list values => some (.list (project values))
    | .tuple values _ => some (.tuple (project values))
    | _ => none

private def successTrace : Option (List Allocation) :=
  match runUtf8 nested.toUTF8 with
  | .ok (.ok _ state) => some (allocations state)
  | _ => none

#guard decide (successTrace = some [.list [some 1], .list [some 2], .list [some 3],
  .list [some 1], .list [some 3], .list [some 2], .tuple [some 7], .tuple [], .tuple [some 7, none, some 7]])

private def failureTrace : Option (List Allocation) :=
  match runUtf8 failure.toUTF8 with
  | .ok (.error (.runtime (.missingArguments ["required"])) state) =>
    if state.heap.any (fun cell =>
      match cell.contents with | .binding (some (.scalar (.int 99))) => true | _ => false)
    then none
    else some (allocations state)
  | _ => none

-- The inner singleton and the failing element's copy survive.
#guard decide (failureTrace = some [.list [some 1], .list [some 2], .list [some 3],
  .list [some 1], .tuple [some 7], .list [some 2]])

/-- Grouping, singleton and empty tuples, and nested tuples on CRLF input. -/
public def tupleSpanSource :=
  "# 雪\r\ngroup=(f())\r\nsingle=(f(),)\r\nouter=((),\r\n  (a() if test() else b(),),\r\n  g((h(),)),)"

/-- Tuple and immediate element spans, grouped in tuple preorder. -/
public def tupleDisplaySpans : List Span := [
  ⟨⟨27, 3, 8⟩, ⟨33, 3, 14⟩⟩, ⟨⟨28, 3, 9⟩, ⟨31, 3, 12⟩⟩,
  ⟨⟨41, 4, 7⟩, ⟨90, 6, 14⟩⟩,
  ⟨⟨42, 4, 8⟩, ⟨44, 4, 10⟩⟩, ⟨⟨49, 5, 3⟩, ⟨74, 5, 28⟩⟩, ⟨⟨79, 6, 3⟩, ⟨88, 6, 12⟩⟩,
  ⟨⟨42, 4, 8⟩, ⟨44, 4, 10⟩⟩,
  ⟨⟨49, 5, 3⟩, ⟨74, 5, 28⟩⟩, ⟨⟨50, 5, 4⟩, ⟨72, 5, 26⟩⟩,
  ⟨⟨81, 6, 5⟩, ⟨87, 6, 11⟩⟩, ⟨⟨82, 6, 6⟩, ⟨85, 6, 9⟩⟩]

private def displaySpans (value : CallOperand) (elements : List CallOperand) : List Span :=
  value.span :: elements.map CallOperand.span

private def parsedSpans : Option (Span × List Span × List (Span × Span × List Span)) := do
  let [first, second, third] ← (parseFileUtf8 tupleSpanSource.toUTF8).toOption | none
  let .assignCall "group" (.group groupSpan (.call ..)) := first.command | none
  let .assignCall "single" singleton := second.command | none
  let .tuple _ [item] := singleton | none
  let .assignCall "outer" outer := third.command | none
  let .tuple _ [empty, inner, call] := outer | none
  let .tuple _ [] := empty | none
  let .tuple _ [conditional] := inner | none
  let .call _ _ arguments := call | none
  let [operand] := arguments.positional | none
  let .tuple _ [nestedCall] := operand | none
  let parsed ← (parseUtf8 tupleSpanSource.toUTF8).toOption
  let [group, single, command] := parsed.commands | none
  if single.application.isSome || command.application.isSome then none else
  match group.command, single.command, command.command with
  | .assign "group" (.call (.scalar (.read "f")) [] [] none none),
    .assign "single" (.tuple [.call (.scalar (.read "f")) [] [] none none]),
    .assign "outer" (.tuple [.tuple [],
      .tuple [.conditional (.call (.scalar (.read "test")) [] [] none none)
        (.call (.scalar (.read "a")) [] [] none none) (.call (.scalar (.read "b")) [] [] none none)],
      .call (.scalar (.read "g")) [.tuple [.call (.scalar (.read "h")) [] [] none none]] [] none none]) =>
    return (groupSpan, displaySpans singleton [item] ++ displaySpans outer [empty, inner, call] ++
      displaySpans empty [] ++ displaySpans inner [conditional] ++ displaySpans operand [nestedCall],
      (group.applications ++ single.nestedCalls ++ command.nestedCalls).map fun app =>
        (app.span, app.callee, app.operands.ordered))
  | _, _, _ => none

example : parsedSpans = some (⟨⟨13, 2, 7⟩, ⟨18, 2, 12⟩⟩, tupleDisplaySpans, [
    (⟨⟨14, 2, 8⟩, ⟨17, 2, 11⟩⟩, ⟨⟨14, 2, 8⟩, ⟨15, 2, 9⟩⟩, []),
    (⟨⟨28, 3, 9⟩, ⟨31, 3, 12⟩⟩, ⟨⟨28, 3, 9⟩, ⟨29, 3, 10⟩⟩, []),
    (⟨⟨50, 5, 4⟩, ⟨53, 5, 7⟩⟩, ⟨⟨50, 5, 4⟩, ⟨51, 5, 5⟩⟩, []),
    (⟨⟨57, 5, 11⟩, ⟨63, 5, 17⟩⟩, ⟨⟨57, 5, 11⟩, ⟨61, 5, 15⟩⟩, []),
    (⟨⟨69, 5, 23⟩, ⟨72, 5, 26⟩⟩, ⟨⟨69, 5, 23⟩, ⟨70, 5, 24⟩⟩, []),
    (⟨⟨79, 6, 3⟩, ⟨88, 6, 12⟩⟩, ⟨⟨79, 6, 3⟩, ⟨80, 6, 4⟩⟩, [⟨⟨81, 6, 5⟩, ⟨87, 6, 11⟩⟩]),
    (⟨⟨82, 6, 6⟩, ⟨85, 6, 9⟩⟩, ⟨⟨82, 6, 6⟩, ⟨83, 6, 7⟩⟩, [])]) := by decide +kernel

/-- Boundary and separator checks paired with pinned Go syntax decisions. -/
public def tupleSyntaxControls : List (String × String × DiagnosticKind × Bool) := [
  ("tuple-missing-comma", "out=(f(), g() h())", .expected "',' or ')'", false),
  ("tuple-double-comma", "out=(f(),,g())", .expected "an expression", false),
  ("tuple-unparenthesized-outside-profile", "out=f(), g()", .unsupported .tuple, true),
  ("grouped-computed-callee-outside-profile", "out=(f())()", .unsupported .call, true),
  ("tuple-default-outside-profile", "def f(x=(1,)):\n  return x", .unsupported .tuple, true)]

#guard tupleSyntaxControls.all fun (_, source, expected, _) =>
  (frontendDiagnostic source).map Diagnostic.kind == some expected

private def standaloneDiagnostic : Option Diagnostic :=
  match parseModuleUtf8 "# 雪\r\nout=(1,)".toUTF8 with
  | .error diagnostic => some diagnostic
  | .ok _ => none

example : standaloneDiagnostic =
    some ⟨.unsupported .tuple, ⟨⟨13, 2, 7⟩, ⟨14, 2, 8⟩⟩⟩ := by decide +kernel

end Silmaril.Languages.Starlark.Frontend.Module
