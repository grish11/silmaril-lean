module

public import Silmaril.Languages.Starlark.Frontend.Module.Checks
import all Silmaril.Languages.Starlark.Frontend.Module.Checks

namespace Silmaril.Languages.Starlark.Frontend.Module

private def setup :=
  "# 雪\nxs=[1]\nys=[2]\nzs=[3]\ndef take(x):\n  return 7\ndef id(x):\n  return x\n" ++
  "def truthy(x):\n  return True\ndef need(x, required):\n  return x\n"
private def nested := setup ++
  "saved=[take(list(xs)), [take(list(ys)) if truthy(list(zs)) else need(list(xs)),], take([]),]\n" ++
  "out=len(saved)"
private def suite := setup ++
  "def relay(pick):\n  saved=[pick(4),]\n  return len([saved, pick(5)])\nout=relay(id)"
private def failure := setup ++
  "out=[[take(list(xs))], need(list(ys)), take(list(zs))]\nmarker=99"

/-- Shared execution controls for nested list displays and their call operands. -/
public def listDisplayControls : List Control := [
  ⟨"list-nested-elements-and-conditional", nested, .exportedInt 3⟩,
  ⟨"list-in-function-assignment-and-return", suite, .exportedInt 2⟩,
  ⟨"list-as-explicit-spread", setup ++ "out=id(*[take(1),])", .exportedInt 7⟩,
  ⟨"list-middle-element-masks-later-elements", failure, .missingArgument "required"⟩,
  ⟨"list-skipped-call-still-resolves",
    "# 雪\nout=len([1 if True else missing()])", .undefinedName "missing"⟩]

#guard listDisplayControls.all fun control => decide (observe control.source = some control.expected)

-- Distinguish non-scalar elements while inspecting every allocated list.
private def listTrace (state : Lists.State) : List (List (Option Int)) :=
  state.heap.toList.filterMap fun cell =>
    match cell.contents with
    | .list values => some (values.map fun
      | .scalar (.int n) => some n
      | _ => none)
    | _ => none

private def successTrace : Option (List (List (Option Int))) :=
  match runUtf8 nested.toUTF8 with
  | .ok (.ok _ state) => some (listTrace state)
  | _ => none

#guard decide (successTrace = some
  [[some 1], [some 2], [some 3], [some 1], [some 3], [some 2], [some 7], [], [some 7, none, some 7]])

private def failureTrace : Option (List (List (Option Int))) :=
  match runUtf8 failure.toUTF8 with
  | .ok (.error (.runtime (.missingArguments ["required"])) state) =>
    if state.heap.any (fun cell =>
      match cell.contents with | .binding (some (.scalar (.int 99))) => true | _ => false)
    then none
    else some (listTrace state)
  | _ => none

-- The completed inner display and effects of the failing element survive.
-- The outer list and the later element's copy are absent.
#guard decide (failureTrace = some [[some 1], [some 2], [some 3], [some 1], [some 7], [some 2]])

/-- CRLF continuation with UTF-8 and trailing commas at each list depth. -/
public def listSpanSource :=
  "# 雪\r\nout=[f(),\r\n  [a() if test() else b(),],\r\n  g([h(),]),]"

/-- Display and immediate element spans, grouped in display preorder. -/
public def listDisplaySpans : List Span := [
  ⟨⟨11, 2, 5⟩, ⟨61, 4, 14⟩⟩,
  ⟨⟨12, 2, 6⟩, ⟨15, 2, 9⟩⟩, ⟨⟨20, 3, 3⟩, ⟨45, 3, 28⟩⟩, ⟨⟨50, 4, 3⟩, ⟨59, 4, 12⟩⟩,
  ⟨⟨20, 3, 3⟩, ⟨45, 3, 28⟩⟩, ⟨⟨21, 3, 4⟩, ⟨43, 3, 26⟩⟩,
  ⟨⟨52, 4, 5⟩, ⟨58, 4, 11⟩⟩, ⟨⟨53, 4, 6⟩, ⟨56, 4, 9⟩⟩]

private def displaySpans (value : CallOperand) (elements : List CallOperand) : List Span :=
  value.span :: elements.map CallOperand.span

private def parsedSpans : Option (List Span × List (Span × Span × List Span)) := do
  let [source] ← (parseFileUtf8 listSpanSource.toUTF8).toOption | none
  let .assignCall "out" root := source.command | none
  let .list _ [first, inner, call] := root | none
  let .list _ [conditional] := inner | none
  let .call _ _ arguments := call | none
  let [operand] := arguments.positional | none
  let .list _ [nestedCall] := operand | none
  let parsed ← (parseUtf8 listSpanSource.toUTF8).toOption
  let [command] := parsed.commands | none
  if command.application.isSome then none else
  match command.command with
  | .assign "out" (.list [
      .call (.scalar (.read "f")) [] [] none none,
      .list [.conditional (.call (.scalar (.read "test")) [] [] none none)
        (.call (.scalar (.read "a")) [] [] none none) (.call (.scalar (.read "b")) [] [] none none)],
      .call (.scalar (.read "g")) [.list [.call (.scalar (.read "h")) [] [] none none]] [] none none]) =>
    return (displaySpans root [first, inner, call] ++ displaySpans inner [conditional] ++
      displaySpans operand [nestedCall],
      command.nestedCalls.map fun app => (app.span, app.callee, app.operands.ordered))
  | _ => none

example : parsedSpans = some (listDisplaySpans, [
    (⟨⟨12, 2, 6⟩, ⟨15, 2, 9⟩⟩, ⟨⟨12, 2, 6⟩, ⟨13, 2, 7⟩⟩, []),
    (⟨⟨21, 3, 4⟩, ⟨24, 3, 7⟩⟩, ⟨⟨21, 3, 4⟩, ⟨22, 3, 5⟩⟩, []),
    (⟨⟨28, 3, 11⟩, ⟨34, 3, 17⟩⟩, ⟨⟨28, 3, 11⟩, ⟨32, 3, 15⟩⟩, []),
    (⟨⟨40, 3, 23⟩, ⟨43, 3, 26⟩⟩, ⟨⟨40, 3, 23⟩, ⟨41, 3, 24⟩⟩, []),
    (⟨⟨50, 4, 3⟩, ⟨59, 4, 12⟩⟩, ⟨⟨50, 4, 3⟩, ⟨51, 4, 4⟩⟩, [⟨⟨52, 4, 5⟩, ⟨58, 4, 11⟩⟩]),
    (⟨⟨53, 4, 6⟩, ⟨56, 4, 9⟩⟩, ⟨⟨53, 4, 6⟩, ⟨54, 4, 7⟩⟩, [])]) := by decide +kernel

/-- Module diagnostics paired with pinned Go syntax decisions. -/
public def listSyntaxControls : List (String × String × DiagnosticKind × Bool) := [
  ("list-missing-comma", "out=[f() g()]", .expected "',' or ']'", false),
  ("list-double-comma", "out=[f(),, g()]", .expected "an expression", false),
  ("list-semicolon", "out=[f(); g()]", .expected "',' or ']'", false),
  ("list-comprehension-outside-profile", "out=[f(x) for x in xs]", .unsupported .collection, true),
  ("dict-value-call-outside-profile", "out={'a': f()}", .unsupported .call, true),
  ("list-default-outside-profile", "def f(x=[g()]):\n  return x", .unsupported .collection, true)]

#guard listSyntaxControls.all fun (_, source, expected, _) =>
  (frontendDiagnostic source).map Diagnostic.kind == some expected

private def standaloneDiagnostic : Option Diagnostic :=
  match parseModuleUtf8 listSpanSource.toUTF8 with
  | .error diagnostic => some diagnostic
  | .ok _ => none

example : standaloneDiagnostic =
    some ⟨.unsupported .collection, ⟨⟨11, 2, 5⟩, ⟨12, 2, 6⟩⟩⟩ := by decide +kernel

end Silmaril.Languages.Starlark.Frontend.Module
