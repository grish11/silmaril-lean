module

public import Silmaril.Languages.Starlark.Frontend.Module.Checks
import all Silmaril.Languages.Starlark.Frontend.Module.Checks

namespace Silmaril.Languages.Starlark.Frontend.Module

private def sourceSetup :=
  "# 雪\nxs=[1]\nys=[2]\nzs=[3]\ndef take(x):\n  return 7\ndef need(x, required):\n  return x\n"
private def moduleSuccess := sourceSetup ++
  "out=take(list(xs)) and take(list(ys)) or take(list(zs))"
private def precedenceSuccess := sourceSetup ++ "out=take(list(xs)) or need() and need()"
private def groupedSuccess := sourceSetup ++ "out=(take(list(xs)) or need()) and take(list(ys))"
private def suiteSuccess := sourceSetup ++
  "def relay(f):\n  saved=False and need() or f(list(xs))\n  return saved and f(list(ys)) or need()\nout=relay(take)"
private def moduleFailure := sourceSetup ++
  "out=need(list(xs)) and take(list(ys)) or take(list(zs))\nmarker=99"

/-- Shared UTF-8 controls for call operands of short-circuit expressions. -/
public def logicalCallControls : List Control := [
  ⟨"logical-call-module-effects", moduleSuccess, .exportedInt 7⟩,
  ⟨"logical-call-and-binds-before-or", precedenceSuccess, .exportedInt 7⟩,
  ⟨"logical-call-parentheses", groupedSuccess, .exportedInt 7⟩,
  ⟨"logical-call-in-assignment-and-return", suiteSuccess, .exportedInt 7⟩,
  ⟨"logical-call-left-error-masks-both-operands", moduleFailure, .missingArgument "required"⟩,
  ⟨"logical-call-skipped-operand-still-resolves", "# 雪\nout=7 or missing()", .undefinedName "missing"⟩,
  ⟨"logical-calls-in-spread-operand", sourceSetup ++ "out=take(*(list(xs) or ys))", .exportedInt 7⟩]

#guard logicalCallControls.all fun control => decide (observe control.source = some control.expected)

private def listTags (state : Lists.State) : List Int :=
  state.heap.toList.filterMap fun cell =>
    match cell.contents with | .list [.scalar (.int value)] => some value | _ => none

private def successfulTrace (source : String) : Option (List Int) :=
  match runUtf8 source.toUTF8 with
  | .ok (.ok _ state) => some (listTags state)
  | _ => none

#guard decide (successfulTrace moduleSuccess = some [1, 2, 3, 1, 2])
#guard decide (successfulTrace precedenceSuccess = some [1, 2, 3, 1])
#guard decide (successfulTrace groupedSuccess = some [1, 2, 3, 1, 2])
#guard decide (successfulTrace suiteSuccess = some [1, 2, 3, 1, 2])

private def firstErrorRetainsPrefix : Bool :=
  match runUtf8 moduleFailure.toUTF8 with
  | .ok (.error (.runtime (.missingArguments ["required"])) state) =>
    listTags state == [1, 2, 3, 1] &&
      !state.heap.any (fun cell =>
        match cell.contents with | .binding (some (.scalar (.int 99))) => true | _ => false)
  | _ => false

#guard firstErrorRetainsPrefix

private def logicalSpans : Option (Span × List (Span × Span × List Span)) := do
  let bytes := "# 雪\r\nout=f() or g()(2) and h(3) or k(4)".toUTF8
  let [source] ← (parseFileUtf8 bytes).toOption | none
  let .assignCall "out" value := source.command | none
  let parsed ← (parseUtf8 bytes).toOption
  let [command] := parsed.commands | none
  match command.command with
  | .assign "out" (.logical .or
      (.logical .or (.call (.scalar (.read "f")) [] [] none none)
        (.logical .and
          (.call (.call (.scalar (.read "g")) [] [] none none) [.scalar (.int 2)] [] none none)
          (.call (.scalar (.read "h")) [.scalar (.int 3)] [] none none)))
      (.call (.scalar (.read "k")) [.scalar (.int 4)] [] none none)) =>
    return (value.span, command.applications.map fun app => (app.span, app.callee, app.operands.ordered))
  | _ => none

example : logicalSpans = some (⟨⟨11, 2, 5⟩, ⟨41, 2, 35⟩⟩, [
    (⟨⟨11, 2, 5⟩, ⟨14, 2, 8⟩⟩, ⟨⟨11, 2, 5⟩, ⟨12, 2, 6⟩⟩, []),
    (⟨⟨18, 2, 12⟩, ⟨24, 2, 18⟩⟩, ⟨⟨18, 2, 12⟩, ⟨21, 2, 15⟩⟩, [⟨⟨22, 2, 16⟩, ⟨23, 2, 17⟩⟩]),
    (⟨⟨18, 2, 12⟩, ⟨21, 2, 15⟩⟩, ⟨⟨18, 2, 12⟩, ⟨19, 2, 13⟩⟩, []),
    (⟨⟨29, 2, 23⟩, ⟨33, 2, 27⟩⟩, ⟨⟨29, 2, 23⟩, ⟨30, 2, 24⟩⟩, [⟨⟨31, 2, 25⟩, ⟨32, 2, 26⟩⟩]),
    (⟨⟨37, 2, 31⟩, ⟨41, 2, 35⟩⟩, ⟨⟨37, 2, 31⟩, ⟨38, 2, 32⟩⟩, [⟨⟨39, 2, 33⟩, ⟨40, 2, 34⟩⟩])]) :=
  by decide +kernel

private def groupedOperandSpans : Option (List Span × List Span) := do
  let parsed ← (parseUtf8 "# 雪\nout=id((f() and g() and h()))".toUTF8).toOption
  let [command] := parsed.commands | none
  match command.command with
  | .assign "out" (.call (.scalar (.read "id"))
      [.logical .and
        (.logical .and (.call (.scalar (.read "f")) [] [] none none)
          (.call (.scalar (.read "g")) [] [] none none))
        (.call (.scalar (.read "h")) [] [] none none)] [] none none) =>
    return ((← command.callSpans).ordered, command.nestedCalls.map ApplicationSpans.span)
  | _ => none

example : groupedOperandSpans = some ([⟨⟨13, 2, 8⟩, ⟨34, 2, 29⟩⟩], [
    ⟨⟨14, 2, 9⟩, ⟨17, 2, 12⟩⟩, ⟨⟨22, 2, 17⟩, ⟨25, 2, 20⟩⟩, ⟨⟨30, 2, 25⟩, ⟨33, 2, 28⟩⟩]) :=
  by decide +kernel

private def standaloneDiagnostic : Option Diagnostic :=
  match parseFunctionUtf8 "def relay(f):\n  return False and f()".toUTF8 with
  | .error diagnostic => some diagnostic
  | .ok _ => none

example : standaloneDiagnostic =
    some ⟨.unsupported .call, ⟨⟨34, 2, 21⟩, ⟨35, 2, 22⟩⟩⟩ := by decide +kernel

end Silmaril.Languages.Starlark.Frontend.Module
