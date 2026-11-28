module

public import Silmaril.Languages.Starlark.Frontend.Module.Checks
import all Silmaril.Languages.Starlark.Frontend.Module.Checks

namespace Silmaril.Languages.Starlark.Frontend.Module

private def sourceSetup :=
  "# 雪\nxs=[1]\nys=[2]\nzs=[3]\ndef take(x):\n  return 7\n" ++
  "def truthy(x):\n  return True\ndef falsy(x):\n  return False\ndef need(x, required):\n  return x\n"
private def moduleSuccess :=
  sourceSetup ++ "out=take(list(xs)) if truthy(list(ys)) else need(list(zs))"
private def suiteSuccess := sourceSetup ++
  "def relay(f):\n  saved=need(list(xs)) if falsy(list(ys)) else f(list(zs)) if truthy(list(xs)) else need()\n" ++
  "  return f(saved) if truthy(list(ys)) else need()\nout=relay(take)"
private def conditionFailure :=
  sourceSetup ++ "out=take(list(xs)) if need(list(ys)) else take(list(zs))\nmarker=99"
private def thenFailure :=
  sourceSetup ++ "out=need(list(xs)) if truthy(list(ys)) else take(list(zs))\nmarker=99"
private def elseFailure := sourceSetup ++
  "def relay():\n  return take(list(xs)) if falsy(list(ys)) else need(list(zs))\nout=relay()\nmarker=99"

/-- Shared UTF-8 controls for postfix calls in conditional expressions. -/
public def conditionalCallControls : List Control := [
  ⟨"conditional-runs-condition-before-then-call", moduleSuccess, .exportedInt 7⟩,
  ⟨"conditional-nested-else-and-return-in-suite", suiteSuccess, .exportedInt 7⟩,
  ⟨"conditional-condition-error-masks-both-arms", conditionFailure, .missingArgument "required"⟩,
  ⟨"conditional-selected-then-error", thenFailure, .missingArgument "required"⟩,
  ⟨"conditional-selected-else-error-in-suite", elseFailure, .missingArgument "required"⟩,
  ⟨"conditional-call-in-operand",
    sourceSetup ++ "out=take(take(list(xs)) if truthy(list(ys)) else need())", .exportedInt 7⟩]

#guard conditionalCallControls.all fun control => decide (observe control.source = some control.expected)

private def listTags (state : Lists.State) : List Int :=
  state.heap.toList.filterMap fun cell =>
    match cell.contents with | .list [.scalar (.int value)] => some value | _ => none

private def successfulTrace (source : String) : Option (List Int) :=
  match runUtf8 source.toUTF8 with
  | .ok (.ok _ state) => some (listTags state)
  | _ => none

-- The condition's copy precedes the chosen arm's copy, including in the
-- right-nested alternative. Skipped arms add no allocations.
#guard decide (successfulTrace moduleSuccess = some [1, 2, 3, 2, 1])
#guard decide (successfulTrace suiteSuccess = some [1, 2, 3, 2, 1, 3, 2])

private def failedTrace (source : String) : Option (List Int) :=
  match runUtf8 source.toUTF8 with
  | .ok (.error (.runtime (.missingArguments ["required"])) state) =>
    if state.heap.any (fun cell =>
      match cell.contents with | .binding (some (.scalar (.int 99))) => true | _ => false)
    then none
    else some (listTags state)
  | _ => none

#guard decide (failedTrace conditionFailure = some [1, 2, 3, 2])
#guard decide (failedTrace thenFailure = some [1, 2, 3, 2, 1])
#guard decide (failedTrace elseFailure = some [1, 2, 3, 2, 3])

private def conditionalSpans : Option (List Span × List (Span × Span × List Span)) := do
  let bytes := "# 雪\r\nout=f() or g()(2) if p() and q() else h(3) if r() else k(4)".toUTF8
  let [source] ← (parseFileUtf8 bytes).toOption | none
  let .assignCall "out" (.conditional span test yes no) := source.command | none
  let parsed ← (parseUtf8 bytes).toOption
  let [command] := parsed.commands | none
  match command.command with
  | .assign "out" (.conditional
      (.logical .and (.call (.scalar (.read "p")) [] [] none none)
        (.call (.scalar (.read "q")) [] [] none none))
      (.logical .or (.call (.scalar (.read "f")) [] [] none none)
        (.call (.call (.scalar (.read "g")) [] [] none none) [.scalar (.int 2)] [] none none))
      (.conditional (.call (.scalar (.read "r")) [] [] none none)
        (.call (.scalar (.read "h")) [.scalar (.int 3)] [] none none)
        (.call (.scalar (.read "k")) [.scalar (.int 4)] [] none none))) =>
    return ([span, yes.span, test.span, no.span],
      command.applications.map fun app => (app.span, app.callee, app.operands.ordered))
  | _ => none

example : conditionalSpans = some ([
    ⟨⟨11, 2, 5⟩, ⟨66, 2, 60⟩⟩, ⟨⟨11, 2, 5⟩, ⟨24, 2, 18⟩⟩,
    ⟨⟨28, 2, 22⟩, ⟨39, 2, 33⟩⟩, ⟨⟨45, 2, 39⟩, ⟨66, 2, 60⟩⟩], [
    (⟨⟨11, 2, 5⟩, ⟨14, 2, 8⟩⟩, ⟨⟨11, 2, 5⟩, ⟨12, 2, 6⟩⟩, []),
    (⟨⟨18, 2, 12⟩, ⟨24, 2, 18⟩⟩, ⟨⟨18, 2, 12⟩, ⟨21, 2, 15⟩⟩, [⟨⟨22, 2, 16⟩, ⟨23, 2, 17⟩⟩]),
    (⟨⟨18, 2, 12⟩, ⟨21, 2, 15⟩⟩, ⟨⟨18, 2, 12⟩, ⟨19, 2, 13⟩⟩, []),
    (⟨⟨28, 2, 22⟩, ⟨31, 2, 25⟩⟩, ⟨⟨28, 2, 22⟩, ⟨29, 2, 23⟩⟩, []),
    (⟨⟨36, 2, 30⟩, ⟨39, 2, 33⟩⟩, ⟨⟨36, 2, 30⟩, ⟨37, 2, 31⟩⟩, []),
    (⟨⟨45, 2, 39⟩, ⟨49, 2, 43⟩⟩, ⟨⟨45, 2, 39⟩, ⟨46, 2, 40⟩⟩, [⟨⟨47, 2, 41⟩, ⟨48, 2, 42⟩⟩]),
    (⟨⟨53, 2, 47⟩, ⟨56, 2, 50⟩⟩, ⟨⟨53, 2, 47⟩, ⟨54, 2, 48⟩⟩, []),
    (⟨⟨62, 2, 56⟩, ⟨66, 2, 60⟩⟩, ⟨⟨62, 2, 56⟩, ⟨63, 2, 57⟩⟩, [⟨⟨64, 2, 58⟩, ⟨65, 2, 59⟩⟩])]) :=
  by decide +kernel

private def standaloneDiagnostic : Option Diagnostic :=
  match parseFunctionUtf8 "def relay(f):\n  return 7 if f() else 0".toUTF8 with
  | .error diagnostic => some diagnostic
  | .ok _ => none

example : standaloneDiagnostic =
    some ⟨.unsupported .call, ⟨⟨29, 2, 16⟩, ⟨30, 2, 17⟩⟩⟩ := by decide +kernel

end Silmaril.Languages.Starlark.Frontend.Module
