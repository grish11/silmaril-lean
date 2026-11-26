module

public import Silmaril.Languages.Starlark.Frontend.Module.Checks
import all Silmaril.Languages.Starlark.Frontend.Module.Checks

namespace Silmaril.Languages.Starlark.Frontend.Module

private def fixturePrefix :=
  "# 雪\ndef target(x):\n  return 7\ndef choose(f, ignored, required):\n  return f\n" ++
  "def need(argument):\n  return argument\nxs=[1]\nys=[2]\n"
private def callSuccess := fixturePrefix ++ "out=choose(target, list(xs), 0)(list(ys))"
private def callFailure := fixturePrefix ++ "out=choose(target, list(xs))(list(ys))"

private def chainPrefix := fixturePrefix ++ "zs=[3]\nws=[4]\n"
private def chainSuccess := chainPrefix ++
  "out=choose(choose, list(xs), 0)(choose, list(ys), 0)(target, list(zs), 0)(list(ws))"
private def chainFailure := chainPrefix ++
  "out=choose(choose, list(xs), 0)(target, list(ys))(list(zs))(list(ws))"

/-- Module outcomes shared by the native frontend and the pinned Go oracle. -/
public def computedCallControls : List Control := [
  ⟨"factory-returns-callable", callSuccess, .exportedInt 7⟩,
  ⟨"computed-call-inside-spread", fixturePrefix ++ "out=target(*choose(list, 0, 0)(xs))", .exportedInt 7⟩,
  ⟨"failed-computed-callee", callFailure, .missingArgument "required"⟩,
  ⟨"callee-error-masks-operand-error", fixturePrefix ++ "out=choose(target, 0)(need())", .missingArgument "required"⟩,
  ⟨"noncallable-dispatch-follows-operands", fixturePrefix ++ "out=choose(0, 0, 0)(need())",
    .missingArgument "argument"⟩,
  ⟨"four-postfix-applications", chainSuccess, .exportedInt 7⟩,
  ⟨"middle-application-failure", chainFailure, .missingArgument "required"⟩,
  ⟨"middle-application-masks-later-errors",
    fixturePrefix ++ "out=choose(choose, 0, 0)(target, 0)(need())(need())", .missingArgument "required"⟩,
  ⟨"parenthesized-conditional-callee",
    fixturePrefix ++ "out=(target if True else later)(1)\nlater=need", .exportedInt 7⟩,
  ⟨"parenthesized-conditional-callee-in-spread",
    fixturePrefix ++ "out=target(*(list if True else later)(xs))\nlater=list", .exportedInt 7⟩,
  ⟨"parenthesized-callee-error-masks-operand",
    fixturePrefix ++ "out=(target if flag else need)(need())\nflag=True", .uninitializedGlobal "flag"⟩]

#guard computedCallControls.all fun control => decide (observe control.source = some control.expected)

private def listTrace (source : String) : Option (List (List Lists.Value)) := do
  let result ← (runUtf8 source.toUTF8).toOption
  let state := match result with
    | .ok _ state | .error _ state => state
  return state.heap.toList.filterMap fun cell =>
    match cell.contents with | .list values => some values | _ => none

-- The factory's copy of xs precedes the operand's copy of ys, each once.
#guard decide (listTrace callSuccess = some [[.scalar (.int 1)], [.scalar (.int 2)],
  [.scalar (.int 1)], [.scalar (.int 2)]])

-- On callee failure only the factory's allocation survives.
#guard decide (listTrace callFailure = some [[.scalar (.int 1)], [.scalar (.int 2)], [.scalar (.int 1)]])

-- Each suffix runs after its callee has returned. The second application in
-- chainFailure allocates its operand before binding fails, then both later
-- operands are skipped.
#guard decide (listTrace chainSuccess = some
  (([1, 2, 3, 4, 1, 2, 3, 4] : List Int).map fun n => [.scalar (.int n)]))
#guard decide (listTrace chainFailure = some
  (([1, 2, 3, 4, 1, 2] : List Int).map fun n => [.scalar (.int n)]))

private def applicationSpans : Option (List (Span × Span × List Span)) := do
  let parsed ← (parseUtf8 "# 雪\r\nout=choose(f, x=2)(*xs, **kw)".toUTF8).toOption
  let [command] := parsed.commands | none
  match command.command with
  | .assign "out" (.call
      (.call (.scalar (.read "choose")) [.scalar (.read "f")] [("x", .scalar (.int 2))] none none)
      [] [] (some (.scalar (.read "xs"))) (some (.scalar (.read "kw")))) =>
    return command.applications.map fun entry => (entry.span, entry.callee, entry.operands.ordered)
  | _ => none

example : applicationSpans = some [
    (⟨⟨11, 2, 5⟩, ⟨36, 2, 30⟩⟩, ⟨⟨11, 2, 5⟩, ⟨25, 2, 19⟩⟩,
      [⟨⟨26, 2, 20⟩, ⟨29, 2, 23⟩⟩, ⟨⟨31, 2, 25⟩, ⟨35, 2, 29⟩⟩]),
    (⟨⟨11, 2, 5⟩, ⟨25, 2, 19⟩⟩, ⟨⟨11, 2, 5⟩, ⟨17, 2, 11⟩⟩,
      [⟨⟨18, 2, 12⟩, ⟨19, 2, 13⟩⟩, ⟨⟨21, 2, 15⟩, ⟨24, 2, 18⟩⟩])] := by decide +kernel

private def conditionalChainSpans : Option (List (Span × Span × List Span)) := do
  let source := "# 雪\r\nout=(f if flag else g)(1)(x=2)(*xs, **kw)\r\nnext=5"
  let parsed ← (parseUtf8 source.toUTF8).toOption
  let [command, following] := parsed.commands | none
  let .assign "next" (.scalar (.int 5)) := following.command | none
  match command.command with
  | .assign "out" (.call
      (.call
        (.call (.conditional (.scalar (.read "flag")) (.scalar (.read "f")) (.scalar (.read "g")))
          [.scalar (.int 1)] [] none none)
        [] [("x", .scalar (.int 2))] none none)
      [] [] (some (.scalar (.read "xs"))) (some (.scalar (.read "kw")))) =>
    return command.applications.map fun entry => (entry.span, entry.callee, entry.operands.ordered)
  | _ => none

example : conditionalChainSpans = some [
    (⟨⟨11, 2, 5⟩, ⟨48, 2, 42⟩⟩, ⟨⟨11, 2, 5⟩, ⟨37, 2, 31⟩⟩,
      [⟨⟨38, 2, 32⟩, ⟨41, 2, 35⟩⟩, ⟨⟨43, 2, 37⟩, ⟨47, 2, 41⟩⟩]),
    (⟨⟨11, 2, 5⟩, ⟨37, 2, 31⟩⟩, ⟨⟨11, 2, 5⟩, ⟨32, 2, 26⟩⟩,
      [⟨⟨33, 2, 27⟩, ⟨36, 2, 30⟩⟩]),
    (⟨⟨11, 2, 5⟩, ⟨32, 2, 26⟩⟩, ⟨⟨11, 2, 5⟩, ⟨29, 2, 23⟩⟩,
      [⟨⟨30, 2, 24⟩, ⟨31, 2, 25⟩⟩])] := by decide +kernel

private def chainLength (count : Nat) : Option Nat := do
  let parsed ← (parse ("out=f" ++ String.join (List.replicate count "()") ++ "\nnext=5")).toOption
  let [command, following] := parsed.commands | none
  let .assign "next" (.scalar (.int 5)) := following.command | none
  return command.applications.length

#guard decide (chainLength 24 = some 24)

example : frontendDiagnostic "out=f()()().value" =
    some ⟨.unsupported .call, ⟨⟨11, 1, 12⟩, ⟨12, 1, 13⟩⟩⟩ := by decide +kernel

end Silmaril.Languages.Starlark.Frontend.Module
