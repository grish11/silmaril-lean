module

public import Silmaril.Languages.Starlark.Frontend.Module.Checks
import all Silmaril.Languages.Starlark.Frontend.Module.Checks

namespace Silmaril.Languages.Starlark.Frontend.Module

private def listSetup := "# 雪\nxs=[1]\nys=[2]\n"
private def moduleSuccess := listSetup ++ "list(xs); list(ys); out=7"
private def suiteBody := listSetup ++
  "def relay(f, enabled):\n  if enabled:\n    f(xs); f(ys)\n  return 7\n"
private def suiteSuccess := suiteBody ++ "out=relay(list, True)"
private def suiteSkipped := suiteBody ++ "out=relay(list, False)"
private def failureSetup := listSetup ++ "def need(x, required):\n  return x\n"
private def moduleFailure := failureSetup ++ "need(list(xs)); list(ys); out=7"
private def suiteFailure := failureSetup ++
  "def relay():\n  need(list(xs)); marker=99; list(ys)\n  return marker\nout=relay()\nlater=101"

/-- Shared module controls for calls whose return value is discarded. -/
public def callStatementControls : List Control := [
  ⟨"module-call-statements-before-semicolon", moduleSuccess, .exportedInt 7⟩,
  ⟨"suite-call-statements-in-branch", suiteSuccess, .exportedInt 7⟩,
  ⟨"suite-call-statements-skipped-branch", suiteSkipped, .exportedInt 7⟩,
  ⟨"module-call-statement-masks-following-statements", moduleFailure, .missingArgument "required"⟩,
  ⟨"suite-call-statement-masks-following-statements", suiteFailure, .missingArgument "required"⟩]

#guard callStatementControls.all fun control => decide (observe control.source = some control.expected)

private def listValues (state : Lists.State) : List (List Lists.Value) :=
  state.heap.toList.filterMap fun cell =>
    match cell.contents with | .list values => some values | _ => none

private def publishedState (source : String) : Option (List String × List (List Lists.Value)) :=
  match runUtf8 source.toUTF8 with
  | .ok (.ok published state) => some (published.exports.map Prod.fst, listValues state)
  | _ => none

private def values (elements : List Int) : List (List Lists.Value) :=
  elements.map fun element => [.scalar (.int element)]

-- The discarded lists remain in the heap in evaluation order. The export
-- lists contain only the source declarations and assignments.
#guard decide (publishedState moduleSuccess = some (["xs", "ys", "out"], values [1, 2, 1, 2]))
#guard decide (publishedState suiteSuccess = some (["xs", "ys", "relay", "out"], values [1, 2, 1, 2]))
#guard decide (publishedState suiteSkipped = some (["xs", "ys", "relay", "out"], values [1, 2]))

private def effectsBeforeFailure (source : String) : Bool :=
  match runUtf8 source.toUTF8 with
  | .ok (.error (.runtime (.missingArguments ["required"])) state) =>
    decide (listValues state = values [1, 2, 1]) &&
      !state.heap.any (fun cell =>
        match cell.contents with
        | .binding (some (.scalar (.int _))) => true
        | _ => false)
  | _ => false

#guard effectsBeforeFailure moduleFailure && effectsBeforeFailure suiteFailure

private def resolvedSuite : Bool := Id.run do
  let .ok parsed := parseUtf8 suiteSuccess.toUTF8 | return false
  let .ok resolved := Modules.Resolve.resolve parsed.toCommands | return false
  let [relay] := resolved.program.toList | return false
  match relay.locals, relay.body with
  | [], .seq (.branchExpr _ (.seq (.evalExpr (.call ..)) (.evalExpr (.call ..))) _)
      (.returnExpr (.atom (.scalar (.int 7)))) => return true
  | _, _ => return false

#guard resolvedSuite

private def expressionSpans : Option (List (Span × List (Span × Span × List Span))) := do
  let source := "# 雪\r\nf()(1); out=7\r\ndef relay(f):\r\n  f()(2); return 8"
  let [_, _, function] ← (parseFileUtf8 source.toUTF8).toOption | none
  let .define fn := function.command | none
  let [⟨bodySpan, .evalCall _⟩, _] := fn.body | none
  let parsed ← (parseUtf8 source.toUTF8).toOption
  let [top, following, relay] := parsed.commands | none
  match top.command, following.command, relay.command with
  | .eval (.call (.call (.scalar (.read "f")) [] [] none none) [.scalar (.int 1)] [] none none),
      .assign "out" (.scalar (.int 7)),
      .define "relay" _ (.seq
        (.eval (.call (.call (.scalar (.read "f")) [] [] none none) [.scalar (.int 2)] [] none none))
        (.ret (some (.scalar (.int 8))))) =>
    let locations := fun command : LocatedCommand =>
      command.applications.map fun app => (app.span, app.callee, app.operands.ordered)
    return [(top.span, locations top), (bodySpan, locations relay)]
  | _, _, _ => none

example : expressionSpans = some [
    (⟨⟨7, 2, 1⟩, ⟨13, 2, 7⟩⟩, [
      (⟨⟨7, 2, 1⟩, ⟨13, 2, 7⟩⟩, ⟨⟨7, 2, 1⟩, ⟨10, 2, 4⟩⟩, [⟨⟨11, 2, 5⟩, ⟨12, 2, 6⟩⟩]),
      (⟨⟨7, 2, 1⟩, ⟨10, 2, 4⟩⟩, ⟨⟨7, 2, 1⟩, ⟨8, 2, 2⟩⟩, [])]),
    (⟨⟨39, 4, 3⟩, ⟨45, 4, 9⟩⟩, [
      (⟨⟨39, 4, 3⟩, ⟨45, 4, 9⟩⟩, ⟨⟨39, 4, 3⟩, ⟨42, 4, 6⟩⟩, [⟨⟨43, 4, 7⟩, ⟨44, 4, 8⟩⟩]),
      (⟨⟨39, 4, 3⟩, ⟨42, 4, 6⟩⟩, ⟨⟨39, 4, 3⟩, ⟨40, 4, 4⟩⟩, [])])] := by decide +kernel

example : frontendDiagnostic "def relay(f):\n  f() + 0\n  return 7" =
    some ⟨.unsupported .operator, ⟨⟨20, 2, 7⟩, ⟨21, 2, 8⟩⟩⟩ := by decide +kernel

private def standaloneDiagnostic : Option Diagnostic :=
  match parseFunctionUtf8 "def relay(f):\n  f()\n  return 7".toUTF8 with
  | .error diagnostic => some diagnostic
  | .ok _ => none

example : standaloneDiagnostic =
    some ⟨.unsupported .call, ⟨⟨17, 2, 4⟩, ⟨18, 2, 5⟩⟩⟩ := by decide +kernel

end Silmaril.Languages.Starlark.Frontend.Module
