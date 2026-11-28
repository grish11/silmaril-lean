module

public import Silmaril.Languages.Starlark.Frontend.Module.Checks
import all Silmaril.Languages.Starlark.Frontend.Module.Checks

namespace Silmaril.Languages.Starlark.Frontend.Module

private def branchBody :=
  "# 雪\nsaved=False\ndef f():\n  return 0\ndef id(x):\n  return x\ndef _factory():\n  return id\n" ++
  "def relay(f, enabled):\n  if enabled:\n    saved = f()(7)\n  return saved\n"
private def branchSuccess := branchBody ++ "result=relay(_factory, True)\nout=0 if saved else result"
private def branchSkipped := branchBody ++ "out=relay(_factory, False)"
private def assignmentFailure :=
  "# 雪\ndef take(a):\n  return a\ndef need(b):\n  return b\n" ++
  "def relay(f):\n  saved=41\n  saved=f()\n  marker=99\n  after=need()\n  return saved\nout=relay(take)\nlater=101"

/-- Shared module controls for name assignments whose RHS is a call. -/
public def assignmentCallControls : List Control := [
  ⟨"body-call-assignment-branch-and-shadowing", branchSuccess, .exportedInt 7⟩,
  ⟨"body-call-assignment-creates-local-even-in-skipped-branch", branchSkipped, .uninitializedLocal "saved"⟩,
  ⟨"body-call-assignment-error-preempts-later-writes", assignmentFailure, .missingArgument "a"⟩]

#guard assignmentCallControls.all fun control => decide (observe control.source = some control.expected)

-- The read of saved and the write target use the same local slot.
-- The callee f is the parameter, so the declaration needs no global capture.
private def resolvedBranch : Bool := Id.run do
  let .ok parsed := parseUtf8 branchSuccess.toUTF8 | return false
  let .ok resolved := Modules.Resolve.resolve parsed.toCommands | return false
  let some relay := resolved.program[3]? | return false
  match relay.free, relay.locals, relay.body with
  | [], [⟨.local, "saved"⟩], .seq
      (.branchExpr (.atom (.read (.bound ⟨.local, "enabled"⟩)))
        (.assignExpr ⟨.local, "saved"⟩ (.call
          (.call (.atom (.read (.bound ⟨.local, "f"⟩))) [] [] none none)
          [.atom (.scalar (.int 7))] [] none none)) _)
      (.returnExpr (.atom (.read (.bound ⟨.local, "saved"⟩)))) => return true
  | _, _, _ => return false

#guard resolvedBranch

private def integersAfterFailure : Option (List Int) :=
  match runUtf8 assignmentFailure.toUTF8 with
  | .ok (.error (.runtime (.missingArguments ["a"])) state) =>
    some (state.heap.toList.filterMap fun cell =>
      match cell.contents with
      | .binding (some (.scalar (.int value))) => some value
      | _ => none)
  | _ => none

-- The earlier value is retained. Neither the failed write nor the later
-- writes to marker and later reach the heap.
#guard decide (integersAfterFailure = some [41])

private def assignmentText := "# 雪\r\ndef relay(f):\r\n  saved = f()(7)\r\n  return saved"

private def assignmentSpans : Option (Span × List (Span × Span × List Span)) := do
  let [source] ← (parseFileUtf8 assignmentText.toUTF8).toOption | none
  let .define fn := source.command | none
  let [⟨statement, .assignCall "saved" _⟩, _] := fn.body | none
  let parsed ← (parseUtf8 assignmentText.toUTF8).toOption
  let [command] := parsed.commands | none
  match command.command with
  | .define "relay" _ (.seq
      (.assign "saved" (.call (.call (.scalar (.read "f")) [] [] none none)
        [.scalar (.int 7)] [] none none))
      (.ret (some (.scalar (.read "saved"))))) =>
    return (statement, command.applications.map fun app => (app.span, app.callee, app.operands.ordered))
  | _ => none

example : assignmentSpans = some (⟨⟨24, 3, 3⟩, ⟨38, 3, 17⟩⟩, [
    (⟨⟨32, 3, 11⟩, ⟨38, 3, 17⟩⟩, ⟨⟨32, 3, 11⟩, ⟨35, 3, 14⟩⟩, [⟨⟨36, 3, 15⟩, ⟨37, 3, 16⟩⟩]),
    (⟨⟨32, 3, 11⟩, ⟨35, 3, 14⟩⟩, ⟨⟨32, 3, 11⟩, ⟨33, 3, 12⟩⟩, [])]) := by decide +kernel

example : frontendDiagnostic "def relay(f):\n  saved=f() + 0\n  return saved" =
    some ⟨.unsupported .operator, ⟨⟨26, 2, 13⟩, ⟨27, 2, 14⟩⟩⟩ := by decide +kernel

private def standaloneDiagnostic : Option Diagnostic :=
  match parseFunctionUtf8 assignmentText.toUTF8 with
  | .error diagnostic => some diagnostic
  | .ok _ => none

example : standaloneDiagnostic =
    some ⟨.unsupported .call, ⟨⟨33, 3, 12⟩, ⟨34, 3, 13⟩⟩⟩ := by decide +kernel

end Silmaril.Languages.Starlark.Frontend.Module
