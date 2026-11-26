module

public import Silmaril.Languages.Starlark.Frontend.Module.Checks
import all Silmaril.Languages.Starlark.Frontend.Module.Checks

namespace Silmaril.Languages.Starlark.Frontend.Module

private def modulePrefix :=
  "# 雪\ndef id(x):\n  return x\ndef f():\n  return 0\ndef _choose():\n  return id\n"

/-- Shared executable controls for call-valued returns. -/
public def returnCallControls : List Control := [
  ⟨"return-call-through-global",
    modulePrefix ++ "def relay(value):\n  return id(value)\nout=relay(8)", .exportedInt 8⟩,
  ⟨"return-postfix-through-shadowing-parameter",
    modulePrefix ++
      "def relay(f, enabled):\n  if enabled:\n    return f()(7)\n  else:\n    return 0\nout=relay(_choose, True)",
    .exportedInt 7⟩,
  ⟨"return-callee-error-masks-operand",
    "# 雪\ndef take(a):\n  return a\ndef need(x):\n  return x\n" ++
      "def relay(factory):\n  return factory()(need())\nout=relay(take)", .missingArgument "a"⟩,
  ⟨"undefined-return-callee", "# 雪\ndef relay():\n  return missing(7)\nout=relay()", .undefinedName "missing"⟩]

#guard returnCallControls.all fun control => decide (observe control.source = some control.expected)

private def returnText := "# 雪\r\ndef relay(f):\r\n  return f()(7)"

private def returnSpans : Option (List (Span × Span × List Span)) := do
  let parsed ← (parseUtf8 returnText.toUTF8).toOption
  let [command] := parsed.commands | none
  match command.command with
  | .define "relay" _ (.ret (some (.call (.call (.scalar (.read "f")) [] [] none none)
      [.scalar (.int 7)] [] none none))) =>
    return command.applications.map fun app => (app.span, app.callee, app.operands.ordered)
  | _ => none

example : returnSpans = some [
    (⟨⟨31, 3, 10⟩, ⟨37, 3, 16⟩⟩, ⟨⟨31, 3, 10⟩, ⟨34, 3, 13⟩⟩, [⟨⟨35, 3, 14⟩, ⟨36, 3, 15⟩⟩]),
    (⟨⟨31, 3, 10⟩, ⟨34, 3, 13⟩⟩, ⟨⟨31, 3, 10⟩, ⟨32, 3, 11⟩⟩, [])] := by decide +kernel

example : frontendDiagnostic "def relay(f):\n  tmp=f()\n  return tmp" =
    some ⟨.unsupported .call, ⟨⟨21, 2, 8⟩, ⟨22, 2, 9⟩⟩⟩ := by decide +kernel

private def standaloneDiagnostic : Option Diagnostic :=
  match parseFunctionUtf8 returnText.toUTF8 with
  | .error diagnostic => some diagnostic
  | .ok _ => none

example : standaloneDiagnostic =
    some ⟨.unsupported .call, ⟨⟨32, 3, 11⟩, ⟨33, 3, 12⟩⟩⟩ := by decide +kernel

end Silmaril.Languages.Starlark.Frontend.Module
