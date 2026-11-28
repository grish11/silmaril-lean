module

public import Silmaril.Languages.Starlark.Frontend.Module.Checks
import all Silmaril.Languages.Starlark.Frontend.Module.Checks

namespace Silmaril.Languages.Starlark.Frontend.Module

private def setup :=
  "# 雪\nxs=[1]\nys=[2]\nzs=[3]\nws=[4]\n" ++
  "def take(x):\n  return 7\ndef truthy(x):\n  return True\ndef falsy(x):\n  return False\n" ++
  "def need(x, required):\n  return x\n"
private def firstArm := setup ++
  "def relay(falsy):\n  if falsy(list(xs)) or need(list(ys)) and need(list(ws)):\n" ++
  "    saved=take(list(zs))\n  elif need(list(ys)):\n    saved=0\n  else:\n    saved=need()\n" ++
  "  list(ws)\n  return saved\nout=relay(truthy)"
private def elifArm := setup ++
  "def relay():\n  if falsy(list(xs)):\n    return need()\n" ++
  "  elif truthy(list(zs)) if truthy(list(ys)) else need():\n    return take(list(ws))\n" ++
  "  elif need(list(xs)):\n    return 0\n  return 1\nout=relay()"
private def elseArm := setup ++
  "def relay():\n  if falsy(list(xs)):\n    return need()\n  elif falsy(list(ys)):\n    return need()\n" ++
  "  else:\n    if falsy(list(zs)):\n      need()\n    return take(list(ws))\nout=relay()"
private def firstFailure := setup ++
  "def relay():\n  if need(list(xs)):\n    list(ys)\n  elif truthy(list(zs)):\n    list(ws)\n" ++
  "  else:\n    list(xs)\n  marker=99\n  return marker\nout=relay()\nlater=101"
private def elifFailure := setup ++
  "def relay():\n  if falsy(list(xs)):\n    list(zs)\n  elif need(list(ys)):\n    list(ws)\n" ++
  "  elif truthy(list(zs)):\n    list(xs)\n  else:\n    list(xs)\n" ++
  "  marker=99\n  return marker\nout=relay()\nlater=101"

/-- Shared UTF-8 module observations for call-containing branch tests. -/
public def branchCallControls : List Control := [
  ⟨"if-short-circuits-and-skips-later-elifs", firstArm, .exportedInt 7⟩,
  ⟨"elif-conditional-tests-before-selected-suite", elifArm, .exportedInt 7⟩,
  ⟨"else-suite-nested-if-without-else", elseArm, .exportedInt 7⟩,
  ⟨"if-condition-error-masks-all-suites", firstFailure, .missingArgument "required"⟩,
  ⟨"elif-condition-error-masks-later-tests-and-suites", elifFailure, .missingArgument "required"⟩,
  ⟨"skipped-elif-still-resolves-its-test",
    "# 雪\ndef relay():\n  if True:\n    return 7\n  elif missing():\n    return 0\nout=relay()",
    .undefinedName "missing"⟩]

#guard branchCallControls.all fun control => decide (observe control.source = some control.expected)

private def listTags (state : Lists.State) : List Int :=
  state.heap.toList.filterMap fun cell =>
    match cell.contents with | .list [.scalar (.int value)] => some value | _ => none

private def successfulTrace (source : String) : Option (List Int) :=
  match runUtf8 source.toUTF8 with
  | .ok (.ok _ state) => some (listTags state)
  | _ => none

#guard decide (successfulTrace firstArm = some [1, 2, 3, 4, 1, 3, 4])
#guard decide (successfulTrace elifArm = some [1, 2, 3, 4, 1, 2, 3, 4])
#guard decide (successfulTrace elseArm = some [1, 2, 3, 4, 1, 2, 3, 4])

private def failedTrace (source : String) : Option (List Int) :=
  match runUtf8 source.toUTF8 with
  | .ok (.error (.runtime (.missingArguments ["required"])) state) =>
    if state.heap.any (fun cell =>
      match cell.contents with
      | .binding (some (.scalar (.int value))) => value == 99 || value == 101
      | _ => false)
    then none
    else some (listTags state)
  | _ => none

#guard decide (failedTrace firstFailure = some [1, 2, 3, 4, 1])
#guard decide (failedTrace elifFailure = some [1, 2, 3, 4, 1, 2])

/-- Both parsers check the heading test positions on this CRLF source. -/
public def branchSpanSource :=
  "# 雪\r\ndef relay(f, g, p, q):\r\n  if f()(1) or g() and p():\r\n    return g(7)\r\n" ++
  "  elif g(2) if p() else q(3):\r\n    return 8\r\n  else:\r\n    return q(9)"

public def branchTestSpans : List Span :=
  [⟨⟨36, 3, 6⟩, ⟨57, 3, 27⟩⟩, ⟨⟨84, 5, 8⟩, ⟨105, 5, 29⟩⟩]

private def branchSpans : Option (List Span × List (Span × Span × List Span)) := do
  let [source] ← (parseFileUtf8 branchSpanSource.toUTF8).toOption | none
  let .define fn := source.command | none
  let [⟨_, .branch test _ [⟨_, .branch elifTest _ _⟩]⟩] := fn.body | none
  let parsed ← (parseUtf8 branchSpanSource.toUTF8).toOption
  let [command] := parsed.commands | none
  match command.command with
  | .define "relay" _ (.branch
      (.logical .or (.call (.call (.scalar (.read "f")) [] [] none none) [.scalar (.int 1)] [] none none)
        (.logical .and (.call (.scalar (.read "g")) [] [] none none)
          (.call (.scalar (.read "p")) [] [] none none)))
      (.ret (some (.call (.scalar (.read "g")) [.scalar (.int 7)] [] none none)))
      (.branch
        (.conditional (.call (.scalar (.read "p")) [] [] none none)
          (.call (.scalar (.read "g")) [.scalar (.int 2)] [] none none)
          (.call (.scalar (.read "q")) [.scalar (.int 3)] [] none none))
        (.ret (some (.scalar (.int 8))))
        (.ret (some (.call (.scalar (.read "q")) [.scalar (.int 9)] [] none none))))) =>
    return ([test.span, elifTest.span],
      command.applications.map fun app => (app.span, app.callee, app.operands.ordered))
  | _ => none

example : branchSpans = some (branchTestSpans, [
    (⟨⟨36, 3, 6⟩, ⟨42, 3, 12⟩⟩, ⟨⟨36, 3, 6⟩, ⟨39, 3, 9⟩⟩, [⟨⟨40, 3, 10⟩, ⟨41, 3, 11⟩⟩]),
    (⟨⟨36, 3, 6⟩, ⟨39, 3, 9⟩⟩, ⟨⟨36, 3, 6⟩, ⟨37, 3, 7⟩⟩, []),
    (⟨⟨46, 3, 16⟩, ⟨49, 3, 19⟩⟩, ⟨⟨46, 3, 16⟩, ⟨47, 3, 17⟩⟩, []),
    (⟨⟨54, 3, 24⟩, ⟨57, 3, 27⟩⟩, ⟨⟨54, 3, 24⟩, ⟨55, 3, 25⟩⟩, []),
    (⟨⟨71, 4, 12⟩, ⟨75, 4, 16⟩⟩, ⟨⟨71, 4, 12⟩, ⟨72, 4, 13⟩⟩, [⟨⟨73, 4, 14⟩, ⟨74, 4, 15⟩⟩]),
    (⟨⟨84, 5, 8⟩, ⟨88, 5, 12⟩⟩, ⟨⟨84, 5, 8⟩, ⟨85, 5, 9⟩⟩, [⟨⟨86, 5, 10⟩, ⟨87, 5, 11⟩⟩]),
    (⟨⟨92, 5, 16⟩, ⟨95, 5, 19⟩⟩, ⟨⟨92, 5, 16⟩, ⟨93, 5, 17⟩⟩, []),
    (⟨⟨101, 5, 25⟩, ⟨105, 5, 29⟩⟩, ⟨⟨101, 5, 25⟩, ⟨102, 5, 26⟩⟩, [⟨⟨103, 5, 27⟩, ⟨104, 5, 28⟩⟩]),
    (⟨⟨142, 8, 12⟩, ⟨146, 8, 16⟩⟩, ⟨⟨142, 8, 12⟩, ⟨143, 8, 13⟩⟩, [⟨⟨144, 8, 14⟩, ⟨145, 8, 15⟩⟩])]) :=
  by decide +kernel

/-- Module heading diagnostics paired with the pinned parser's syntax decision. -/
public def branchSyntaxControls : List (String × String × DiagnosticKind × Bool) := [
  ("top-level-call-test", "# 雪\nif f():\n  pass", .topLevelIf, true),
  ("inline-call-test-suite", "def f():\n  if g(): pass", .unsupported .inlineSuite, true),
  ("call-test-after-semicolon", "def f():\n  pass; if g():\n    pass", .expected "a simple statement", false),
  ("call-test-missing-colon", "def f():\n  if g()\n    pass", .expected "':'", false),
  ("elif-conditional-missing-else", "def f():\n  if p():\n    pass\n  elif g() if p():\n    pass",
    .expected "'else'", false)]

#guard branchSyntaxControls.all fun (_, source, expected, _) =>
  (frontendDiagnostic source).map Diagnostic.kind == some expected

private def standaloneDiagnostic : Option Diagnostic :=
  match parseFunctionUtf8 branchSpanSource.toUTF8 with
  | .error diagnostic => some diagnostic
  | .ok _ => none

example : standaloneDiagnostic =
    some ⟨.unsupported .call, ⟨⟨37, 3, 7⟩, ⟨38, 3, 8⟩⟩⟩ := by decide +kernel

end Silmaril.Languages.Starlark.Frontend.Module
