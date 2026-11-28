module

meta import Lean.Elab.Tactic.Cbv
public import Silmaril.Languages.Starlark.Frontend.Module.Loader.Thms
import all Silmaril.Languages.Starlark.Frontend.Module.Loader.Defs
import all Silmaril.Languages.Starlark.Frontend.Module.Checks
import all Silmaril.Languages.Starlark.Frontend.Module.Defs
import all Silmaril.Languages.Starlark.Frontend.Defs
import all Silmaril.Languages.Starlark.Frontend.Lexer.Defs
import all Silmaril.Languages.Starlark.Modules.Loader.Defs
import all Silmaril.Languages.Starlark.Modules.Resolve.Defs
import all Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Defs
import all Silmaril.Languages.Starlark.Functions.Denotation.Defs
import all Silmaril.Languages.Starlark.Functions.Expressions.Denotation.Defs
import all Silmaril.Languages.Starlark.Lists.Denotation.Defs
meta import Silmaril.Languages.Starlark.Modules.Loader.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Defs

namespace Silmaril.Languages.Starlark.Frontend.Module.Loader

public def producer : String := "# 雪\ndef id(x):\n  return x"
public def label : String := "pkg:dep"

private def success := "load(\"pkg:dep\", imported=\"id\")\nout = imported(7)"
private def direct := "load('pkg:dep', 'id',)\nout = id(9)"
private def missing := "load(\"pkg:dep\", imported=\"absent\")\nmarker = 99\nout = imported(7)"
private def late := "marker = 99\nload(\"pkg:dep\", imported=\"absent\")\nout = imported(7)"
private def privateName := "load(\"pkg:dep\", imported=\"_id\")\nout = imported(7)"
private def empty := "load(\"pkg:dep\",)"
private def nested := "def f():\n  load(\"pkg:dep\", \"id\")\n  return id"

private def wrapperPrefix := "# 橋\nload(\"pkg:dep\", imported=\"id\")\ndef relay():\n  return imported"
private def wrapper := wrapperPrefix ++ "(11)\nout = relay()"
private def failedWrapper := wrapperPrefix ++ "()\nout = relay()\nmarker = 99"

public inductive Observation where
  | exportedInt (value : Int)
  | wrapperExportedInt (value : Int)
  | missingExport (name : String)
  | wrapperArgumentError (name : String)
  | privateImport (name : String)
  | lateLoad | emptyLoad | loadInFunction
  deriving DecidableEq

public structure Control where
  name : String
  source : String
  expected : Observation

public def controls : List Control := [
  ⟨"renamed-callable-import", success, .exportedInt 7⟩,
  ⟨"direct-callable-import", direct, .exportedInt 9⟩,
  ⟨"missing-export-preempts-body", missing, .missingExport "absent"⟩,
  ⟨"late-load-policy", late, .lateLoad⟩,
  ⟨"private-export-validation", privateName, .privateImport "_id"⟩,
  ⟨"missing-import-operand", empty, .emptyLoad⟩,
  ⟨"function-local-load", nested, .loadInFunction⟩,
  ⟨"wrapper-returns-imported-call", wrapper, .wrapperExportedInt 11⟩,
  ⟨"wrapper-call-failure-preempts-suffix", failedWrapper, .wrapperArgumentError "x"⟩]

private def graph (consumer : String) : Array TextEntry :=
  #[⟨producer.toUTF8, []⟩, ⟨consumer.toUTF8, [(label, 0)]⟩]

private def observe (source : String) : Option Observation :=
  match loadUtf8 (graph source) 1 with
  | .ok (.ok published session) =>
    match published.exports, session.cache with
    | [("out", .scalar (.int value))], [(1, _), (0, _)] => some (.exportedInt value)
    | [("relay", .function address), ("out", .scalar (.int value))], [(1, _), (0, _)] =>
      match session.runtime.heap[address]? with
      | some ⟨.function closure, true⟩ =>
        if closure.declaration == 1 then some (.wrapperExportedInt value) else none
      | _ => none
    | _, _ => none
  | .ok (.error (.initialization 1 (.missingExport "pkg:dep" name)) session) =>
    -- The first consumer slot is `marker`. Its assignment would write 99.
    let marker : Option Lists.Cell := session.runtime.heap[0]?
    match session.cache, marker with
    | [(0, _)], some (Lists.Cell.mk (.binding none) _) => some (.missingExport name)
    | _, _ => none
  | .ok (.error (.initialization 1 (.runtime (.missingArguments [name]))) session) =>
    if session.cache.map Prod.fst == [0] && !session.runtime.heap.any (fun cell =>
        match cell.contents with
        | .binding (some (.scalar (.int 99))) => true
        | _ => false) then some (.wrapperArgumentError name)
    else none
  | .error (.intake 1 (.validation (.validation (.privateImport name)))) => some (.privateImport name)
  | .error (.intake 1 (.frontend ⟨.unsupported .lateLoad, _⟩)) => some .lateLoad
  | .error (.intake 1 (.frontend ⟨.expected "an imported name", _⟩)) => some .emptyLoad
  | .error (.intake 1 (.frontend ⟨.loadInFunction, _⟩)) => some .loadInFunction
  | _ => none

section

set_option maxRecDepth 6000
set_option maxHeartbeats 2500000

attribute [local cbv_eval] Modules.Resolve.compileBody.eq_def
  Silmaril.Languages.Starlark.Frontend.Module.readExpr_eq
  Silmaril.Languages.Starlark.Frontend.Module.startsWith_eq_prefix

example : observe success = some (.exportedInt 7) := by cbv
example : observe missing = some (.missingExport "absent") := by cbv

end

#guard controls.all fun control => decide (observe control.source = some control.expected)

-- The normal loader assigns the producer slot first. The wrapper's
-- return reads the file-local capture chosen by ordinary body resolution.
private def wrapperLayout : Bool := Id.run do
  let .ok prepared := prepare (graph wrapper) | return false
  let [dependency, consumer] := prepared.manifest.toList | return false
  let [.exec (.define "id" 0)] := dependency.source.commands | return false
  let [_, declaration] := prepared.program.toList | return false
  match consumer.source.commands, declaration.free, declaration.body with
  | [.load .., .exec (.define "relay" 1), .exec (.assignExpr "out" _)],
      [⟨⟨.local, "imported"⟩, ⟨.local, "imported"⟩⟩],
      .returnExpr (.call (.atom (.read (.bound ⟨.local, "imported"⟩)))
        [.atom (.scalar (.int 11))] [] none none) => return true
  | _, _, _ => return false

#guard wrapperLayout

private def loadSpans : Option (List Span) := do
  let commands ← (parseFileUtf8 "# 雪\nload(\"pkg:dep\", 'id', alias=\"other\",)".toUTF8).toOption
  match commands with
  | [⟨command, .load moduleLabel imports⟩] =>
    some ([command, moduleLabel.span] ++ imports.flatMap fun item =>
      [item.exported.span, item.localName.span])
  | _ => none

example : loadSpans = some [⟨⟨6, 2, 1⟩, ⟨43, 2, 38⟩⟩, ⟨⟨11, 2, 6⟩, ⟨20, 2, 15⟩⟩,
    ⟨⟨22, 2, 17⟩, ⟨26, 2, 21⟩⟩, ⟨⟨22, 2, 17⟩, ⟨26, 2, 21⟩⟩,
    ⟨⟨34, 2, 29⟩, ⟨41, 2, 36⟩⟩, ⟨⟨28, 2, 23⟩, ⟨33, 2, 28⟩⟩] := by decide +kernel

end Silmaril.Languages.Starlark.Frontend.Module.Loader
