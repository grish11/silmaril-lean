module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance

open scoped Functions.Lowering.Quote
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Functions (Program)

private def callerBlock : LexicalBlock :=
  ⟨["data", "index", "child", "copy", "marker", "result", "after"], [], []⟩

private def readLocal (name : String) : Functions.Lowering.Expr := Leaf.readOperand (fileSlot name)

private def scalar (n : Int) : Functions.Lowering.Expr := .atom (.scalar (.int n))

private def boxed (n : Int) : Functions.Lowering.Expr := .list [scalar n]

private def childFormals : List PlainKeywordParameter :=
  [.required "key", .defaulted ⟨"stage", starlark%[[32]], boxed 32, []⟩,
   .defaulted ⟨"saved", starlark%[data], readLocal "data", [fileSlot "data"]⟩]

private theorem child_defaults : KeywordLexical callerBlock childFormals :=
  .cons (.list (.int 32)) (.cons (.read (by decide) (.owned (by decide)) (.owned (by decide))) .nil)

private def childBody : Body.Suite :=
  .assign "made" starlark%[[44]]
    (.assign "check" starlark%[required[saved[key]][index]] (.ret starlark%[extras]))

private def child : Site callerBlock childFormals (some "rest") (some "extras") where
  name := "child"
  target := by decide
  parameters := ⟨["required"], [("spare", starlark%[[31]])]⟩
  source := childBody.source
  binders := ["made", "check"]
  locals := ["made", "check"]
  collects := .seq (.assign _ _) (.seq (.assign _ _) (.ret _))
  localOrder := .keep (by decide) (.keep (by decide) .nil)
  body := ⟨.seq (.assignExpr (fileSlot "made") (boxed 44)) (.seq (.assignExpr (fileSlot "check") (.index
    (.index (readLocal "required") (.index (readLocal "saved") (readLocal "key"))) (readLocal "index")))
    (.returnExpr (readLocal "extras"))),
    [fileSlot "required", fileSlot "saved", fileSlot "key", fileSlot "index", fileSlot "extras"]⟩
  free := [⟨fileSlot "index", fileSlot "index"⟩]
  selects := .owned (.owned (by decide)) (.owned (.owned (by decide)) (.owned (.owned (by decide))
    (.enclosing (.enclosing (by decide) (by decide)) (.owned (.owned (by decide)) .nil))))
  defaults := [⟨"spare", starlark%[[31]], boxed 31, []⟩]
  lexical := .cons (.list (.int 31)) .nil

private theorem child_body (seed : Program) :
    Elaborates child.block empty child.source seed child.body seed [] :=
  .plain (.straight (.assign (by decide) (.list (.int 44)) (.assign (by decide)
    (.index
      (.index (.read (by decide) (.owned (by decide)) (.owned (by decide)))
        (.index (.read (by decide) (.owned (by decide)) (.owned (by decide)))
          (.read (by decide) (.owned (by decide)) (.owned (by decide)))))
      (.read (by decide) (.enclosing (by decide) (by decide)) (.enclosing (by decide) (by decide))))
    (.ret (.read (by decide) (.owned (by decide)) (.owned (by decide)))))))

private inductive Mode where
  | emptyPack | nonempty | missing | duplicate | operandError | bodyError

private def unmatched : Call.Named.Operands callerBlock :=
  ⟨[("zeta", starlark%[data]), ("extras", starlark%[data])],
    [("zeta", readLocal "data"), ("extras", readLocal "data")], [fileSlot "data", fileSlot "data"],
    .cons (.read (by decide) (.owned (by decide)) (.owned (by decide)))
      (.cons (.read (by decide) (.owned (by decide)) (.owned (by decide))) .nil), by decide⟩

private def named (mode : Mode) : Call.Named.Operands callerBlock :=
  match mode with
  | .emptyPack => ⟨[("key", starlark%[0])], [("key", scalar 0)], [], .cons (.int 0) .nil, by decide⟩
  | .nonempty =>
    ⟨[("zeta", starlark%[data]), ("key", starlark%[0]), ("extras", starlark%[data])],
      [("zeta", readLocal "data"), ("key", scalar 0), ("extras", readLocal "data")],
      [fileSlot "data", fileSlot "data"],
      .cons (.read (by decide) (.owned (by decide)) (.owned (by decide)))
        (.cons (.int 0) (.cons (.read (by decide) (.owned (by decide)) (.owned (by decide))) .nil)), by decide⟩
  | .missing => unmatched
  | .duplicate =>
    ⟨[("zeta", starlark%[[85]]), ("required", starlark%[[86]])],
      [("zeta", boxed 85), ("required", boxed 86)], [],
      .cons (.list (.int 85)) (.cons (.list (.int 86)) .nil), by decide⟩
  | .operandError =>
    ⟨[("zeta", starlark%[[85]]), ("key", starlark%[[0][1]]), ("extras", starlark%[[77]])],
      [("zeta", boxed 85), ("key", .index (boxed 0) (scalar 1)), ("extras", boxed 77)], [],
      .cons (.list (.int 85)) (.cons (.index (.list (.int 0)) (.int 1)) (.cons (.list (.int 77)) .nil)),
      by decide⟩
  | .bodyError =>
    ⟨[("key", starlark%[1]), ("zeta", starlark%[data]), ("extras", starlark%[data])],
      [("key", scalar 1), ("zeta", readLocal "data"), ("extras", readLocal "data")],
      [fileSlot "data", fileSlot "data"], .cons (.int 1)
        (.cons (.read (by decide) (.owned (by decide)) (.owned (by decide)))
          (.cons (.read (by decide) (.owned (by decide)) (.owned (by decide))) .nil)), by decide⟩

private def invocation (mode : Mode) : Invocation callerBlock where
  callee := "copy"
  calleeOwned := by decide
  calleeLegal := by decide
  destination := "result"
  destinationOwned := by decide
  arguments := starlark%[[[11]]] :: (match mode with
    | .emptyPack => []
    | _ => [starlark%[[74]], starlark%[73], starlark%[data]])
  codes := .list [boxed 11] :: (match mode with
    | .emptyPack => []
    | _ => [boxed 74, scalar 73, readLocal "data"])
  argumentReads := match mode with
    | .emptyPack => []
    | _ => [fileSlot "data"]
  operands := by
    apply Call.Arguments.cons (Body.Operand.list (Body.Operand.list (Body.Operand.int 11)))
    cases mode with
    | emptyPack => exact .nil
    | nonempty | missing | duplicate | operandError | bodyError =>
      exact .cons (.list (.int 74)) (.cons (.int 73)
        (.cons (.read (by decide) (.owned (by decide)) (.owned (by decide))) .nil))
  keywords := named mode

private def setup := [("copy", starlark%[child]), ("marker", starlark%[[17]])]

private def tail : Body.Suite := .assign "after" starlark%[[99]] (.ret starlark%[result])

private def tailCode : ResolvedBody :=
  ⟨.seq (.assignExpr (fileSlot "after") (boxed 99)) (.returnExpr (readLocal "result")), [fileSlot "result"]⟩

private def source (mode : Mode) : Statement :=
  .seq child.statement (Body.prependSource setup (.seq (invocation mode).source tail.source))

private def resolvedBody (mode : Mode) (id : Nat) : ResolvedBody :=
  ⟨.seq (.define (fileSlot "child") id)
      (Body.prependCode [("copy", readLocal "child"), ("marker", boxed 17)]
        (.seq (invocation mode).code tailCode.code)),
    child.reads ++ ([fileSlot "child"] ++ (invocation mode).reads ++ tailCode.reads)⟩

private theorem profile (mode : Mode) (seed : Program) :
    Elaborates callerBlock empty (source mode) seed (resolvedBody mode seed.size)
      (seed.push child.declaration) [(seed.size, child.declaration)] := by
  have ending : Body.Elaborates callerBlock tail tailCode.code tailCode.reads :=
    .assign (by decide) (.list (.int 99))
      (.ret (.read (by decide) (.owned (by decide)) (.owned (by decide))))
  have built := Elaborates.define (locals := empty) child child_defaults (child_body seed)
    (.assign (name := "copy") (by decide) (.read (by decide) (.owned child.target) (.owned child.target))
      (.copy child.target rfl)
      (.assign (name := "marker") (by decide) (.list (.int 17)) .forget
        (.invoke (invocation mode) ⟨seed.size, childFormals, some "rest", some "extras", child⟩ rfl
          (.plain (.straight ending)))))
  have name : child.name = "child" := rfl
  simpa [source, setup, resolvedBody, readLocal, boxed, scalar, fileSlot, Body.prependSource, Body.prependCode, name]
    using built

example (mode : Mode) (seed : Program) :
    compileBody ⟨callerBlock.context, .local⟩ (source mode) seed =
      .ok (resolvedBody mode seed.size, seed.push child.declaration) :=
  compiles (profile mode seed)

example (mode : Mode) (seed : Program) {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved)
    (table : PreservesDeclarations (seed.push child.declaration) resolved.program)
    {free : List Functions.FreeName} (selected : Selects callerBlock (resolvedBody mode seed.size).reads free)
    {state : Lists.State} {floor : Nat} (frame : Body.Frame callerBlock free floor state)
    (distinct : RootCall.DistinctOwned state) :
    let available := Functions.withoutDeclaration (List.range resolved.program.size) (seed.push child.declaration).size
    ∃ out, Runs callerBlock state (source mode) (resolvedBody mode seed.size).code out ∧
      Functions.Exec resolved.program available state (resolvedBody mode seed.size).code out ∧
      Functions.denoteBody resolved.program available (resolvedBody mode seed.size).code state = out := by
  have selection : Selects callerBlock ([] ++ (resolvedBody mode seed.size).reads ++ []) free := by simpa using selected
  obtain ⟨out, trace, _, _, exec, meaning⟩ :=
    runs (profile mode seed) checked table _ (entry_guard (profile mode seed) table) selection state frame distinct
  exact ⟨out, trace, exec, meaning⟩

private def commands (mode : Mode) : List Command :=
  [.assign "data" starlark%[[0,22]], .define "factory" (.required ["data", "index"]) (source mode),
   .assign "result" starlark%[factory(data, 0)], .assign "finished" starlark%[[91]]]

private def collectors (state : Lists.State) : List (Nat × Lists.Contents) :=
  (List.range state.heap.size).filterMap fun address => do
    let cell ← state.heap[address]?
    match cell.contents with
    | .tuple .. | .dict .. => some (address, cell.contents)
    | _ => none

private def dictionary (data : Nat) : Lists.Contents := .dict
  [⟨.string "zeta", [.string "zeta"], .list data⟩, ⟨.string "extras", [.string "extras"], .list data⟩]

#guard
  match resolve (commands .emptyPack), runModule (commands .emptyPack) (fun _ => none) {} with
  | .ok resolved, .ok (.ok published final) =>
    match resolved.program[0]?, published.exports.lookup "result", collectors final with
    | some declaration, some (.dict dict), [(tuple, first), (address, second)] =>
      declaration.signature.slots.map (·.name) == ["required", "spare", "key", "stage", "saved", "rest", "extras"] &&
      declaration.signature.kwargs == some (fileSlot "extras") &&
      dict == address && dict == tuple + 1 &&
      first == .tuple [] (some [.openTuple, .closeTuple]) && second == .dict []
    | _, _, _ => false
  | _, _ => false

#guard
  match runModule (commands .nonempty) (fun _ => none) {} with
  | .ok (.ok published final) =>
    match published.exports.lookup "result", published.exports.lookup "data", collectors final with
    | some (.dict address), some (.list data), [(tuple, first), (dict, second)] =>
      dict == address && dict == tuple + 1 &&
      first == .tuple [.scalar (.int 73), .list data] none && second == dictionary data
    | _, _, _ => false
  | _ => false

private def fails (mode : Mode) (expected : Lists.Error) (lists : List Int) (packed : Bool) : Bool :=
  let source := commands mode
  let caller : Lists.State := { iterators := [123] }
  match resolve source, runModule source (fun _ => none) caller with
  | .ok resolved, .ok (.error (.runtime reached) final) =>
    let entered := enter resolved.source caller
    let moduleCell name := (entered.slots (globalSlot name)).bind (fun slot => final.heap[slot.address]?)
    let keptLists := final.heap.toList.filterMap (fun cell => match cell.contents with
      | .list [.scalar (.int value)] => some value
      | _ => none)
    let packing := match moduleCell "data", collectors final with
      | _, [] => !packed
      | some ⟨.binding (some (.list address)), false⟩, [(tuple, first), (dict, second)] =>
        packed && dict == tuple + 1 && first == .tuple [.scalar (.int 73), .list address] none &&
        second == dictionary address && final.heap[dict]? == some ⟨second, false⟩
      | _, _ => false
    let skippedLocal := match moduleCell "factory" with
      | some ⟨.binding (some (.function address)), false⟩ =>
        final.heap[address + 6]? == some ⟨.binding none, false⟩ &&
        final.heap[address + 7]? == some ⟨.binding none, false⟩
      | _ => false
    reached == expected && keptLists == lists && packing && skippedLocal &&
    moduleCell "result" == some ⟨.binding none, false⟩ && moduleCell "finished" == some ⟨.binding none, false⟩ &&
    (final.slots (globalSlot "factory")).isNone && final.iterators == [123]
  | _, _ => false

#guard fails .missing (.missingArguments ["key"]) [31, 32, 17, 11, 74] false
#guard fails .duplicate (.multipleArgumentValues "required") [31, 32, 17, 11, 74, 85, 86] false
#guard fails .operandError (.indexRange 1 1) [31, 32, 17, 11, 74, 85, 0] false
#guard fails .bodyError (.indexRange 22 1) [31, 32, 17, 11, 74, 44] true

-- A keyword collector alone creates a distinct empty dictionary per call.
#guard
  let childDef := Statement.define "child" { kwargs := some "extras" } (.ret (some starlark%[extras]))
  let wrapper := Command.define "factory" (.required [])
    (.seq childDef (.seq (.assign "copy" starlark%[child])
      (.seq (.assign "first" starlark%[copy()]) (.seq (.assign "second" starlark%[copy()])
        (.ret (some starlark%[[first, second]]))))))
  let source := [wrapper, .assign "results" starlark%[factory()]]
  match runModule source (fun _ => none) {} with
  | .ok (.ok published final) =>
    match published.exports.lookup "results", collectors final with
    | some (.list results), [(a, .dict []), (b, .dict [])] =>
      (final.heap[results]?.map (·.contents)) == some (.list [.dict a, .dict b]) && a < b
    | _, _ => false
  | _ => false

#guard
  let childDef := Statement.define "child" { kwargs := some "extras" } (.ret (some starlark%[extras]))
  let wrapper := Command.define "factory" (.required [])
    (.seq childDef (.ret (some (.call (.scalar (.read "child")) []
      [("zeta", starlark%[[0][1]]), ("zeta", starlark%[[]])] none none))))
  match resolve [wrapper] with
  | .error (.validation (.syntax (.duplicateExplicitKeyword "zeta"))) => true
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance
