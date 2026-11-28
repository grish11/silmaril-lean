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
  .assign "check" starlark%[required[saved[key]][index]] (.ret starlark%[rest])

private def child : Site callerBlock childFormals (some "rest") where
  name := "child"
  target := by decide
  parameters := ⟨["required"], [("spare", starlark%[[31]])]⟩
  source := childBody.source
  binders := ["check"]
  locals := ["check"]
  collects := .seq (.assign _ _) (.ret _)
  localOrder := .keep (by decide) .nil
  body := ⟨.seq (.assignExpr (fileSlot "check") (.index
    (.index (readLocal "required") (.index (readLocal "saved") (readLocal "key"))) (readLocal "index")))
    (.returnExpr (readLocal "rest")),
    [fileSlot "required", fileSlot "saved", fileSlot "key", fileSlot "index", fileSlot "rest"]⟩
  free := [⟨fileSlot "index", fileSlot "index"⟩]
  selects := .owned (.owned (by decide)) (.owned (.owned (by decide)) (.owned (.owned (by decide))
    (.enclosing (.enclosing (by decide) (by decide)) (.owned (.owned (by decide)) .nil))))
  defaults := [⟨"spare", starlark%[[31]], boxed 31, []⟩]
  lexical := .cons (.list (.int 31)) .nil

private theorem child_body (seed : Program) :
    Elaborates child.block empty child.source seed child.body seed [] :=
  .plain (.straight (.assign (by decide)
    (.index
      (.index (.read (by decide) (.owned (by decide)) (.owned (by decide)))
        (.index (.read (by decide) (.owned (by decide)) (.owned (by decide)))
          (.read (by decide) (.owned (by decide)) (.owned (by decide)))))
      (.read (by decide) (.enclosing (by decide) (by decide)) (.enclosing (by decide) (by decide))))
    (.ret (.read (by decide) (.owned (by decide)) (.owned (by decide))))))

private inductive Mode where
  | emptyPack | nonempty | missing | operandError | bodyError

private def named (mode : Mode) : Call.Named.Operands callerBlock :=
  match mode with
  | .emptyPack | .nonempty => ⟨[("key", starlark%[0])], [("key", scalar 0)], [], .cons (.int 0) .nil, by decide⟩
  | .missing => .empty
  | .operandError =>
    ⟨[("key", starlark%[[0][1]]), ("saved", starlark%[[77]])],
     [("key", .index (boxed 0) (scalar 1)), ("saved", boxed 77)], [],
     .cons (.index (.list (.int 0)) (.int 1)) (.cons (.list (.int 77)) .nil), by decide⟩
  | .bodyError => ⟨[("key", starlark%[1])], [("key", scalar 1)], [], .cons (.int 1) .nil, by decide⟩

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
    | nonempty | missing | operandError | bodyError =>
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
        (.invoke (invocation mode) ⟨seed.size, childFormals, some "rest", none, child⟩ rfl
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

private def tuples (state : Lists.State) : List Lists.Contents :=
  state.heap.toList.filterMap fun cell => match cell.contents with
    | .tuple values key => some (.tuple values key)
    | _ => none

#guard
  match runModule (commands .emptyPack) (fun _ => none) {} with
  | .ok (.ok published final) =>
    match published.exports.lookup "result" with
    | some (.tuple address) =>
      (final.heap[address]?.map (·.contents)) == some (.tuple [] (some [.openTuple, .closeTuple])) &&
      tuples final == [.tuple [] (some [.openTuple, .closeTuple])]
    | _ => false
  | _ => false

#guard
  match runModule (commands .nonempty) (fun _ => none) {} with
  | .ok (.ok published final) =>
    match published.exports.lookup "result", published.exports.lookup "data" with
    | some (.tuple address), some (.list data) =>
      (final.heap[address]?.map (·.contents)) == some (.tuple [.scalar (.int 73), .list data] none) &&
      tuples final == [.tuple [.scalar (.int 73), .list data] none]
    | _, _ => false
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
    let packing := match moduleCell "data" with
      | some ⟨.binding (some (.list address)), false⟩ =>
        tuples final == if packed then [.tuple [.scalar (.int 73), .list address] none] else []
      | _ => false
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
#guard fails .operandError (.indexRange 1 1) [31, 32, 17, 11, 74, 0] false
#guard fails .bodyError (.indexRange 22 1) [31, 32, 17, 11, 74] true

-- A named collector also permits a required-only keyword suffix.
-- The child in this control has no lexical captures.
#guard
  let childDef := Statement.define "child"
    { varargs := some "rest", keywordOnly := [⟨"key", none⟩] } (.ret (some starlark%[rest]))
  let wrapper := Command.define "factory" (.required [])
    (.seq childDef (.seq (.assign "copy" starlark%[child])
      (.seq (.assign "result" starlark%[copy(4, 5, key=0)]) (.ret (some starlark%[result])))))
  let source := [wrapper, .assign "result" starlark%[factory()]]
  match resolve source, runModule source (fun _ => none) {} with
  | .ok resolved, .ok (.ok published final) =>
    match resolved.program[0]?, published.exports.lookup "result" with
    | some declaration, some (.tuple address) =>
      declaration.free.isEmpty &&
      (match final.heap[address]? with
      | some ⟨.tuple [.scalar (.int 4), .scalar (.int 5)] _, _⟩ => true
      | _ => false)
    | _, _ => false
  | _, _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance
