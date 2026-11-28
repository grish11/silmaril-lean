module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance

open scoped Functions.Lowering.Quote
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Functions (Program)

private def caller : LexicalBlock := ⟨["data", "child", "copy", "result", "after"], [], []⟩

private def readLocal (name : String) : Functions.Lowering.Expr := Leaf.readOperand (fileSlot name)

private def int (n : Int) : Functions.Lowering.Expr := .atom (.scalar (.int n))

private def boxed (n : Int) : Functions.Lowering.Expr := .list [int n]

private def formals : List PlainKeywordParameter := [.required "key"]

private def child : Site caller formals (some "rest") where
  name := "child"
  target := by decide
  parameters := ⟨["first"], [("second", starlark%[[41]])]⟩
  source := .seq (.assign "marked" starlark%[[44]]) (.ret (some starlark%[rest]))
  binders := ["marked"]
  locals := ["marked"]
  collects := .seq (.assign _ _) (.ret _)
  localOrder := .keep (by decide) .nil
  body := ⟨.seq (.assignExpr (fileSlot "marked") (boxed 44)) (.returnExpr (readLocal "rest")), [fileSlot "rest"]⟩
  free := []
  selects := .owned (.owned (by decide)) .nil
  defaults := [⟨"second", starlark%[[41]], boxed 41, []⟩]
  lexical := .cons (.list (.int 41)) .nil

private theorem child_body (seed : Program) :
    Elaborates child.block empty child.source seed child.body seed [] :=
  .plain (.straight (.assign (by decide) (.list (.int 44))
    (.ret (.read (by decide) (.owned (by decide)) (.owned (by decide))))))

private inductive Mode where
  | emptyTuple | tuple | list | invalid | namedError | elementError | conflict

private theorem aliased : Call.Arguments caller [starlark%[data], starlark%[73], starlark%[data]]
    [readLocal "data", int 73, readLocal "data"] [fileSlot "data", fileSlot "data"] :=
  .cons (.read (by decide) (.owned (by decide)) (.owned (by decide)))
    (.cons (.int 73) (.cons (.read (by decide) (.owned (by decide)) (.owned (by decide))) .nil))

private def spread (mode : Mode) : Call.Named.Spread caller :=
  match mode with
  | .emptyTuple => .tuple .nil
  | .tuple => .tuple aliased
  | .list | .conflict => .list aliased
  | .invalid => .integer 7
  | .namedError => .list (.cons (.list (.int 88)) .nil)
  | .elementError => .list (.cons (.list (.int 53))
      (.cons (.index (.list (.int 0)) (.int 1)) (.cons (.list (.int 77)) .nil)))

private def keyword (mode : Mode) : Call.Named.Operands caller :=
  match mode with
  | .namedError =>
    ⟨[("key", starlark%[[0][1]])], [("key", .index (boxed 0) (int 1))], [],
      .cons (.index (.list (.int 0)) (.int 1)) .nil, by decide⟩
  | .invalid | .conflict =>
    ⟨[("first", starlark%[[31]])], [("first", boxed 31)], [], .cons (.list (.int 31)) .nil, by decide⟩
  | _ => ⟨[("key", starlark%[[31]])], [("key", boxed 31)], [], .cons (.list (.int 31)) .nil, by decide⟩

private def invocation (mode : Mode) : Invocation caller where
  callee := "copy"
  calleeOwned := by decide
  calleeLegal := by decide
  destination := "result"
  destinationOwned := by decide
  arguments := [starlark%[[17]]]
  codes := [boxed 17]
  argumentReads := []
  operands := .cons (.list (.int 17)) .nil
  keywords := keyword mode
  star := some (spread mode)

private def tail : Body.Suite := .assign "after" starlark%[[99]] (.ret starlark%[result])

private def tailCode : ResolvedBody :=
  ⟨.seq (.assignExpr (fileSlot "after") (boxed 99)) (.returnExpr (readLocal "result")), [fileSlot "result"]⟩

private def source (mode : Mode) : Statement :=
  .seq child.statement (.seq (.assign "copy" starlark%[child]) (.seq (invocation mode).source tail.source))

private def resolvedBody (mode : Mode) (id : Nat) : ResolvedBody :=
  ⟨.seq (.define (fileSlot "child") id) (.seq (.assignExpr (fileSlot "copy") (readLocal "child"))
      (.seq (invocation mode).code tailCode.code)),
    child.reads ++ ([fileSlot "child"] ++ (invocation mode).reads ++ tailCode.reads)⟩

private theorem profile (mode : Mode) (seed : Program) :
    Elaborates caller empty (source mode) seed (resolvedBody mode seed.size)
      (seed.push child.declaration) [(seed.size, child.declaration)] := by
  have ending : Body.Elaborates caller tail tailCode.code tailCode.reads :=
    .assign (by decide) (.list (.int 99))
      (.ret (.read (by decide) (.owned (by decide)) (.owned (by decide))))
  exact .define child .nil (child_body seed)
    (.assign (name := "copy") (by decide) (.read (by decide) (.owned child.target) (.owned child.target))
      (.copy child.target rfl)
      (.invoke (invocation mode) ⟨seed.size, formals, some "rest", none, child⟩ rfl
        (.plain (.straight ending))))

example (mode : Mode) (seed : Program) :
    compileBody ⟨caller.context, .local⟩ (source mode) seed =
      .ok (resolvedBody mode seed.size, seed.push child.declaration) :=
  compiles (profile mode seed)

example (mode : Mode) (seed : Program) {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved)
    (table : PreservesDeclarations (seed.push child.declaration) resolved.program)
    {free : List Functions.FreeName} (selected : Selects caller (resolvedBody mode seed.size).reads free)
    {state : Lists.State} {floor : Nat} (frame : Body.Frame caller free floor state)
    (distinct : RootCall.DistinctOwned state) :
    let available := Functions.withoutDeclaration (List.range resolved.program.size) (seed.push child.declaration).size
    ∃ out, Runs caller state (source mode) (resolvedBody mode seed.size).code out ∧
      Functions.Exec resolved.program available state (resolvedBody mode seed.size).code out ∧
      Functions.denoteBody resolved.program available (resolvedBody mode seed.size).code state = out := by
  have selection : Selects caller ([] ++ (resolvedBody mode seed.size).reads ++ []) free := by simpa using selected
  obtain ⟨out, trace, _, _, exec, meaning⟩ :=
    runs (profile mode seed) checked table _ (entry_guard (profile mode seed) table) selection state frame distinct
  exact ⟨out, trace, exec, meaning⟩

private def commands (mode : Mode) : List Command :=
  [.assign "data" starlark%[[0,22]], .define "factory" (.required ["data"]) (source mode),
   .assign "result" starlark%[factory(data)], .assign "finished" starlark%[[91]]]

private def contents (state : Lists.State) (address : Nat) : Option Lists.Contents :=
  state.heap[address]?.map (·.contents)

private def listSlot (state : Lists.State) (slot : Nat) (value : Int) : Bool :=
  match contents state slot with
  | some (.binding (some (.list address))) => contents state address == some (.list [.scalar (.int value)])
  | _ => false

private def success (mode : Mode) : Bool :=
  match runModule (commands mode) (fun _ => none) {} with
  | .ok (.ok published final) =>
    match published.exports.lookup "result", published.exports.lookup "data" with
    | some (.tuple address), some (.list data) =>
      let retained := contents final address
      let carrier := contents final (address - 1)
      let firstAndNamed := listSlot final (address + 1) 17 && listSlot final (address + 3) 31
      firstAndNamed && (match mode with
      | .emptyTuple =>
        let empty := some (Lists.Contents.tuple [] (some [.openTuple, .closeTuple]))
        retained == empty && carrier == empty && listSlot final (address + 2) 41
      | .tuple | .list =>
        let values : List Lists.Value := [.list data, .scalar (.int 73), .list data]
        retained == some (.tuple values.tail none) &&
        contents final (address + 2) == some (.binding (some (.list data))) &&
        (match mode with
        | .tuple => carrier == some (.tuple values none)
        | _ => carrier == some (.list values))
      | _ => false)
    | _, _ => false
  | _ => false

#guard success .emptyTuple && success .tuple && success .list

private def fails (mode : Mode) (expected : Lists.Error) (lists : List Int) (carrier : Bool) : Bool :=
  let source := commands mode
  let initial : Lists.State := { iterators := [123] }
  match resolve source, runModule source (fun _ => none) initial with
  | .ok resolved, .ok (.error (.runtime reached) final) =>
    let entered := enter resolved.source initial
    let moduleCell name := (entered.slots (globalSlot name)).bind (fun slot => final.heap[slot.address]?)
    let numbers := final.heap.toList.filterMap fun cell => match cell.contents with
      | .list [.scalar (.int value)] => some value
      | _ => none
    let display := match moduleCell "data" with
      | some ⟨.binding (some (.list data)), false⟩ =>
        final.heap.toList.any (fun cell => cell.contents == .list [.list data, .scalar (.int 73), .list data])
      | _ => false
    let noPack := final.heap.toList.all fun cell => match cell.contents with
      | .tuple .. => false
      | _ => true
    let skipped := match moduleCell "factory" with
      | some ⟨.binding (some (.function address)), false⟩ =>
        contents final (address + 4) == some (.binding none) && contents final (address + 5) == some (.binding none)
      | _ => false
    reached == expected && numbers == lists && display == carrier && noPack && skipped &&
      moduleCell "result" == some ⟨.binding none, false⟩ && moduleCell "finished" == some ⟨.binding none, false⟩ &&
      (final.slots (globalSlot "factory")).isNone && final.iterators == [123]
  | _, _ => false

#guard fails .invalid .invalidStar [41, 17, 31] false
#guard fails .namedError (.indexRange 1 1) [41, 17, 0] false
#guard fails .elementError (.indexRange 1 1) [41, 17, 31, 53, 0] false
#guard fails .conflict (.multipleArgumentValues "first") [41, 17, 31] true

-- Both display forms feed an ordinary parameter and omit or replace a saved value.
#guard
  let childDef := Statement.define "child" { positional := [⟨"x", none⟩, ⟨"y", some starlark%[[41]]⟩] }
    (.ret (some starlark%[y]))
  let wrapper := Command.define "factory" (.required ["data"])
    (.seq childDef (.seq (.assign "copy" starlark%[child])
      (.seq (.assign "first" starlark%[copy(*[data])])
        (.seq (.assign "second" starlark%[copy(*(data, data))]) (.ret (some starlark%[[first, second]]))))))
  let source := [.assign "data" starlark%[[0,22]], wrapper, .assign "result" starlark%[factory(data)]]
  match runModule source (fun _ => none) {} with
  | .ok (.ok published final) =>
    match published.exports.lookup "result", published.exports.lookup "data" with
    | some (.list result), some (.list data) =>
      match contents final result with
      | some (.list [.list saved, .list supplied]) =>
        contents final saved == some (.list [.scalar (.int 41)]) && supplied == data
      | _ => false
    | _, _ => false
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance
