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

private def formals : List PlainKeywordParameter :=
  [.defaulted ⟨"key", starlark%[[31]], boxed 31, []⟩]

private def child : Site caller formals (some "rest") (some "extras") where
  name := "child"
  target := by decide
  parameters := ⟨["first"], []⟩
  source := .seq (.assign "marked" starlark%[[44]])
    (.seq (.assign "probe" starlark%[key[0]]) (.ret (some starlark%[extras])))
  binders := ["marked", "probe"]
  locals := ["marked", "probe"]
  collects := .seq (.assign _ _) (.seq (.assign _ _) (.ret _))
  localOrder := .keep (by decide) (.keep (by decide) .nil)
  body := ⟨.seq (.assignExpr (fileSlot "marked") (boxed 44))
    (.seq (.assignExpr (fileSlot "probe") (.index (readLocal "key") (int 0))) (.returnExpr (readLocal "extras"))),
    [fileSlot "key", fileSlot "extras"]⟩
  free := []
  selects := .owned (.owned (by decide)) (.owned (.owned (by decide)) .nil)
  defaults := []
  lexical := .nil

private theorem child_body (seed : Program) :
    Elaborates child.block empty child.source seed child.body seed [] :=
  .plain (.straight (.assign (by decide) (.list (.int 44))
    (.assign (by decide) (.index (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.int 0))
      (.ret (.read (by decide) (.owned (by decide)) (.owned (by decide)))))))

private structure Term where
  source : Functions.Lowering.Resolve.SourceExpr
  code : Functions.Lowering.Expr
  reads : List Binding
  related : Call.Named.DisplayOperand caller source code reads

private def text (key : String) : Term := ⟨.string key, .atom (.string key), [], .string key⟩

private def dataOperand : Term :=
  ⟨starlark%[data], readLocal "data", [fileSlot "data"],
    .plain (.read (by decide) (.owned (by decide)) (.owned (by decide)))⟩

private def number (n : Int) : Term := ⟨.scalar (.int n), int n, [], .plain (.int n)⟩

private def list (n : Int) : Term := ⟨.list [(.scalar (.int n))], boxed n, [], .plain (.list (.int n))⟩

private def broken : Term :=
  ⟨starlark%[[0][1]], .index (boxed 0) (int 1), [], .plain (.index (.list (.int 0)) (.int 1))⟩

private theorem entries_related (pairs : List (Term × Term)) :
    Call.Named.DisplayEntries caller
      (pairs.map fun (key, value) => (key.source, value.source))
      (pairs.map fun (key, value) => (key.code, value.code))
      (pairs.flatMap fun (key, value) => key.reads ++ value.reads) := by
  induction pairs with
  | nil => exact .empty
  | cons pair rest ih =>
    obtain ⟨key, value⟩ := pair
    exact .entry key.related value.related ih

private def display (pairs : List (Term × Term)) : Call.Named.Mapping caller :=
  ⟨_, _, _, entries_related pairs⟩

private inductive Mode where
  | emptyMap | ordered | duplicate | duplicateExtra | nonString | earlier | starError | later | badStar | displayDuplicate | bodyError

private def mapping (mode : Mode) : Call.Named.Mapping caller :=
  display (match mode with
    | .emptyMap => []
    | .ordered => [(text "zeta", dataOperand), (text "key", dataOperand), (text "alpha", dataOperand)]
    | .duplicate => [(text "key", dataOperand), (text "later", list 64)]
    | .duplicateExtra => [(text "beta", dataOperand), (text "later", list 64)]
    | .nonString => [(text "key", dataOperand), (number 3, list 63), (text "later", list 64)]
    | .earlier | .starError => [(text "unused", list 77)]
    | .later => [(number 3, list 63), (text "broken", broken), (text "unused", list 77)]
    | .badStar => [(text "key", dataOperand)]
    | .bodyError => [(text "key", number 8)]
    | .displayDuplicate => [(text "dup", list 63), (text "dup", list 64), (text "unused", list 77)])

private def spread (mode : Mode) : Call.Named.Spread caller :=
  match mode with
  | .nonString | .later | .badStar => .integer 7
  | .starError => .list (.cons (.index (.list (.int 0)) (.int 1)) .nil)
  | _ => .list (.cons (.read (name := "data") (by decide) (.owned (by decide)) (.owned (by decide))) .nil)

private def keyword (mode : Mode) : Call.Named.Operands caller :=
  match mode with
  | .earlier =>
    ⟨[("beta", broken.source)], [("beta", broken.code)], [],
      .cons (.index (.list (.int 0)) (.int 1)) .nil, by decide⟩
  | .duplicate | .nonString =>
    ⟨[("key", (list 61).source)], [("key", boxed 61)], [], .cons (.list (.int 61)) .nil, by decide⟩
  | _ => ⟨[("beta", (list 61).source)], [("beta", boxed 61)], [], .cons (.list (.int 61)) .nil, by decide⟩

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
  mapping := some (mapping mode)

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
  have defaults : KeywordLexical caller formals := .cons (.list (.int 31)) .nil
  exact .define child defaults (child_body seed)
    (.assign (name := "copy") (by decide) (.read (by decide) (.owned child.target) (.owned child.target))
      (.copy child.target rfl)
      (.invoke (invocation mode) ⟨seed.size, formals, some "rest", some "extras", child⟩ rfl
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

private def dicts (state : Lists.State) : List (List Lists.Entry) :=
  state.heap.toList.filterMap fun cell => match cell.contents with
    | .dict entries => some entries
    | _ => none

private def success (mode : Mode) : Bool :=
  match runModule (commands mode) (fun _ => none) {} with
  | .ok (.ok published final) =>
    match published.exports.lookup "result", published.exports.lookup "data", dicts final with
    | some (.dict packed), some (.list data), [carrier, actuals] =>
      match actuals with
      | ⟨.string "beta", _, .list beta⟩ :: rest =>
        contents final beta == some (.list [.scalar (.int 61)]) &&
        contents final packed == some (.dict actuals) &&
        contents final (packed - 1) == some (.tuple [.list data] none) &&
        (match mode with
        | .emptyMap =>
          carrier.isEmpty && rest.isEmpty &&
          (match contents final (packed + 2) with
          | some (.binding (some (.list saved))) => contents final saved == some (.list [.scalar (.int 31)])
          | _ => false)
        | .ordered =>
          carrier.map (·.key) == [.string "zeta", .string "key", .string "alpha"] &&
          carrier.all (fun entry => entry.value == .list data) &&
          rest.map (fun entry => (entry.key, entry.value)) == [(.string "zeta", .list data), (.string "alpha", .list data)] &&
          contents final (packed + 2) == some (.binding (some (.list data)))
        | _ => false)
      | _ => false
    | _, _, _ => false
  | _ => false

#guard success .emptyMap && success .ordered

private def fails (mode : Mode) (expected : Lists.Error) (lists : List Int)
    (keys : List (List Lists.Value)) : Bool :=
  let source := commands mode
  let initial : Lists.State := { iterators := [123] }
  match resolve source, runModule source (fun _ => none) initial with
  | .ok resolved, .ok (.error (.runtime reached) final) =>
    let entered := enter resolved.source initial
    let moduleCell name := (entered.slots (globalSlot name)).bind (fun slot => final.heap[slot.address]?)
    let numbers := final.heap.toList.filterMap fun cell => match cell.contents with
      | .list [.scalar (.int value)] => some value
      | _ => none
    let dictKeys := (dicts final).map (List.map (·.key))
    let displayPrefix := match mode, dicts final with
      | .displayDuplicate, [[entry]] =>
        match entry.value with
        | .list address => contents final address == some (.list [.scalar (.int 63)])
        | _ => false
      | .displayDuplicate, _ => false
      | _, _ => true
    let tuples := final.heap.toList.filterMap fun cell => match cell.contents with
      | .tuple values _ => some values
      | _ => none
    let packs := match mode, moduleCell "data" with
      | .bodyError, some ⟨.binding (some (.list data)), false⟩ => tuples == [[.list data]]
      | .bodyError, _ => false
      | _, _ => tuples.isEmpty
    let skipped := match moduleCell "factory" with
      | some ⟨.binding (some (.function address)), false⟩ =>
        contents final (address + 4) == some (.binding none) && contents final (address + 5) == some (.binding none)
      | _ => false
    reached == expected && numbers == lists && dictKeys == keys && displayPrefix && packs && skipped &&
      moduleCell "result" == some ⟨.binding none, false⟩ && moduleCell "finished" == some ⟨.binding none, false⟩ &&
      (final.slots (globalSlot "factory")).isNone && final.iterators == [123]
  | _, _ => false

#guard fails .duplicate (.multipleArgumentValues "key") [31, 17, 61, 64] [[.string "key", .string "later"]]
#guard fails .duplicateExtra (.multipleArgumentValues "beta") [31, 17, 61, 64] [[.string "beta", .string "later"]]
#guard fails .nonString (.keywordMustBeString (.scalar (.int 3))) [31, 17, 61, 63, 64]
  [[.string "key", .scalar (.int 3), .string "later"]]
#guard fails .earlier (.indexRange 1 1) [31, 17, 0] []
#guard fails .starError (.indexRange 1 1) [31, 17, 61, 0] []
#guard fails .later (.indexRange 1 1) [31, 17, 61, 63, 0] [[.scalar (.int 3)]]
#guard fails .badStar .invalidStar [31, 17, 61] [[.string "key"]]
#guard fails .displayDuplicate (.duplicateKey (.string "dup")) [31, 17, 61, 63, 64] [[.string "dup"]]
#guard fails .bodyError .indexTarget [31, 17, 61, 44] [[.string "key"], [.string "beta"]]

-- A mapping alone supplies a fixed positional-or-named slot and retains its alias.
#guard
  let childDef := Statement.define "child" (.required ["value"]) (.ret (some starlark%[value]))
  let wrapper := Command.define "factory" (.required ["data"])
    (.seq childDef (.seq (.assign "copy" starlark%[child]) (.ret (some starlark%[copy(**{"value": data})]))))
  let source := [.assign "data" starlark%[[0,22]], wrapper, .assign "result" starlark%[factory(data)]]
  match runModule source (fun _ => none) {} with
  | .ok (.ok published _) => published.exports.lookup "data" == published.exports.lookup "result"
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance
