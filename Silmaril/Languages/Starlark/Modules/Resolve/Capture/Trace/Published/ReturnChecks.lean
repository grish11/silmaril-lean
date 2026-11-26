module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Thms
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs
meta import Silmaril.Languages.Starlark.Modules.Loader.Defs
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published

open scoped Functions.Lowering.Quote
open Defaults
open Defaults.Nested.Sequence.Recursive (Site)
open Defaults.Nested.Sequence.Recursive.Call.Named (Mapping)
open Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance (Entry)
open Functions (Program)

private def globals : List String := ["data", "factory", "escaped", "late", "alias", "result", "after"]
private def int (n : Int) : Functions.Lowering.Expr := .atom (.scalar (.int n))
private def boxed (n : Int) : Functions.Lowering.Expr := .list [int n]
private def localRead (name : String) : Functions.Lowering.Expr := Leaf.readOperand (fileSlot name)
private def globalRead (name : String) : Functions.Lowering.Expr := Leaf.readOperand (globalSlot name)

private def factoryBlock : Assignment.LexicalBlock := ⟨["value", "child", "copy"], [], globals⟩
private def childKeywords : List PlainKeywordParameter :=
  [.defaulted ⟨"key", starlark%[value], localRead "value", [fileSlot "value"]⟩]

private def childBody : Body.Suite :=
  .assign "marked" starlark%[[44]] (.assign "probe" starlark%[key[0]]
    (.assign "seen" starlark%[value[0]] (.ret starlark%[late])))

private def child : Site factoryBlock childKeywords (some "rest") (some "extras") where
  name := "child"
  target := by decide
  parameters := ⟨["first"], []⟩
  source := childBody.source
  binders := ["marked", "probe", "seen"]
  locals := ["marked", "probe", "seen"]
  collects := .seq (.assign _ _) (.seq (.assign _ _) (.seq (.assign _ _) (.ret _)))
  localOrder := .keep (by decide) (.keep (by decide) (.keep (by decide) .nil))
  body := ⟨.seq (.assignExpr (fileSlot "marked") (boxed 44))
    (.seq (.assignExpr (fileSlot "probe") (.index (localRead "key") (int 0)))
      (.seq (.assignExpr (fileSlot "seen") (.index (localRead "value") (int 0)))
        (.returnExpr (globalRead "late")))), [fileSlot "key", fileSlot "value", globalSlot "late"]⟩
  free := [⟨fileSlot "value", fileSlot "value"⟩, ⟨globalSlot "late", globalSlot "late"⟩]
  selects := .owned (.owned (by decide))
    (.enclosing (.enclosing (by decide) (by decide)) (.module (.module (by decide) (by decide) (by decide)) .nil))
  defaults := []
  lexical := .nil

private def returned : Entry factoryBlock := ⟨0, childKeywords, some "rest", some "extras", child⟩

private def factoryTail : Statement :=
  .seq (.assign "copy" starlark%[child])
    (.seq (.assign "value" starlark%[[52]]) (.ret (some starlark%[copy])))

private def factoryTailCode : ResolvedBody :=
  ⟨.seq (.assignExpr (fileSlot "copy") (localRead "child"))
    (.seq (.assignExpr (fileSlot "value") (boxed 52)) (.returnExpr (localRead "copy"))),
    [fileSlot "child", fileSlot "copy"]⟩

private def factory : Site (moduleLex globals) [] none none .global where
  name := "factory"
  target := by decide
  parameters := ⟨["value"], []⟩
  source := .seq child.statement factoryTail
  binders := ["child", "copy", "value"]
  locals := ["child", "copy"]
  collects := .seq (.define _ _ _) (.seq (.assign _ _) (.seq (.assign _ _) (.ret _)))
  localOrder := .keep (by decide) (.keep (by decide) (.skip (by decide) .nil))
  body := ⟨.seq (.define (fileSlot "child") 0) factoryTailCode.code, child.reads ++ factoryTailCode.reads⟩
  free := [⟨globalSlot "late", globalSlot "late"⟩]
  selects := .owned (.owned (by decide)) (.module (.module (by decide) (by decide) (by decide))
    (.owned (.owned (by decide)) (.owned (.owned (by decide)) .nil)))
  defaults := []
  lexical := .nil

private def root : Root globals where
  keywords := []
  varargs := none
  kwargs := none
  site := factory
  lexical := .nil
  seed := #[]
  bodyTable := #[child.declaration]
  children := [(0, child.declaration)]
  returned := some returned
  suite := by
    refine .define (rest := factoryTail) (tail := factoryTailCode)
      (childTable := #[]) (descendants := []) (later := []) child (.cons (.read (by decide) (.owned (by decide)) (.owned (by decide))) .nil) ?_ ?_
    · refine .plain (.straight (source := childBody) ?_)
      refine .assign (by decide) (.list (.int 44)) ?_
      refine .assign (by decide) (.index (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.int 0)) ?_
      refine .assign (by decide) (.index (.read (by decide) (.enclosing (by decide) (by decide))
        (.enclosing (by decide) (by decide))) (.int 0)) ?_
      exact .ret (.read (by decide) (.global (by decide) (by decide) (by decide))
        (.module (by decide) (by decide) (by decide)))
    · exact .assign (by decide) (.read (by decide) (.owned (by decide)) (.owned (by decide)))
        (.copy (name := "child") (by decide) rfl)
        (.assign (by decide) (.list (.int 52)) .forget (.returnLocal (by decide) (by decide) rfl))

private theorem fromGlobal {name : String} (member : name ∈ globals)
    (legal : name.toList.head? ≠ some '$') :
    Body.Operand (moduleLex globals) (.scalar (.read name)) (globalRead name) [globalSlot name] :=
  .read legal (.global (by simp [moduleLex]) (by simp [moduleLex]) member)
    (.module (by simp [moduleLex]) (by simp [moduleLex]) member)

private def make : Invocation globals where
  callee := "factory"
  calleeGlobal := by decide
  legal := by decide
  destination := "escaped"
  destinationGlobal := by decide
  arguments := [starlark%[data]]
  codes := [globalRead "data"]
  reads := [globalSlot "data"]
  operands := .cons (fromGlobal (by decide) (by decide)) .nil
  keywords := .empty

private def mapping (bad : Bool) : Mapping (moduleLex globals) :=
  if bad then ⟨[(.string "key", starlark%[8])], [(.atom (.string "key"), int 8)], [],
    .entry (.string "key") (.plain (.int 8)) .empty⟩
  else ⟨[(.string "extra", starlark%[late])], [(.atom (.string "extra"), globalRead "late")], [globalSlot "late"],
    .entry (.string "extra") (.plain (fromGlobal (by decide) (by decide))) .empty⟩

private def invoke (bad : Bool) : Invocation globals where
  callee := "alias"
  calleeGlobal := by decide
  legal := by decide
  destination := "result"
  destinationGlobal := by decide
  arguments := []
  codes := []
  reads := []
  operands := .nil
  keywords := ⟨[("another", starlark%[[61]])], [("another", boxed 61)], [], .cons (.list (.int 61)) .nil, by decide⟩
  star := some (.list (.cons (fromGlobal (name := "data") (by decide) (by decide))
    (.cons (fromGlobal (name := "data") (by decide) (by decide)) .nil)))
  mapping := some (mapping bad)

private def commands (bad : Bool) : List Resolve.Command :=
  [.assign "data" starlark%[[31]], root.command, make.source, .assign "late" starlark%[[83]],
   .assign "alias" starlark%[escaped], (invoke bad).source, .assign "after" starlark%[[99]]]

private def code (bad : Bool) : List Modules.Command :=
  [.exec (.assignExpr "data" (boxed 31)), .exec (.define "factory" 1), .exec (.assignExpr "escaped" make.code),
   .exec (.assignExpr "late" (boxed 83)), .exec (.assignExpr "alias" (globalRead "escaped")),
   .exec (.assignExpr "result" (invoke bad).code), .exec (.assignExpr "after" (boxed 99))]

private def exports : Environment :=
  update (update (update (update (update (update (update (fun _ => none) "data" none)
    "factory" (some root.callable)) "escaped" (some (.nested returned))) "late" none)
    "alias" (some (.nested returned))) "result" none) "after" none

private theorem plan (bad : Bool) : Plan globals (fun _ => none) (commands bad) #[] (code bad) root.table exports := by
  refine .assign (by decide) (.list (.int 31)) .forget (.define root ?_)
  refine .invoke make root.callable rfl (.assign (by decide) (.list (.int 83)) .forget ?_)
  refine .assign (by decide) (fromGlobal (by decide) (by decide)) (.copy (name := "escaped") rfl) ?_
  exact .invoke (invoke bad) (.nested returned) rfl (.assign (by decide) (.list (.int 99)) .forget .done)

example (bad : Bool) {resolved : ResolvedModule} (checked : resolve (commands bad) = .ok resolved)
    (caller : Lists.State) :
    ∃ reached, ExecutesAll globals (enter resolved.source caller) (commands bad) reached ∧
      runModule (commands bad) (fun _ => none) caller = .ok (finish resolved.source caller reached) ∧
      ∀ published final, finish resolved.source caller reached = .ok published final →
        PublishedLive exports resolved.program published final := by
  have checkedPlan : Plan (Trace.names (commands bad)) (fun _ => none) (commands bad) #[] (code bad) root.table exports := plan bad
  obtain ⟨out, source, _, _, exactResult, published⟩ := module_agrees checkedPlan checked (fun _ => none) caller
  exact ⟨out, source, exactResult, published⟩

#guard
  match runModule (commands false) (fun _ => none) {} with
  | .ok (.ok published final) =>
    match published.exports.lookup "escaped", published.exports.lookup "alias", published.exports.lookup "data",
      published.exports.lookup "late", published.exports.lookup "result" with
    | some (.function escaped), some (.function alias), some (.list data), some (.list late), some (.list result) =>
      match final.heap[escaped]? with
      | some ⟨.function closure, true⟩ =>
        escaped == alias && late == result && closure.declaration == 0 &&
        closure.defaults == [(fileSlot "key", .list data)] &&
        final.heap[data]? == some ⟨.list [.scalar (.int 31)], true⟩ &&
        final.heap[late]? == some ⟨.list [.scalar (.int 83)], true⟩ &&
        (match closure.captures with
        | [value, global] =>
          (match final.heap[value.address]? with
          | some ⟨.binding (some (.list rebound)), true⟩ =>
            final.heap[rebound]? == some ⟨.list [.scalar (.int 52)], true⟩
          | _ => false) && final.heap[global.address]? == some ⟨.binding (some (.list late)), false⟩
        | _ => false)
      | _ => false
    | _, _, _, _, _ => false
  | _ => false

#guard
  let caller : Lists.State := { iterators := [123] }
  match runModule (commands true) (fun _ => none) caller, resolve (commands true) with
  | .ok (.error (.runtime .indexTarget) final), .ok resolved =>
    let entered := enter resolved.source caller
    let cell name := (entered.slots (globalSlot name)).bind (fun slot => final.heap[slot.address]?)
    let lists := final.heap.toList.filterMap fun cell => match cell.contents with
      | .list [.scalar (.int value)] => some (value, cell.frozen)
      | _ => none
    let tuples := final.heap.toList.countP fun cell => match cell.contents with | .tuple .. => true | _ => false
    let dicts := final.heap.toList.countP fun cell => match cell.contents with | .dict .. => true | _ => false
    lists == [(31, false), (52, false), (83, false), (61, false), (44, false)] && tuples == 1 && dicts == 2 &&
    cell "escaped" == cell "alias" && cell "result" == some ⟨.binding none, false⟩ &&
    cell "after" == some ⟨.binding none, false⟩ && (final.slots (globalSlot "alias")).isNone &&
    final.iterators == [123]
  | _, _ => false

open Imports

private inductive ImportCase where
  | ok | bodyError | missing

private def importName : ImportCase → String
  | .ok | .bodyError => "factory"
  | .missing => "absent"

private def importerGlobals : List String := ["starter", "made", "held", "marker", "result", "late"]

private def importsMapping (test : ImportCase) : Mapping (block "loaded" importerGlobals) :=
  match test with
  | .bodyError =>
    ⟨[(.string "key", starlark%[8])], [(.atom (.string "key"), int 8)], [],
      .entry (.string "key") (.plain (.int 8)) .empty⟩
  | .ok | .missing =>
    ⟨[(.string "extra", starlark%[9])], [(.atom (.string "extra"), int 9)], [],
      .entry (.string "extra") (.plain (.int 9)) .empty⟩

private def factoryCall : Imports.Invocation "loaded" importerGlobals where
  callee := "starter"
  declared := .inr (by decide)
  legal := by decide
  destination := "made"
  destinationGlobal := by decide
  arguments := [starlark%[[41]]]
  codes := [boxed 41]
  reads := []
  operands := .cons (.list (.int 41)) .nil
  keywords := .empty

private def childCall (test : ImportCase) : Imports.Invocation "loaded" importerGlobals where
  callee := "held"
  declared := .inr (by decide)
  legal := by decide
  destination := "result"
  destinationGlobal := by decide
  arguments := []
  codes := []
  reads := []
  operands := .nil
  keywords := ⟨[("another", starlark%[[71]])], [("another", boxed 71)], [],
    .cons (.list (.int 71)) .nil, by decide⟩
  star := some (.list (.cons (.int 17) (.cons (.int 18) .nil)))
  mapping := some (importsMapping test)

private def consumer (test : ImportCase) : Consumer where
  label := "prodé.star"
  name := importName test
  alias := "loaded"
  publicName := by cases test <;> simp [importName, Modules.isPublic, String.startsWith_string_eq_false_iff]
  globals := importerGlobals
  body :=
    [.assign "starter" (by decide)
        (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.name "loaded"),
      .invoke factoryCall,
      .assign "held" (by decide)
        (.read (by decide) (.global (by decide) (by decide) (by decide))
          (.module (by decide) (by decide) (by decide))) (.name "made"),
      .assign "marker" (by decide) (.list (.int 88)) .forget,
      .invoke (childCall test),
      .assign "late" (by decide) (.list (.int 199)) .forget]
  declared := rfl
  separate := by decide

private theorem covered (test : ImportCase) : Covered exports (commands false) (consumer test) := by
  have ready : ReadyFor (initial "loaded" root.callable) (consumer test).body := by
    exact ⟨root.callable, rfl, ⟨.nested returned, rfl, trivial⟩⟩
  cases test
  · exact .inl ⟨root.callable, rfl, ready⟩
  · exact .inl ⟨root.callable, rfl, ready⟩
  · exact .inr (by decide)

example (test : ImportCase) {producer importer : ResolvedModule}
    (prod : resolve (commands false) #[] = .ok producer)
    (imp : resolve (consumer test).commands producer.program = .ok importer)
    (caller : Lists.State) :
    Agrees (commands false) producer importer (consumer test) exports ⟨caller, []⟩ :=
  cold_agrees (commands := commands false) (plan false) prod (consumer test) imp (covered test) caller

example (test : ImportCase) {producer importer : ResolvedModule}
    (prod : resolve (commands false) #[] = .ok producer)
    (imp : resolve (consumer test).commands producer.program = .ok importer)
    (caller : Lists.State) :
    ∃ preload, Producer (commands false) producer.source ⟨caller, []⟩ preload ∧
      Loader.load producer.program (graph producer importer (consumer test)) 0 ⟨caller, []⟩ = preload ∧
      ∀ published reached, preload = .ok published reached →
        reached.cache = [(0, published)] ∧ Agrees (commands false) producer importer (consumer test) exports reached :=
  preloaded_agrees (commands := commands false) (plan false) prod (consumer test) imp (covered test) caller

private def runImport (test : ImportCase) (warm : Bool) : Option (Loader.Result Modules.Published) := do
  let producer ← (resolve (commands false)).toOption
  let importer ← (resolve (consumer test).commands producer.program).toOption
  let manifest := graph producer importer (consumer test)
  let caller : Loader.Session := { runtime := {iterators := [123]} }
  if warm then
    match Loader.load producer.program manifest 0 caller with
    | .ok _ state => some (Loader.load producer.program manifest 1 state)
    | .error .. => none
  else
    some (Loader.load producer.program manifest 1 caller)

private def imported (warm : Bool) : Bool :=
  match runImport .ok warm with
  | some (.ok published final) =>
    match final.cache.lookup 0, published.exports.lookup "result", published.exports.lookup "late",
      published.exports.lookup "made", published.exports.lookup "held" with
    | some producer, some (.list result), some (.list consumerLate), some (.function made), some (.function held) =>
      match producer.exports.lookup "factory", producer.exports.lookup "escaped", producer.exports.lookup "late" with
      | some (.function factory), some (.function escaped), some (.list producerLate) =>
        match final.runtime.heap[made]?, final.runtime.heap[escaped]? with
        | some ⟨.function closure, true⟩, some ⟨.function prior, true⟩ =>
          let lists := final.runtime.heap.toList.filterMap (fun cell => match cell.contents with
            | .list [.scalar (.int n)] => some n
            | _ => none)
          final.cache.map Prod.fst == [1, 0] && made == held && made != escaped &&
          published.exports.lookup "starter" == some (.function factory) &&
          published.exports.lookup "loaded" == none && result == producerLate && result != consumerLate &&
          final.runtime.heap[result]? == some ⟨.list [.scalar (.int 83)], true⟩ &&
          final.runtime.heap[consumerLate]? == some ⟨.list [.scalar (.int 199)], true⟩ &&
          (match closure.defaults with
           | [(name, .list saved)] =>
             name == fileSlot "key" && final.runtime.heap[saved]? == some ⟨.list [.scalar (.int 41)], true⟩
           | _ => false) &&
          (match closure.captures, prior.captures with
           | [localCapture, globalCapture], [oldLocal, oldGlobal] =>
             localCapture.address != oldLocal.address && globalCapture.address == oldGlobal.address &&
             (match final.runtime.heap[localCapture.address]? with
             | some ⟨.binding (some (.list rebound)), true⟩ =>
               final.runtime.heap[rebound]? == some ⟨.list [.scalar (.int 52)], true⟩
             | _ => false) &&
             final.runtime.heap[globalCapture.address]? == some ⟨.binding (some (.list producerLate)), false⟩
           | _, _ => false) &&
          lists.count 31 == 1 && lists.count 44 == 2 && final.runtime.iterators == [123] &&
          (final.runtime.slots (fileSlot "loaded")).isNone
        | _, _ => false
      | _, _, _ => false
    | _, _, _, _, _ => false
  | _ => false

#guard imported false
#guard imported true

private def failedImport (test : ImportCase) (warm : Bool) (expected : Modules.Error) (retained : List Int) : Bool :=
  match runImport test warm with
  | some (.error (.initialization 1 error) final) =>
    let lists := final.runtime.heap.toList.filterMap fun cell => match cell.contents, cell.frozen with
      | .list [.scalar (.int n)], false => some n
      | _, _ => none
    error == expected && final.cache.map Prod.fst == [0] && lists == retained &&
      (final.runtime.slots (fileSlot "loaded")).isNone && final.runtime.iterators == [123]
  | _ => false

-- The producer's unreachable operand/body allocations remain in both heaps.
-- The missing import skips the full suite. The second-call error retains
-- the factory's saved value, rebinding and earlier importer assignment.
#guard failedImport .missing false (.missingExport "prodé.star" "absent") [61, 44]
#guard failedImport .missing true (.missingExport "prodé.star" "absent") [61, 44]
#guard failedImport .bodyError false (.runtime .indexTarget) [61, 44, 41, 52, 88, 71, 44]
#guard failedImport .bodyError true (.runtime .indexTarget) [61, 44, 41, 52, 88, 71, 44]


end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
