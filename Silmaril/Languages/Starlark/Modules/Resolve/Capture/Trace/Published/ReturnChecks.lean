module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Thms
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.Defs
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

private theorem covered (test : ImportCase) (program : Program) : Covered exports (commands false) (consumer test) program := by
  have ready : ReadyFor root.callable program (initial "loaded" root.callable) (consumer test).body := by
    exact ⟨.regular root.callable, rfl, ⟨.regular (.nested returned), rfl, trivial⟩⟩
  cases test
  · exact .inl ⟨root.callable, rfl, ready⟩
  · exact .inl ⟨root.callable, rfl, ready⟩
  · exact .inr (by decide)

example (test : ImportCase) {producer importer : ResolvedModule}
    (prod : resolve (commands false) #[] = .ok producer)
    (imp : resolve (consumer test).commands producer.program = .ok importer)
    (caller : Lists.State) :
    Agrees (commands false) producer importer (consumer test) exports ⟨caller, []⟩ :=
  cold_agrees (commands := commands false) (plan false) prod (consumer test) imp (covered test producer.program) caller

example (test : ImportCase) {producer importer : ResolvedModule}
    (prod : resolve (commands false) #[] = .ok producer)
    (imp : resolve (consumer test).commands producer.program = .ok importer)
    (caller : Lists.State) :
    ∃ preload, Producer (commands false) producer.source ⟨caller, []⟩ preload ∧
      Loader.load importer.program (graph producer importer (consumer test)) 0 ⟨caller, []⟩ = preload ∧
      ∀ published reached, preload = .ok published reached →
        reached.cache = [(0, published)] ∧ Agrees (commands false) producer importer (consumer test) exports reached :=
  preloaded_agrees (commands := commands false) (plan false) prod (consumer test) imp (covered test producer.program) caller

private def runImport (test : ImportCase) (warm : Bool) : Option (Loader.Result Modules.Published) := do
  let producer ← (resolve (commands false)).toOption
  let importer ← (resolve (consumer test).commands producer.program).toOption
  let manifest := graph producer importer (consumer test)
  let caller : Loader.Session := { runtime := {iterators := [123]} }
  if warm then
    match Loader.load importer.program manifest 0 caller with
    | .ok _ state => some (Loader.load importer.program manifest 1 state)
    | .error .. => none
  else
    some (Loader.load importer.program manifest 1 caller)

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


private def wrapperMapping (test : ImportCase) : Mapping ⟨[], ["loaded"], ["relay", "result"]⟩ :=
  match test with
  | .bodyError => ⟨[(.string "key", starlark%[8])], [(.atom (.string "key"), int 8)], [],
      .entry (.string "key") (.plain (.int 8)) .empty⟩
  | .ok | .missing => ⟨[(.string "extra", starlark%[9])], [(.atom (.string "extra"), int 9)], [],
      .entry (.string "extra") (.plain (.int 9)) .empty⟩

private def consumerWrapper (test : ImportCase) : Imports.Wrapper where
  label := "prodé.star"
  imported := match test with | .ok | .bodyError => "escaped" | .missing => "absent"
  alias := "loaded"
  name := "relay"
  destination := "result"
  publicImport := by cases test <;> simp [Modules.isPublic, String.startsWith_string_eq_false_iff]
  legalAlias := by decide
  legalName := by decide
  separate := by decide
  arguments := []
  codes := []
  reads := []
  operands := .nil
  keywords := ⟨[("another", starlark%[[71]])], [("another", boxed 71)], [],
    .cons (.list (.int 71)) .nil, by decide⟩
  star := some (.list (.cons (.int 17) (.cons (.int 18) .nil)))
  mapping := some (wrapperMapping test)
  selects := by cases test <;> exact .enclosing (.enclosing (by decide) (by decide)) .nil

private theorem wrapperCovered (test : ImportCase) :
    (∃ callee, exports (consumerWrapper test).imported = some callee) ∨
      (consumerWrapper test).imported ∉ Trace.names (commands false) := by
  cases test
  · exact .inl ⟨.nested returned, rfl⟩
  · exact .inl ⟨.nested returned, rfl⟩
  · exact .inr (by decide)

example (test : ImportCase) {producer importer : ResolvedModule}
    (prod : resolve (commands false) #[] = .ok producer)
    (imp : resolve (consumerWrapper test).commands producer.program = .ok importer)
    (caller : Lists.State) : (consumerWrapper test).Agrees producer importer (commands false) exports ⟨caller, []⟩ :=
  Imports.Wrapper.cold_agrees (commands := commands false) (consumerWrapper test) (plan false) prod imp (wrapperCovered test) caller

private def runWrapper (test : ImportCase) (warm : Bool) : Option (Loader.Result Modules.Published) := do
  let wrapper := consumerWrapper test
  let producer ← (resolve (commands false)).toOption
  let importer ← (resolve wrapper.commands producer.program).toOption
  let manifest := wrapper.graph producer importer
  let caller : Loader.Session := { runtime := {iterators := [123]} }
  if warm then
    match Loader.load importer.program manifest 0 caller with
    | .ok _ state => some (Loader.load importer.program manifest 1 state)
    | .error .. => none
  else
    some (Loader.load importer.program manifest 1 caller)

private def wrapped (warm : Bool) : Bool :=
  match runWrapper .ok warm with
  | some (.ok published final) =>
    match final.cache.lookup 0, published.exports.lookup "relay", published.exports.lookup "result" with
    | some producer, some (.function relay), some (.list result) =>
      match producer.exports.lookup "escaped", producer.exports.lookup "late", producer.exports.lookup "data" with
      | some (.function escaped), some (.list late), some (.list data) =>
        match final.runtime.heap[relay]?, final.runtime.heap[escaped]? with
        | some ⟨.function wrapper, true⟩, some ⟨.function imported, true⟩ =>
          final.cache.map Prod.fst == [1, 0] && wrapper.declaration == 2 && imported.declaration == 0 &&
          imported.defaults == [(fileSlot "key", .list data)] && result == late &&
          published.exports.lookup "loaded" == none && (final.runtime.slots (fileSlot "loaded")).isNone &&
          final.runtime.heap[late]? == some ⟨.list [.scalar (.int 83)], true⟩ &&
          final.runtime.iterators == [123] &&
          (match wrapper.captures, imported.captures with
           | [alias], [localCapture, globalCapture] =>
             final.runtime.heap[alias.address]? == some ⟨.binding (some (.function escaped)), true⟩ &&
             final.runtime.heap[globalCapture.address]? == some ⟨.binding (some (.list late)), false⟩ &&
             (match final.runtime.heap[localCapture.address]? with
              | some ⟨.binding (some (.list rebound)), true⟩ =>
                final.runtime.heap[rebound]? == some ⟨.list [.scalar (.int 52)], true⟩
              | _ => false)
           | _, _ => false)
        | _, _ => false
      | _, _, _ => false
    | _, _, _ => false
  | _ => false

#guard wrapped false
#guard wrapped true

private def failedWrapper (test : ImportCase) (warm : Bool) (expected : Modules.Error) (retained : List Int) : Bool :=
  match runWrapper test warm with
  | some (.error (.initialization 1 error) final) =>
    let lists := final.runtime.heap.toList.filterMap fun cell => match cell.contents, cell.frozen with
      | .list [.scalar (.int n)], false => some n
      | _, _ => none
    let hasWrapper := final.runtime.heap.any fun cell => match cell.contents, cell.frozen with
      | .function closure, false => closure.declaration == 2
      | _, _ => false
    let reachedWrapper := match test with | .missing => false | _ => true
    error == expected && final.cache.map Prod.fst == [0] && lists == retained &&
      hasWrapper == reachedWrapper && (final.runtime.slots (globalSlot "result")).isNone &&
      (final.runtime.slots (fileSlot "loaded")).isNone && final.runtime.iterators == [123]
  | _ => false

#guard failedWrapper .missing false (.missingExport "prodé.star" "absent") [61, 44]
#guard failedWrapper .missing true (.missingExport "prodé.star" "absent") [61, 44]
#guard failedWrapper .bodyError false (.runtime .indexTarget) [61, 44, 71, 44]
#guard failedWrapper .bodyError true (.runtime .indexTarget) [61, 44, 71, 44]


private def declarationGlobals : List String :=
  ["first", "copied", "marker", "second", "firstOut", "secondOut", "after"]

private def relayMapping (second bad : Bool) : Mapping ⟨[], ["loaded"], declarationGlobals⟩ :=
  if second then
    if bad then
      ⟨[(.string "key", starlark%[8])], [(.atom (.string "key"), int 8)], [],
        .entry (.string "key") (.plain (.int 8)) .empty⟩
    else
      ⟨[(.string "key", starlark%[[72]])], [(.atom (.string "key"), boxed 72)], [],
        .entry (.string "key") (.plain (.list (.int 72))) .empty⟩
  else
    ⟨[(.string "extra", starlark%[9])], [(.atom (.string "extra"), int 9)], [],
      .entry (.string "extra") (.plain (.int 9)) .empty⟩

private def relayDeclaration (second bad : Bool) : Imports.WrapperDeclaration "loaded" declarationGlobals where
  name := if second then "second" else "first"
  target := by cases second <;> decide
  legalAlias := by decide
  arguments := []
  codes := []
  reads := []
  operands := .nil
  keywords := ⟨[("another", starlark%[[71]])], [("another", boxed 71)], [],
    .cons (.list (.int 71)) .nil, by decide⟩
  star := some (.list (.cons (.int 17) (.cons (.int 18) .nil)))
  mapping := some (relayMapping second bad)
  selects := by cases second <;> cases bad <;> exact .enclosing (.enclosing (by decide) (by decide)) .nil

private def callDeclaration (second : Bool) : Imports.Invocation "loaded" declarationGlobals where
  callee := if second then "second" else "copied"
  declared := .inr (by cases second <;> decide)
  legal := by cases second <;> decide
  destination := if second then "secondOut" else "firstOut"
  destinationGlobal := by cases second <;> decide
  arguments := []
  codes := []
  reads := []
  operands := .nil
  keywords := .empty

private def declarationSuite (bad : Bool) : Consumer where
  label := "prodé.star"
  name := "escaped"
  alias := "loaded"
  publicName := by simp [Modules.isPublic, String.startsWith_string_eq_false_iff]
  globals := declarationGlobals
  body :=
    [.define (relayDeclaration false bad),
     .assign "copied" (by decide) (.read (by decide) (.global (by decide) (by decide) (by decide))
       (.module (by decide) (by decide) (by decide))) (.name "first"),
     .assign "marker" (by decide) (.list (.int 88)) .forget,
     .define (relayDeclaration true bad),
     .invoke (callDeclaration false),
     .invoke (callDeclaration true),
     .assign "after" (by decide) (.list (.int 199)) .forget]
  declared := rfl
  separate := by decide

private theorem declarationCovered (bad : Bool) (program : Program) :
    Covered exports (commands false) (declarationSuite bad) program :=
  .inl ⟨.nested returned, rfl,
    ⟨.wrapper (relayDeclaration false bad) program.size, rfl,
      ⟨.wrapper (relayDeclaration true bad) (program.push (relayDeclaration false bad).site.declaration).size, rfl, trivial⟩⟩⟩

example (bad : Bool) {producer importer : ResolvedModule}
    (prod : resolve (commands false) #[] = .ok producer)
    (imp : resolve (declarationSuite bad).commands producer.program = .ok importer)
    (caller : Lists.State) :
    Agrees (commands false) producer importer (declarationSuite bad) exports ⟨caller, []⟩ :=
  cold_agrees (commands := commands false) (plan false) prod (declarationSuite bad) imp
    (declarationCovered bad producer.program) caller

private def runDeclarationSuite (consumer : Consumer) (warm : Bool) : Option (Loader.Result Modules.Published × Lists.State) := do
  let producer ← (resolve (commands false)).toOption
  let importer ← (resolve consumer.commands producer.program).toOption
  let manifest := graph producer importer consumer
  let caller : Loader.Session := { runtime := { iterators := [123] } }
  let entry ← if warm then
      match Loader.load importer.program manifest 0 caller with
      | .ok _ reached => some reached
      | .error .. => none
    else some caller
  some (Loader.load importer.program manifest 1 entry, enter importer.source entry.runtime)

private def relaySuiteSuccess (warm : Bool) : Bool :=
  match runDeclarationSuite (declarationSuite false) warm with
  | some (.ok published final, _) =>
    let heap := final.runtime.heap
    match final.cache.lookup 0, published.exports.lookup "first", published.exports.lookup "second" with
    | some producer, some (.function first), some (.function second) =>
      match producer.exports.lookup "late", producer.exports.lookup "escaped", producer.exports.lookup "data",
        heap[first]?, heap[second]? with
      | some (.list late), some (.function escaped), some (.list data),
          some ⟨.function firstRecord, true⟩, some ⟨.function secondRecord, true⟩ =>
        first != second && firstRecord.declaration == 2 && secondRecord.declaration == 3 &&
        firstRecord.captures == secondRecord.captures &&
        (match firstRecord.captures, heap[escaped]? with
         | [capture], some ⟨.function original, true⟩ =>
           original.declaration == 0 && original.defaults == [(fileSlot "key", .list data)] &&
           heap[capture.address]? == some ⟨.binding (some (.function escaped)), true⟩
         | _, _ => false) &&
        published.exports.lookup "copied" == some (.function first) &&
        published.exports.lookup "firstOut" == some (.list late) &&
        published.exports.lookup "secondOut" == some (.list late) &&
        final.cache.map Prod.fst == [1, 0] && final.runtime.iterators == [123]
      | _, _, _, _, _ => false
    | _, _, _ => false
  | _ => false

private def relaySuiteFailure (warm : Bool) : Bool :=
  match runDeclarationSuite (declarationSuite true) warm with
  | some (.error (.initialization 1 (.runtime .indexTarget)) final, entered) =>
    let cell name := (entered.slots (globalSlot name)).bind (fun slot => final.runtime.heap[slot.address]?)
    let allocations := final.runtime.heap.toList.filterMap fun cell =>
      match cell.contents, cell.frozen with
      | .list [.scalar (.int n)], false => some n
      | _, _ => none
    match final.cache.lookup 0 with
    | some producer =>
      final.cache.map Prod.fst == [0] && final.runtime.iterators == [123] &&
      (final.runtime.slots (fileSlot "loaded")).isNone &&
      cell "first" == cell "copied" &&
      cell "firstOut" == some ⟨.binding (producer.exports.lookup "late"), false⟩ &&
      cell "secondOut" == some ⟨.binding none, false⟩ && cell "after" == some ⟨.binding none, false⟩ &&
      allocations == [61, 44, 88, 71, 44, 71, 44]
    | none => false
  | _ => false

#guard relaySuiteSuccess false
#guard relaySuiteSuccess true
#guard relaySuiteFailure false
#guard relaySuiteFailure true


private def factoryWrapperGlobals : List String := ["make", "held", "result"]

private def factoryWrapper : Imports.WrapperDeclaration "loaded" factoryWrapperGlobals where
  name := "make"
  target := by decide
  legalAlias := by decide
  arguments := [starlark%[[41]]]
  codes := [boxed 41]
  reads := []
  operands := .cons (.list (.int 41)) .nil
  keywords := .empty
  selects := .enclosing (.enclosing (by decide) (by decide)) .nil

private def factoryWrapperConsumer : Consumer where
  label := "prodé.star"
  name := "factory"
  alias := "loaded"
  publicName := by simp [Modules.isPublic, String.startsWith_string_eq_false_iff]
  globals := factoryWrapperGlobals
  body := [.define factoryWrapper,
    .invoke { callee := "make", declared := .inr (by decide), legal := by decide
              destination := "held", destinationGlobal := by decide
              arguments := [], codes := [], reads := [], operands := .nil, keywords := .empty },
    .invoke { callee := "held", declared := .inr (by decide), legal := by decide
              destination := "result", destinationGlobal := by decide
              arguments := [starlark%[17]], codes := [int 17], reads := [], operands := .cons (.int 17) .nil
              keywords := .empty }]
  declared := rfl
  separate := by decide

example {producer importer : ResolvedModule} (prod : resolve (commands false) #[] = .ok producer)
    (imp : resolve factoryWrapperConsumer.commands producer.program = .ok importer)
    (caller : Lists.State) :
    Agrees (commands false) producer importer factoryWrapperConsumer exports ⟨caller, []⟩ :=
  cold_agrees (commands := commands false) (plan false) prod factoryWrapperConsumer imp
    (.inl ⟨root.callable, rfl, ⟨.wrapper factoryWrapper producer.program.size, rfl,
      ⟨.regular (.nested returned), rfl, trivial⟩⟩⟩) caller

#guard
  match runDeclarationSuite factoryWrapperConsumer false with
  | some (.ok published final, _) =>
    match final.cache.lookup 0, published.exports.lookup "held" with
    | some producer, some (.function held) =>
      match producer.exports.lookup "escaped", final.runtime.heap[held]? with
      | some (.function escaped), some ⟨.function closure, true⟩ =>
        held != escaped && closure.declaration == 0 &&
        published.exports.lookup "result" == producer.exports.lookup "late" &&
        (match closure.defaults with
         | [(slot, .list saved)] =>
           slot == fileSlot "key" && final.runtime.heap[saved]? == some ⟨.list [.scalar (.int 41)], true⟩
         | _ => false)
      | _, _ => false
    | _, _ => false
  | _ => false


private def middleGlobals : List String := ["relay", "before", "reexport"]

private def middleWrapper : Imports.WrapperDeclaration "loaded" middleGlobals where
  name := "relay"
  target := by decide
  legalAlias := by decide
  arguments := [starlark%[17]]
  codes := [int 17]
  reads := []
  operands := .cons (.int 17) .nil
  keywords := .empty
  selects := .enclosing (.enclosing (by decide) (by decide)) .nil

private def middleConsumer : Consumer where
  label := "prodé.star"
  name := "escaped"
  alias := "loaded"
  publicName := by simp [Modules.isPublic, String.startsWith_string_eq_false_iff]
  globals := middleGlobals
  body :=
    [.define middleWrapper,
     .invoke { callee := "relay", declared := .inr (by decide), legal := by decide
               destination := "before", destinationGlobal := by decide
               arguments := [], codes := [], reads := [], operands := .nil, keywords := .empty },
     .assign "reexport" (by decide) (.read (by decide) (.owned (by decide)) (.owned (by decide)))
       (.name "loaded")]
  declared := rfl
  separate := by decide

private def lastGlobals : List String := ["held", "first", "marker", "answer", "after"]

private def lastMapping (bad : Bool) : Mapping (block "transferred" lastGlobals) :=
  if bad then ⟨[(.string "key", starlark%[8])], [(.atom (.string "key"), int 8)], [],
    .entry (.string "key") (.plain (.int 8)) .empty⟩
  else ⟨[(.string "key", starlark%[[72]])], [(.atom (.string "key"), boxed 72)], [],
    .entry (.string "key") (.plain (.list (.int 72))) .empty⟩

private def lastCall (second bad : Bool) : Imports.Invocation "transferred" lastGlobals where
  callee := "held"
  declared := .inr (by decide)
  legal := by decide
  destination := if second then "answer" else "first"
  destinationGlobal := by cases second <;> decide
  arguments := []
  codes := []
  reads := []
  operands := .nil
  keywords := ⟨[("another", starlark%[[71]])], [("another", boxed 71)], [],
    .cons (.list (.int 71)) .nil, by decide⟩
  star := some (.list (.cons (.int 17) (.cons (.int 18) .nil)))
  mapping := if second then some (lastMapping bad) else none

private def lastConsumer (bad : Bool) : Consumer where
  label := "middle.star"
  name := "reexport"
  alias := "transferred"
  publicName := by simp [Modules.isPublic, String.startsWith_string_eq_false_iff]
  globals := lastGlobals
  body :=
    [.assign "held" (by decide) (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.name "transferred"),
     .invoke (lastCall false bad),
     .assign "marker" (by decide) (.list (.int 88)) .forget,
     .invoke (lastCall true bad),
     .assign "after" (by decide) (.list (.int 199)) .forget]
  declared := rfl
  separate := by decide

private def chainManifest (producer middle last : ResolvedModule) : Loader.Manifest :=
  #[⟨producer.source, []⟩, ⟨middle.source, [("prodé.star", 0)]⟩, ⟨last.source, [("middle.star", 1)]⟩]

private def chainExports (producer middle : Program) (bad : Bool) : Nat → Environment
  | 0 => exports
  | 1 => Imports.Chain.exportsOf middleConsumer producer (.nested returned)
  | _ => Imports.Chain.exportsOf (lastConsumer bad) middle (.nested returned)

private def checkedChain (bad : Bool) {producer middle last : ResolvedModule}
    (producerChecked : resolve (commands false) #[] = .ok producer)
    (middleChecked : resolve middleConsumer.commands producer.program = .ok middle)
    (lastChecked : resolve (lastConsumer bad).commands middle.program = .ok last) :
    Imports.Chain.Graph producer.program (chainManifest producer middle last) where
  commands := (lastConsumer bad).commands
  seed := middle.program
  linked := last
  checked := lastChecked
  includesOrigin := fun index entry seen =>
    consumer_preserves (lastConsumer bad) lastChecked index entry (consumer_preserves middleConsumer middleChecked index entry seen)
  exports := chainExports producer.program middle.program bad
  nodes := by
    intro id bound
    have range : id = 0 ∨ id = 1 ∨ id = 2 := by
      change id < 3 at bound
      omega
    rcases range with rfl | rfl | rfl
    · exact .root (commands := commands false) (plan false) producerChecked (fun _ _ seen => seen) rfl
    · apply Imports.Chain.Node.importer middleConsumer (show 0 < 1 by decide)
        middleChecked (fun _ _ seen => seen) (consumer_preserves (lastConsumer bad) lastChecked) rfl rfl
      exact .found (.nested returned) rfl ⟨.wrapper middleWrapper producer.program.size, rfl, trivial⟩
    · apply Imports.Chain.Node.importer (lastConsumer bad) (show 1 < 2 by decide)
        lastChecked (consumer_preserves middleConsumer middleChecked) (fun _ _ seen => seen) rfl rfl
      exact .found (.nested returned) rfl ⟨.regular (.nested returned), rfl, ⟨.regular (.nested returned), rfl, trivial⟩⟩

example (bad : Bool) {producer middle last : ResolvedModule}
    (prod : resolve (commands false) #[] = .ok producer)
    (mid : resolve middleConsumer.commands producer.program = .ok middle)
    (checked : resolve (lastConsumer bad).commands middle.program = .ok last)
    (caller : Lists.State) (history : List Nat) (bounded : ∀ id ∈ history, id < 3) :
    let graph := checkedChain bad prod mid checked
    ∃ entered out, Imports.Chain.Requests graph history ⟨caller, []⟩ entered ∧
      Imports.Chain.TraceRun (chainManifest producer middle last) 2 entered out ∧
      Loader.load last.program (chainManifest producer middle last) 2 entered = out ∧
      Imports.Chain.Cache producer.program (chainManifest producer middle last) graph.exports (Imports.Chain.resultSession out) := by
  intro graph
  have empty : Imports.Chain.Cache producer.program (chainManifest producer middle last) graph.exports ⟨caller, []⟩ := by
    intro id published seen
    cases seen
  obtain ⟨entered, preload, cache⟩ := Imports.Chain.requests graph history bounded ⟨caller, []⟩ empty
  obtain ⟨out, source, _, meaning, reached⟩ := Imports.Chain.agrees graph 2 (by change 2 < 3; decide) entered cache
  exact ⟨entered, out, preload, source, meaning, reached.cache⟩

private def runChainCommands (source : List Resolve.Command) (preload : Option Nat) :
    Option (Loader.Result Modules.Published × Lists.State) := do
  let producer ← (resolve (commands false)).toOption
  let middle ← (resolve middleConsumer.commands producer.program).toOption
  let last ← (resolve source middle.program).toOption
  let manifest := chainManifest producer middle last
  let cold : Loader.Session := { runtime := {iterators := [123]} }
  let ready ← match preload with
    | none => some cold
    | some id =>
      match Loader.load last.program manifest id cold with
      | .ok _ state => some state
      | .error .. => none
  some (Loader.load last.program manifest 2 ready, enter last.source ready.runtime)

private def runChain (bad : Bool) : Option Nat → Option (Loader.Result Modules.Published × Lists.State) :=
  runChainCommands (lastConsumer bad).commands

private def chainOK (preload : Option Nat) : Bool :=
  match runChain false preload with
  | some (.ok published final, _) =>
    match final.cache.lookup 0, final.cache.lookup 1 with
    | some producer, some middle =>
      match producer.exports.lookup "escaped", producer.exports.lookup "late",
        producer.exports.lookup "data", middle.exports.lookup "relay" with
      | some (.function address), some (.list late), some (.list data), some (.function wrapper) =>
        match final.runtime.heap[address]?, final.runtime.heap[wrapper]? with
        | some ⟨.function closure, true⟩, some ⟨.function linked, true⟩ =>
          closure.declaration == 0 && linked.declaration == 2 &&
          closure.defaults == [(fileSlot "key", .list data)] &&
          (match closure.captures, linked.captures with
           | [_, global], [capturedImport] =>
             final.runtime.heap[global.address]? == some ⟨.binding (some (.list late)), false⟩ &&
             final.runtime.heap[capturedImport.address]? == some ⟨.binding (some (.function address)), true⟩
           | _, _ => false) &&
          middle.exports.lookup "reexport" == some (.function address) &&
          middle.exports.lookup "before" == some (.list late) &&
          published.exports.lookup "held" == some (.function address) &&
          published.exports.lookup "first" == some (.list late) &&
          published.exports.lookup "answer" == some (.list late) &&
          final.runtime.heap[late]? == some ⟨.list [.scalar (.int 83)], true⟩ &&
          final.cache.map Prod.fst == [2, 1, 0] && final.runtime.iterators == [123]
        | _, _ => false
      | _, _, _, _ => false
    | _, _ => false
  | _ => false

private def chainError (preload : Option Nat) : Bool :=
  match runChain true preload with
  | some (.error (.initialization 2 (.runtime .indexTarget)) final, entered) =>
    let cell name := (entered.slots (globalSlot name)).bind (fun slot => final.runtime.heap[slot.address]?)
    let marker := match cell "marker" with
      | some ⟨.binding (some (.list address)), false⟩ =>
        final.runtime.heap[address]? == some ⟨.list [.scalar (.int 88)], false⟩
      | _ => false
    match final.cache.lookup 0 with
    | some producer =>
      marker && cell "held" == some ⟨.binding (producer.exports.lookup "escaped"), false⟩ &&
      cell "first" == some ⟨.binding (producer.exports.lookup "late"), false⟩ &&
      cell "answer" == some ⟨.binding none, false⟩ && cell "after" == some ⟨.binding none, false⟩ &&
      (final.runtime.slots (fileSlot "transferred")).isNone && final.runtime.iterators == [123] &&
      final.cache.map Prod.fst == [1, 0]
    | none => false
  | _ => false

#guard chainOK none
#guard chainOK (some 0)
#guard chainOK (some 1)
#guard chainError none
#guard chainError (some 0)
#guard chainError (some 1)


-- The resolved loader also dispatches a published wrapper across the next
-- module edge. The independent chain theorem above tracks regular re-exports.
private def callPublishedWrapper : List Resolve.Command :=
  [.load "middle.star" [⟨"relay", "wrapped"⟩], .assign "result"
    (.call (.scalar (.read "wrapped")) [] [] none none)]

#guard
  match runChainCommands callPublishedWrapper (some 1) with
  | some (.ok published final, _) =>
    match final.cache.lookup 0 with
    | some producer =>
      published.exports.lookup "result" == producer.exports.lookup "late" &&
      final.cache.map Prod.fst == [2, 1, 0] && final.runtime.iterators == [123]
    | none => false
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
