module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive

open scoped Functions.Lowering.Quote
open Assignment (LexicalBlock)
open Functions (FreeName Program)

private def enclosingBlock : LexicalBlock := ⟨["factory"], [], []⟩

private def factoryBlock : LexicalBlock := ⟨["x", "index", "relay", "copy"], enclosingBlock.owned, []⟩

private def relayBlock : LexicalBlock := ⟨["leaf"], factoryBlock.owned ++ factoryBlock.enclosing, []⟩

private def localRead (name : String) : Functions.Lowering.Expr := Leaf.readOperand (fileSlot name)

private def returnName (name : String) : Statement := .ret (some (.scalar (.read name)))

private def leafSuite : Body.Suite :=
  .assign "offset" starlark%[index] (.assign "alias" starlark%[x] (.ret starlark%[saved[offset]]))

private def leafParameters : Parameters := ⟨[], [("saved", starlark%[x])]⟩

private def leafSite : Site relayBlock where
  name := "leaf"
  target := by decide
  parameters := leafParameters
  source := leafSuite.source
  binders := ["offset", "alias"]
  locals := ["offset", "alias"]
  collects := .seq (.assign _ _) (.seq (.assign _ _) (.ret _))
  localOrder := .keep (by decide) (.keep (by decide) .nil)
  body := ⟨.seq (.assignExpr (fileSlot "offset") (localRead "index"))
    (.seq (.assignExpr (fileSlot "alias") (localRead "x"))
     (.returnExpr (.index (localRead "saved") (localRead "offset")))),
    [fileSlot "index", fileSlot "x", fileSlot "saved", fileSlot "offset"]⟩
  free := [⟨fileSlot "index", fileSlot "index"⟩, ⟨fileSlot "x", fileSlot "x"⟩]
  selects := .enclosing (.enclosing (by decide) (by decide))
    (.enclosing (.enclosing (by decide) (by decide))
      (.owned (.owned (by decide)) (.owned (.owned (by decide)) .nil)))
  defaults := [⟨"saved", starlark%[x], localRead "x", [fileSlot "x"]⟩]
  lexical := .cons (.read (by decide) (.enclosing (by decide) (by decide)) (.enclosing (by decide) (by decide))) .nil

private theorem leafBody (seed : Program) :
    Elaborates leafSite.block leafSite.source seed leafSite.body seed [] :=
  .straight (.assign (by decide)
    (.read (by decide) (.enclosing (by decide) (by decide)) (.enclosing (by decide) (by decide)))
    (.assign (by decide)
      (.read (by decide) (.enclosing (by decide) (by decide)) (.enclosing (by decide) (by decide)))
      (.ret (.index (.read (by decide) (.owned (by decide)) (.owned (by decide)))
        (.read (by decide) (.owned (by decide)) (.owned (by decide)))))))

private def relaySite (seed : Program) : Site factoryBlock where
  name := "relay"
  target := by decide
  parameters := ⟨[], []⟩
  source := .seq leafSite.statement (returnName "leaf")
  binders := ["leaf"]
  locals := ["leaf"]
  collects := .seq (.define _ _ _) (.ret _)
  localOrder := .keep (by decide) .nil
  body := ⟨.seq (.define (fileSlot "leaf") seed.size) (.returnExpr (localRead "leaf")),
    leafSite.reads ++ [fileSlot "leaf"]⟩
  -- The default reads x before the body's first free reference index.
  free := [⟨fileSlot "x", fileSlot "x"⟩, ⟨fileSlot "index", fileSlot "index"⟩]
  selects := .enclosing (.enclosing (by decide) (by decide))
    (.enclosing (.enclosing (by decide) (by decide)) (.owned (.owned (by decide)) .nil))
  defaults := []
  lexical := .nil

private theorem relayBody (seed : Program) :
    Elaborates (relaySite seed).block (relaySite seed).source seed (relaySite seed).body
      (seed.push leafSite.declaration) [(seed.size, leafSite.declaration)] :=
  .define leafSite .nil (leafBody seed) (.straight (.ret (.read (by decide) (.owned (by decide)) (.owned (by decide)))))

private def factoryTail : Body.Suite := .assign "copy" starlark%[relay] (.ret starlark%[copy])

private def factorySite (seed : Program) : Site enclosingBlock where
  name := "factory"
  target := by decide
  parameters := ⟨["x", "index"], []⟩
  source := .seq (relaySite seed).statement factoryTail.source
  binders := ["relay", "copy"]
  locals := ["relay", "copy"]
  collects := .seq (.define _ _ _) (.seq (.assign _ _) (.ret _))
  localOrder := .keep (by decide) (.keep (by decide) .nil)
  body := ⟨.seq (.define (fileSlot "relay") (seed.size + 1))
    (.seq (.assignExpr (fileSlot "copy") (localRead "relay")) (.returnExpr (localRead "copy"))),
    [fileSlot "x", fileSlot "index", fileSlot "relay", fileSlot "copy"]⟩
  free := []
  selects := .owned (.owned (by decide)) (.owned (.owned (by decide))
    (.owned (.owned (by decide)) (.owned (.owned (by decide)) .nil)))
  defaults := []
  lexical := .nil

private def factoryTable (seed : Program) : Program :=
  (seed.push leafSite.declaration).push (relaySite seed).declaration

private theorem factoryBody (seed : Program) :
    Elaborates (factorySite seed).block (factorySite seed).source seed (factorySite seed).body (factoryTable seed)
      [(seed.size, leafSite.declaration), (seed.size + 1, (relaySite seed).declaration)] := by
  have last : Body.Elaborates factoryBlock factoryTail
      (.seq (.assignExpr (fileSlot "copy") (localRead "relay")) (.returnExpr (localRead "copy")))
      [fileSlot "relay", fileSlot "copy"] :=
    .assign (by decide) (.read (by decide) (.owned (by decide)) (.owned (by decide)))
      (.ret (.read (by decide) (.owned (by decide)) (.owned (by decide))))
  simpa [Array.size_push, Body.prependSource, Body.prependCode, relaySite, factorySite, factoryTable, Site.reads,
    Site.defaultsInOrder, Site.block, parameterNames, factoryBlock, Parameters.names, enclosingBlock] using
    (Elaborates.define (relaySite seed) .nil (relayBody seed) (.straight last))

example (seed : Program) :
    let final := factoryTable seed
    PreservesDeclarations seed final ∧ final[seed.size]? = some leafSite.declaration ∧
      final[seed.size + 1]? = some (relaySite seed).declaration := by
  obtain ⟨stable, emitted⟩ := links (factoryBody seed)
  exact ⟨stable, emitted (seed.size, leafSite.declaration) (by simp),
    emitted (seed.size + 1, (relaySite seed).declaration) (by simp)⟩

example (seed : Program) :
    compileBody ⟨factoryBlock.context, .local⟩ (factorySite seed).source seed =
      .ok ((factorySite seed).body, factoryTable seed) :=
  compiles (factoryBody seed)

-- The activation supplies every owned slot and uses the generic recursive
-- execution rule, even though the relay to be returned has a nested body.
example (seed : Program) (caller : Lists.State) (x : Lists.Value) (index : Int) :
    let site := factorySite seed
    let program := factoryTable seed
    let active := Functions.activate caller site.declaration []
      [(fileSlot "x", x), (fileSlot "index", .scalar (.int index))]
    ∃ out, Runs factoryBlock active site.source site.body.code out ∧
      Functions.denoteBody program (List.range program.size) site.body.code active = out ∧
      (Lists.Iteration.finishState (Leaf.returnTo caller out)).slots = caller.slots := by
  obtain ⟨out, ran, _, _, meaning, restored, _, _⟩ :=
    runs_activated (factorySite seed) (factoryBody seed) (factoryTable seed) (fun _ _ same => same)
      (List.range (factoryTable seed).size) caller caller [] .nil (by simp [Body.CaptureCells])
      [(fileSlot "x", x), (fileSlot "index", .scalar (.int index))]
  exact ⟨out, ran, meaning, restored⟩

private def noise : Command := .define "noise" (.required []) (.ret (some starlark%[0]))

private def factory (shadowed malformed : Bool) (failed : Bool := false) : Command :=
  let parameters := if malformed then { leafParameters with required := ["saved"] } else leafParameters
  let relay := Statement.define "relay" (.required (if shadowed then ["x"] else []))
    (.seq (.define "leaf" parameters.source leafSuite.source) (returnName "leaf"))
  let leading := if failed then
    [("marker", starlark%[[73]]), ("broken", starlark%[marker[1]]), ("later", starlark%[[99]])]
    else []
  .define "factory" (.required ["x", "index"]) (.seq relay (Body.prependSource leading factoryTail.source))

private def commands (shadowed malformed : Bool) (failed : Bool := false) : List Command :=
  [noise, .assign "values" starlark%[[11,22]], .assign "near" starlark%[[33,44]],
   factory shadowed malformed failed, .assign "relay_fn" starlark%[factory(values,1)],
   .assign "leaf_fn" (if shadowed then starlark%[relay_fn(near)] else starlark%[relay_fn()]),
   .assign "result" starlark%[leaf_fn()]]

private def checks (shadowed : Bool) : Bool :=
  let cmds := commands shadowed false
  match resolve cmds, runModule cmds (fun _ => none) {} with
  | .ok resolved, .ok (.ok published final) =>
    let get name := published.exports.lookup name
    let free := resolved.program.toList.map fun declaration => declaration.free.map FreeName.source
    free == [[], [fileSlot "index", fileSlot "x"], (if shadowed then [fileSlot "index"] else [fileSlot "x", fileSlot "index"]), []] &&
    get "result" == some (.scalar (.int (if shadowed then 44 else 22))) &&
    (match get "relay_fn", get "leaf_fn" with
    | some (.function relay), some (.function leaf) =>
      match final.heap[relay]?, final.heap[leaf]? with
      | some ⟨.function relayClosure, true⟩, some ⟨.function leafClosure, true⟩ =>
        match leafClosure.captures, leafClosure.defaults with
        | [index, x], [(saved, value)] =>
          relayClosure.declaration == 2 && leafClosure.declaration == 1 &&
          saved == fileSlot "saved" && some value == get (if shadowed then "near" else "values") &&
          (if shadowed then relayClosure.captures == [index] && x.address > relay
            else relayClosure.captures == [x, index] && x.address < relay) &&
          final.heap[x.address]? == some ⟨.binding (some value), true⟩
        | _, _ => false
      | _, _ => false
    | _, _ => false)
  | _, _ => false

#guard checks false
#guard checks true

#guard
  match resolve (commands false true) with
  | .error (.validation (.syntax (.duplicateParameter "saved"))) => true
  | _ => false

-- A reached index error after installing the relay retains that closure
-- and the marker allocation. Later statements and the relay call never run.
#guard
  let cmds := commands false false true
  let caller : Lists.State := { iterators := [123] }
  match resolve cmds, runModule cmds (fun _ => none) caller with
  | .ok resolved, .ok (.error (.runtime (.indexRange 1 1)) final) =>
    let entered := enter resolved.source caller
    let moduleCell name := (entered.slots (globalSlot name)).bind (fun slot => final.heap[slot.address]?)
    let reached := final.heap.toList.filterMap fun cell => match cell.contents with
      | .function closure => some closure.declaration
      | _ => none
    reached == [0, 3, 2] &&
    final.heap.back? == some ⟨.list [.scalar (.int 73)], false⟩ &&
    moduleCell "relay_fn" == some ⟨.binding none, false⟩ &&
    moduleCell "leaf_fn" == some ⟨.binding none, false⟩ &&
    moduleCell "result" == some ⟨.binding none, false⟩ &&
    (final.slots (globalSlot "factory")).isNone && final.iterators == [123]
  | _, _ => false

private inductive CallCase where
  | defaults
  | operandError
  | arityError

private def chainBlock : LexicalBlock :=
  ⟨["x", "index", "outerMark", "relay", "relayCopy", "outerValue", "outerAfter"], enclosingBlock.owned, []⟩

private def callRelayBlock : LexicalBlock :=
  ⟨["leaf", "copy", "value", "after"], chainBlock.owned ++ chainBlock.enclosing, []⟩

private def callLeafSuite : Body.Suite :=
  .assign "offset" starlark%[index] (.assign "alias" starlark%[[x]] (.ret starlark%[saved[offset]]))

private def callLeafSite : Site callRelayBlock where
  name := "leaf"
  target := by decide
  parameters := leafParameters
  source := callLeafSuite.source
  binders := ["offset", "alias"]
  locals := ["offset", "alias"]
  collects := .seq (.assign _ _) (.seq (.assign _ _) (.ret _))
  localOrder := .keep (by decide) (.keep (by decide) .nil)
  body := ⟨.seq (.assignExpr (fileSlot "offset") (localRead "index"))
    (.seq (.assignExpr (fileSlot "alias") (.list [localRead "x"]))
     (.returnExpr (.index (localRead "saved") (localRead "offset")))),
    [fileSlot "index", fileSlot "x", fileSlot "saved", fileSlot "offset"]⟩
  free := [⟨fileSlot "index", fileSlot "index"⟩, ⟨fileSlot "x", fileSlot "x"⟩]
  selects := .enclosing (.enclosing (by decide) (by decide))
    (.enclosing (.enclosing (by decide) (by decide))
      (.owned (.owned (by decide)) (.owned (.owned (by decide)) .nil)))
  defaults := [⟨"saved", starlark%[x], localRead "x", [fileSlot "x"]⟩]
  lexical := .cons (.read (by decide) (.enclosing (by decide) (by decide)) (.enclosing (by decide) (by decide))) .nil

private theorem callLeafBody (seed : Program) :
    Elaborates callLeafSite.block callLeafSite.source seed callLeafSite.body seed [] :=
  .straight (.assign (by decide)
    (.read (by decide) (.enclosing (by decide) (by decide)) (.enclosing (by decide) (by decide)))
    (.assign (by decide)
      (.list (.read (by decide) (.enclosing (by decide) (by decide)) (.enclosing (by decide) (by decide))))
      (.ret (.index (.read (by decide) (.owned (by decide)) (.owned (by decide)))
        (.read (by decide) (.owned (by decide)) (.owned (by decide)))))))

private def callArguments : CallCase → List Functions.Lowering.Resolve.SourceExpr
  | .defaults => []
  | .operandError => [starlark%[[73]], starlark%[[0][1]], starlark%[[99]]]
  | .arityError => [starlark%[[73]], starlark%[[74]]]

private def boxed (n : Int) : Functions.Lowering.Expr := .list [.atom (.scalar (.int n))]

private def callOperands : CallCase → List Functions.Lowering.Expr
  | .defaults => []
  | .operandError => [boxed 73, .index (boxed 0) (.atom (.scalar (.int 1))), boxed 99]
  | .arityError => [boxed 73, boxed 74]

private def callAssignment (mode : CallCase) : Call.Suite.Assignment callRelayBlock where
  copy := "copy"
  copyOwned := by decide
  copyLegal := by decide
  destination := "value"
  destinationOwned := by decide
  arguments := callArguments mode
  codes := callOperands mode
  argumentReads := []
  operands := by
    cases mode with
    | defaults => exact .nil
    | operandError =>
      exact .cons (.list (.int 73))
        (.cons (.index (.list (.int 0)) (.int 1)) (.cons (.list (.int 99)) .nil))
    | arityError => exact .cons (.list (.int 73)) (.cons (.list (.int 74)) .nil)

private def callTail : Body.Suite :=
  .assign "after" starlark%[[value]] (.ret starlark%[after[0]])

private def callTailCode : ResolvedBody :=
  ⟨.seq (.assignExpr (fileSlot "after") (.list [localRead "value"]))
    (.returnExpr (.index (localRead "after") (.atom (.scalar (.int 0))))),
    [fileSlot "value", fileSlot "after"]⟩

private def relayCallSource (mode : CallCase) : Statement :=
  .seq callLeafSite.statement ((callAssignment mode).source "leaf" callTail.source)

private def relayCallCode (mode : CallCase) (id : Nat) : ResolvedBody :=
  ⟨.seq (.define (fileSlot "leaf") id) ((callAssignment mode).code "leaf" callTailCode.code),
    callLeafSite.reads ++ ((callAssignment mode).reads "leaf" ++ callTailCode.reads)⟩

private theorem callProfile (mode : CallCase) (seed : Program) :
    Call.Suite.Elaborates callRelayBlock (relayCallSource mode) seed (relayCallCode mode seed.size)
      (seed.push callLeafSite.declaration) [(seed.size, callLeafSite.declaration)] [seed.size] := by
  have tail : Body.Elaborates callRelayBlock callTail callTailCode.code callTailCode.reads :=
    .assign (by decide) (.list (.read (by decide) (.owned (by decide)) (.owned (by decide))))
      (.ret (.index (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.int 0)))
  exact .call callLeafSite (by decide) (callAssignment mode) (.plain (callLeafBody seed)) (.plain (.straight tail))

example (mode : CallCase) (seed : Program) :
    compileBody ⟨callRelayBlock.context, .local⟩ (relayCallSource mode) seed =
      .ok (relayCallCode mode seed.size, seed.push callLeafSite.declaration) :=
  Call.Suite.compiles (callProfile mode seed)

-- The source-run theorem covers the very same body in success and error modes.
example (mode : CallCase) (seed : Program) {cmds : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve cmds linked = .ok resolved)
    (table : PreservesDeclarations (seed.push callLeafSite.declaration) resolved.program)
    (available : List Nat) (guarded : seed.size ∈ available) {free : List FreeName}
    (selected : Selects callRelayBlock (relayCallCode mode seed.size).reads free)
    (state : Lists.State) (floor : Nat) (frame : Body.Frame callRelayBlock free floor state) :
    ∃ out, Call.Suite.Runs callRelayBlock state (relayCallSource mode) (relayCallCode mode seed.size).code out ∧
      Functions.denoteBody resolved.program available (relayCallCode mode seed.size).code state = out := by
  have selection : Selects callRelayBlock ([] ++ (relayCallCode mode seed.size).reads ++ []) free := by simpa using selected
  obtain ⟨out, trace, _, _, _, denoted⟩ := Call.Suite.runs (callProfile mode seed) checked table available
    (by
      intro id member
      cases List.mem_singleton.mp member
      exact guarded) selection state frame
  exact ⟨out, trace, denoted⟩

private def relayCallSite (mode : CallCase) (seed : Program) : Site chainBlock where
  name := "relay"
  target := by decide
  parameters := ⟨[], []⟩
  source := relayCallSource mode
  binders := ["leaf", "copy", "value", "after"]
  locals := ["leaf", "copy", "value", "after"]
  collects := .seq (.define _ _ _) (.seq (.assign _ _) (.seq (.assign _ _) (.seq (.assign _ _) (.ret _))))
  localOrder := .keep (by decide) (.keep (by decide) (.keep (by decide) (.keep (by decide) .nil)))
  body := relayCallCode mode seed.size
  free := [⟨fileSlot "x", fileSlot "x"⟩, ⟨fileSlot "index", fileSlot "index"⟩]
  selects := .enclosing (.enclosing (by decide) (by decide))
    (.enclosing (.enclosing (by decide) (by decide))
      (.owned (.owned (by decide)) (.owned (.owned (by change "copy" ∈ callRelayBlock.owned; decide))
        (.owned (.owned (by decide)) (.owned (.owned (by decide)) .nil)))))
  defaults := []
  lexical := .nil

private def chainAssignment : Call.Suite.Assignment chainBlock :=
  ⟨"relayCopy", by decide, by decide, "outerValue", by decide, [], [], [], .nil⟩

private def chainTail : Body.Suite :=
  .assign "outerAfter" starlark%[[outerValue]] (.ret starlark%[outerAfter[0]])

private def chainTailCode : ResolvedBody :=
  ⟨.seq (.assignExpr (fileSlot "outerAfter") (.list [localRead "outerValue"]))
    (.returnExpr (.index (localRead "outerAfter") (.atom (.scalar (.int 0))))),
    [fileSlot "outerValue", fileSlot "outerAfter"]⟩

private def chainSource (mode : CallCase) : Statement :=
  Body.prependSource [("outerMark", starlark%[[17]])]
    (.seq (relayCallSite mode #[]).statement (chainAssignment.source "relay" chainTail.source))

private def chainCode (mode : CallCase) (seed : Program) : ResolvedBody :=
  let site := relayCallSite mode seed
  ⟨Body.prependCode [("outerMark", boxed 17)]
    (.seq (.define (fileSlot "relay") (seed.size + 1)) (chainAssignment.code "relay" chainTailCode.code)),
    site.reads ++ (chainAssignment.reads "relay" ++ chainTailCode.reads)⟩

private theorem chainProfile (mode : CallCase) (seed : Program) :
    Call.Suite.Elaborates chainBlock (chainSource mode) seed (chainCode mode seed)
      ((seed.push callLeafSite.declaration).push (relayCallSite mode seed).declaration)
      [(seed.size, callLeafSite.declaration), (seed.size + 1, (relayCallSite mode seed).declaration)]
      [seed.size + 1, seed.size] := by
  have ending : Body.Elaborates chainBlock chainTail chainTailCode.code chainTailCode.reads :=
    .assign (by decide) (.list (.read (by decide) (.owned (by decide)) (.owned (by decide))))
      (.ret (.index (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.int 0)))
  have leading : Body.ElaboratesPrefix chainBlock [("outerMark", starlark%[[17]])] [("outerMark", boxed 17)] [] :=
    .cons (by decide) (.list (.int 17)) .nil
  simpa [chainSource, chainCode, relayCallSite, Site.statement, Site.sourceSignature, Site.block, parameterNames, callRelayBlock,
    Parameters.names, Array.size_push] using
    (Call.Suite.Elaborates.assignments leading
      (.call (relayCallSite mode seed) (by change "relay".toList.head? ≠ some '$'; decide)
        chainAssignment (callProfile mode seed) (.plain (.straight ending))))

-- The same source proof covers the two reached calls under different
-- available sets as well as the failure cases in the inner suite.
example (mode : CallCase) (seed : Program) {cmds : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve cmds linked = .ok resolved)
    (table : PreservesDeclarations ((seed.push callLeafSite.declaration).push (relayCallSite mode seed).declaration)
      resolved.program)
    (available : List Nat) (guarded : List.Subset [seed.size + 1, seed.size] available)
    {free : List FreeName} (selected : Selects chainBlock (chainCode mode seed).reads free)
    (state : Lists.State) (floor : Nat) (frame : Body.Frame chainBlock free floor state) :
    ∃ out, Call.Suite.Runs chainBlock state (chainSource mode) (chainCode mode seed).code out ∧
      Functions.denoteBody resolved.program available (chainCode mode seed).code state = out := by
  have selection : Selects chainBlock ([] ++ (chainCode mode seed).reads ++ []) free := by simpa using selected
  obtain ⟨out, trace, _, _, _, denoted⟩ :=
    Call.Suite.runs (chainProfile mode seed) checked table available guarded selection state frame
  exact ⟨out, trace, denoted⟩

private def callCommands (mode : CallCase) (index : Int := 1) : List Command :=
  let factory := Command.define "factory" (.required ["x", "index"]) (chainSource mode)
  [noise, .assign "values" starlark%[[11,22]], factory,
   .assign "result" (.call starlark%[factory] [starlark%[values], .scalar (.int index)] [] none none),
   .assign "finished" starlark%[[99]]]

-- The factory calls the relay, which calls the leaf through its local
-- copy. The leaf uses the relay's inherited cell addresses.
#guard
  match runModule (callCommands .defaults) (fun _ => none) {} with
  | .ok (.ok published final) =>
    let captures (id : Nat) := final.heap.toList.findSome? fun cell =>
      match cell.contents with
      | .function closure => if closure.declaration == id then some closure.captures else none
      | _ => none
    published.exports.lookup "result" == some (.scalar (.int 22)) &&
    (final.heap.filter (fun cell => cell.contents == .list [.scalar (.int 22)])).size == 2 &&
    (match captures 2, captures 1 with
    | some [x, index], some [index', x'] =>
      x == x' && index == index' &&
      final.heap[index.address]? == some ⟨.binding (some (.scalar (.int 1))), false⟩
    | _, _ => false)
  | _ => false

private def outerTailUnreached (heap : Array Lists.Cell) : Bool :=
  match heap.toList.findIdx? (fun cell =>
    match cell.contents with
    | .function closure => closure.declaration == 3
    | _ => false) with
  | some factory =>
    heap[factory + 6]? == some ⟨.binding none, false⟩ &&
    heap[factory + 7]? == some ⟨.binding none, false⟩ &&
    heap[factory + 8]? == some ⟨.list [.scalar (.int 17)], false⟩
  | none => false

private def stoppedBeforeActivation (mode : CallCase) (error : Lists.Error) (last : Int) : Bool :=
  let cmds := callCommands mode
  let caller : Lists.State := { iterators := [123] }
  match resolve cmds, runModule cmds (fun _ => none) caller with
  | .ok resolved, .ok (.error (.runtime reached) final) =>
    let entered := enter resolved.source caller
    let moduleCell name := (entered.slots (globalSlot name)).bind (fun slot => final.heap[slot.address]?)
    reached == error && outerTailUnreached final.heap &&
    (match final.heap[final.heap.size - 3]? with
    | some ⟨.function closure, false⟩ => closure.declaration == 1
    | _ => false) &&
    final.heap[final.heap.size - 2]? == some ⟨.list [.scalar (.int 73)], false⟩ &&
    final.heap[final.heap.size - 4]? == some ⟨.binding none, false⟩ &&
    final.heap[final.heap.size - 5]? == some ⟨.binding none, false⟩ &&
    final.heap.back? == some ⟨.list [.scalar (.int last)], false⟩ &&
    moduleCell "result" == some ⟨.binding none, false⟩ &&
    moduleCell "finished" == some ⟨.binding none, false⟩ &&
    (final.slots (globalSlot "factory")).isNone && final.iterators == [123]
  | _, _ => false

#guard stoppedBeforeActivation .operandError (.indexRange 1 1) 0
#guard stoppedBeforeActivation .arityError (.arity 1 2) 74

-- This time the leaf activates and allocates before its return operand
-- fails. Both callers retain that allocation and skip their destinations.
#guard
  let cmds := callCommands .defaults 3
  let caller : Lists.State := { iterators := [123] }
  match resolve cmds, runModule cmds (fun _ => none) caller with
  | .ok resolved, .ok (.error (.runtime (.indexRange 3 2)) final) =>
    let entered := enter resolved.source caller
    let moduleCell name := (entered.slots (globalSlot name)).bind (fun slot => final.heap[slot.address]?)
    let retained :=
      match moduleCell "values", final.heap.back? with
      | some ⟨.binding (some (.list values)), false⟩, some ⟨.list [.list saved], false⟩ => saved == values
      | _, _ => false
    let relayTailUnreached :=
      match final.heap.toList.findIdx? (fun cell =>
        match cell.contents with
        | .function closure => closure.declaration == 1
        | _ => false) with
      | some leaf =>
        final.heap[leaf - 2]? == some ⟨.binding none, false⟩ &&
        final.heap[leaf - 1]? == some ⟨.binding none, false⟩
      | none => false
    retained && relayTailUnreached && outerTailUnreached final.heap &&
    moduleCell "result" == some ⟨.binding none, false⟩ &&
    moduleCell "finished" == some ⟨.binding none, false⟩ &&
    (final.slots (globalSlot "factory")).isNone && final.iterators == [123]
  | _, _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive
