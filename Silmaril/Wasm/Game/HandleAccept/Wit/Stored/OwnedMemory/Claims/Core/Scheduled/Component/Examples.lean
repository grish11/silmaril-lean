module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Deferred.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Publication.Defs
import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
meta import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Defs
meta import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Deferred.Defs
meta import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Publication.Defs
meta import Silmaril.Wasm.Component.Reference.Machine.Exec.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Examples

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.AsyncRef
  Silmaril.Wasm.Execution.Core

public abbrev grow := SingleThreaded.neverFail
public abbrev engine := core3 grow
private def resource : RtId := ⟨0⟩
private def eventMemory : engine.MemAddr := (0 : Nat)

private def signature (spill : Bool) (storedBorrow : Bool := false) : Signature :=
  ⟨Unit, fun _ => .tuple ([.own resource, .own resource] ++
    (if spill then [.fixedList (.prim .u32) 13] else []) ++
    (if storedBorrow then [.option (.borrow resource)] else [])), fun _ => .star⟩

private def callee (spill async_ : Bool) (storedBorrow : Bool := false) : Callee (signature spill storedBorrow) :=
  ⟨"accept", ⟨0⟩, ⟨0⟩, 0, .i32, .utf8, async_, ()⟩

private def indexOf {kind : IndexKind} (index : Nat) : Idx kind := ⟨Fin.ofNat _ index⟩
private def word (value : Nat) : Instr := .intConst .i32 (BitVec.ofNat 32 value)
private def storeWord (ptr : Nat) (value : Instr) : List Instr :=
  [word ptr, value, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩]

private def instantiate (spill async_ storedBorrow : Bool) (deferred : Bool := false) :
    Option (Store (CanonHost engine) × ModuleInst) := do
  let c := callee spill async_ storedBorrow
  let newType : V1.FuncType := ⟨[.int .i32], [.int .i32]⟩
  let wrapperType : V1.FuncType := ⟨List.replicate 4 (.int .i32), c.coreType.results⟩
  let (store, newAddr) := SingleThreaded.allocHost ({} : Store (CanonHost engine)) newType
    (.builtin (.resourceNew resource .i32) ⟨0⟩)
  let (store, acceptAddr) := SingleThreaded.allocHost store c.coreType (c.lowered ⟨0⟩)
  let dropType : V1.FuncType := ⟨[.int .i32], []⟩
  let controls : List (String × V1.FuncType × CanonHost engine) := if deferred then
    [ ("start", Deferred.startType, .embedder "start" Deferred.startType)
    , ("cancel", newType, .builtin (.subtaskCancel true) ⟨0⟩)
    , ("drop", dropType, .builtin .subtaskDrop ⟨0⟩)
    , ("new-set", ⟨[], [.int .i32]⟩, .builtin .waitableSetNew ⟨0⟩)
    , ("join", ⟨[.int .i32, .int .i32], []⟩, .builtin .waitableJoin ⟨0⟩)
    , ("poll", ⟨[.int .i32, .int .i32], [.int .i32]⟩, .builtin (.waitableSetPoll eventMemory) ⟨0⟩)
    , ("drop-set", dropType, .builtin .waitableSetDrop ⟨0⟩) ] else []
  let (store, controlAddrs) := controls.foldl (fun (store, addrs) (_, type, host) =>
    let (store, addr) := SingleThreaded.allocHost store type host
    (store, addrs ++ [.func addr])) (store, [])
  let controlTypes := controls.map fun (_, type, _) => type.toCoreRec
  let controlImports := controls.zipIdx |>.map fun ((name, _, _), index) =>
    (⟨"host", name, .func (indexOf (3 + index))⟩ : Import)
  let controlExports := controls.zipIdx |>.map fun ((name, _, _), index) =>
    (⟨name, .func (indexOf (2 + index))⟩ : Export)
  let wrapperIndex := 2 + controls.length
  let localValue := fun index => Instr.localGet (indexOf index)
  let body := storeWord 100 (word 1) ++ (if spill then
    storeWord 16 (word 100) ++ storeWord 20 (localValue 0) ++
      storeWord 24 (localValue 1) ++ storeWord 28 (localValue 2) ++ [word 16]
    else [word 100, localValue 0, localValue 1, localValue 2]) ++
      [localValue 3, .call (indexOf 1)]
  let module_ : Module := {
    types := [newType.toCoreRec, c.coreType.toCoreRec, wrapperType.toCoreRec] ++ controlTypes
    imports := [⟨"host", "new-own", .func (indexOf 0)⟩, ⟨"host", "accept", .func (indexOf 1)⟩] ++ controlImports
    memories := [⟨.i32, ⟨1, none⟩⟩]
    funcs := [⟨indexOf 0, [], [localValue 0, .call (indexOf 0)]⟩, ⟨indexOf 2, [], body⟩]
    exports := [⟨"new-own", .func (indexOf wrapperIndex)⟩,
      ⟨"accept", .func (indexOf (wrapperIndex + 1))⟩] ++ controlExports }
  let (store, inst, none) ← Core3.prepareE? store module_ ([.func newAddr, .func acceptAddr] ++ controlAddrs) | none
  return (store, inst)

private def exportAddr (inst : ModuleInst) (name : String) : Option engine.FuncAddr := do
  let (_, .func address) ← (Core3.instExports inst).find? (·.1 == name) | none
  return address

private inductive Scenario where
  | retry
  | one (second out : Nat)

private def program (spill async_ storedBorrow : Bool) (inst : ModuleInst) (scenario : Scenario) :
    Session grow (signature spill storedBorrow) (Ret engine) := do
  let some newOwn := exportAddr inst "new-own" | internal "missing new-own export"
  let some accept := exportAddr inst "accept" | internal "missing accept export"
  let newResource := fun slot => do
    trapIf ((← callCore newOwn [i32Flat 77]) != [i32Flat slot]) (.internal "unexpected owner slot")
  let expected := if async_ then [i32Flat AsyncRef.AsyncLowerResult.returned.pack] else []
  let acceptNode := fun count first second out => do
    trapIf ((← callCore accept ([count, first, second, out].map i32Flat)) != expected)
      (.internal "unexpected canonical accept result")
  newResource 1
  newResource 2
  match scenario with
  | .one second out => acceptNode 0 1 second out
  | .retry =>
    acceptNode 1 1 2 128
    acceptNode 0 1 2 136
    newResource 2
    newResource 1
    acceptNode 1 2 1 144
  return .unit

private def config (spill async_ : Bool) (storedBorrow : Bool := false) (scenario : Scenario := .retry) :
    Option (Machine.Config engine (HostState (signature spill storedBorrow))) := do
  let (core, inst) ← instantiate spill async_ storedBorrow
  let store : CStore engine := { CStore.empty with
    core, insts := [{}], resourceTypes := [{ impl := some ⟨0⟩ }],
    funcs := [.host (callee spill async_ storedBorrow).funcType ⟨0⟩]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  return {
    store, host := {}, conts := [none]
    ctl := [Machine.Activation.ofProg (some ⟨0⟩) (program spill async_ storedBorrow inst scenario)] }

private def ready {spill storedBorrow : Bool} : HostReady (HostState (signature spill storedBorrow)) := fun _ _ => false

private def dispatch (spill async_ : Bool) := specDispatch ready
  (hostWithComponent (grow := grow) [] [callee spill async_])

private def run (spill async_ : Bool) (start : Machine.Config engine (HostState (signature spill))) :=
  Machine.run ready (dispatch spill async_) (core3Exec grow) Machine.Oracle.first 1700 start

theorem replay_sound (spill async_ : Bool) (start : Machine.Config engine (HostState (signature spill))) :
    Machine.Steps .deterministic ready (dispatch spill async_) start
      (run spill async_ start).labels (run spill async_ start).config :=
  Machine.run_sound ready (dispatch spill async_) (core3Exec grow) Machine.Oracle.first 1700 start

private def regression (spill async_ : Bool) : Bool :=
  match config spill async_ with
  | none => false
  | some start =>
    let result := run spill async_ start
    let state := result.config.host
    let summaries := state.writer.accepted.map fun tree => (rootReceipts tree).map fun r => (receiptId r).idx
    let journaled := (state.publicationRootsFrom 0).map (Option.map fun tree =>
      (rootReceipts tree).map fun receipt => (receiptId receipt).idx)
    result.outcome == .resolved && state.publications == [(1, 1), (2, 2)] &&
    state.refusals == [.accept (.boundary (.invalidChild 1))] && summaries == [[2, 3], [0, 1]] &&
    journaled == [some [0, 1], some [2, 3]] &&
    (result.config.store.core.mems[0]?.map fun mem => (mem.bytes.extract 128 152).data) ==
      some #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]

#guard regression false false
#guard regression false true
#guard regression true false
#guard regression true true

private def ownerSlots (store : CStore engine) : Option (Option HandleEntry × Option HandleEntry) :=
  (store.insts.get? 0).map fun inst => (inst.handles.get? 1, inst.handles.get? 2)

private def rejectedSchema (out : Nat) (resultTraps : Bool) : Bool :=
  match config true true true (.one 2 out) with
  | none => false
  | some start =>
    let result := Machine.run ready (specDispatch ready (hostWithComponent [] [callee true true true]))
      (core3Exec grow) Machine.Oracle.first 900 start
    result.config.host.publications.isEmpty && result.config.host.writer.accepted.isEmpty &&
      result.config.host.refusals == [.accept (.claims (.lift (.schema .storedBorrow)))] &&
      ownerSlots result.config.store == some (some (.resource ⟨0⟩), some (.resource ⟨1⟩)) &&
      (if resultTraps then
        result.outcome == .trap && result.labels.any (fun label => match label with
          | .trap .outOfBounds => true
          | _ => false)
      else result.outcome == .resolved && result.config.store.core.mems[0]?.bind (·.bytes.data[out]?) == some 1)

private def rejectedMemoryWidth : Bool :=
  match config false false false (.one 2 128) with
  | none => false
  | some start =>
    let wrong := { callee false false with width := .i64 }
    let result := Machine.run ready (specDispatch ready (hostWithComponent [] [wrong]))
      (core3Exec grow) Machine.Oracle.first 900 start
    result.outcome == .trap && result.config.host.publications.isEmpty &&
      result.config.host.refusals == [.badLoweringMemory] &&
      ownerSlots result.config.store == some (some (.resource ⟨0⟩), some (.resource ⟨1⟩))

private def canonicalTrap (second out : Nat) (reason : TrapReason)
    (slots : Option HandleEntry × Option HandleEntry) : Bool :=
  match config false false false (.one second out) with
  | none => false
  | some start =>
    let result := run false false start
    result.outcome == .trap && result.config.host.publications.isEmpty &&
      result.config.host.writer.accepted.isEmpty && result.config.host.refusals.isEmpty &&
      result.labels.any (fun label => match label with | .trap actual => actual == reason | _ => false) &&
      ownerSlots result.config.store == some slots

#guard rejectedSchema 128 false
#guard rejectedSchema 65536 true
#guard rejectedMemoryWidth
#guard canonicalTrap 1 128 (.unknownHandle 1) (none, some (.resource ⟨1⟩))
#guard canonicalTrap 2 65536 .outOfBounds (none, none)
#guard canonicalTrap 2 129 .unalignedPointer (none, none)

private def deferredProgram (spill stale : Bool) (pollOut : Option Nat) (inst : ModuleInst) :
    Session grow (signature spill) (Ret engine) := do
  let check := fun name args expected => do
    let some address := exportAddr inst name | internal "missing deferred replay export"
    let reply ← callCore address (args.map i32Flat)
    trapIf (reply != expected.map i32Flat) (.internal s!"unexpected deferred reply: {name}")
  let pending := AsyncRef.AsyncLowerResult.pending .starting 3 |>.pack
  check "new-own" [77] [1]
  check "new-own" [77] [2]
  check "accept" [0, 1, 2, 128] [pending]
  check "cancel" [3] [AsyncRef.subtaskCancelResult (some .cancelledBeforeStarted)]
  check "drop" [3] []
  check "accept" [0, 1, 2, 136] [pending]
  if pollOut.isSome then
    check "new-set" [] [4]
    check "join" [3, 4] []
    check "poll" [4, 160] [EventCode.none.toNat]
  check "start" [3] [0]
  if let some out := pollOut then
    let state ← hostGet
    trapIf (state.publications != [(1, 1)]) (.internal "result not published before poll")
    check "poll" [4, out] [EventCode.subtask.toNat]
    let cx : LiftLowerContext engine := { inst := ⟨0⟩, opts := { memory := some eventMemory } }
    trapIf ((← readMem cx out 8).data != #[3, 0, 0, 0, 2, 0, 0, 0])
      (.internal "unexpected delivered subtask")
    check "poll" [4, 168] [EventCode.none.toNat]
    check "join" [3, 0] []
    check "drop-set" [4] []
  else check "cancel" [3] [AsyncRef.subtaskCancelResult (some .returned)]
  check "drop" [3] []
  if stale then check "start" [3] [0]
  return .unit

private def deferredConfig (spill stale : Bool) (pollOut : Option Nat := none) :
    Option (Machine.Config engine (HostState (signature spill))) := do
  let (core, inst) ← instantiate spill true false true
  let store : CStore engine := { CStore.empty with
    core, insts := [{}], resourceTypes := [{ impl := some ⟨0⟩ }],
    funcs := [.host (callee spill true).funcType ⟨0⟩],
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }],
    threads := [{ status := .running, task := ⟨0⟩ }] }
  return {
    store, host := {}, conts := [none]
    ctl := [Machine.Activation.ofProg (some ⟨0⟩) (deferredProgram spill stale pollOut inst)] }

private def deferredDispatch (spill : Bool) := specDispatch ready
  (Deferred.hostWithDeferred (grow := grow) [] [callee spill true] [⟨0⟩] "start")

private def runDeferred (spill : Bool) (start : Machine.Config engine (HostState (signature spill))) :=
  Machine.run ready (deferredDispatch spill) (core3Exec grow) Machine.Oracle.first 1800 start

theorem deferred_replay_sound (spill : Bool) (start : Machine.Config engine (HostState (signature spill))) :
    Machine.Steps .deterministic ready (deferredDispatch spill) start
      (runDeferred spill start).labels (runDeferred spill start).config :=
  Machine.run_sound ready (deferredDispatch spill) (core3Exec grow) Machine.Oracle.first 1800 start

private def deferredRegression (spill stale : Bool) (pollOut : Option Nat := none) : Bool :=
  match deferredConfig spill stale pollOut with
  | none => false
  | some start =>
    let result := runDeferred spill start
    let state := result.config.host
    let summary := (state.publicationRootsFrom 0).map (Option.map fun root =>
      (rootReceipts root).map fun receipt => ((receiptId receipt).idx, receipt.2.representation))
    let pollTraps := pollOut == some 65536
    let store := result.config.store
    result.outcome == (if stale || pollTraps then .trap else .resolved) &&
      (!pollTraps || (result.labels.any (fun label => match label with | .trap .outOfBounds => true | _ => false) &&
        store.subtaskResolveDelivered ⟨1⟩ && !store.waitableHasEvent (.subtask ⟨1⟩))) &&
      state.refusals == (if stale then [.stalePendingAccept] else []) &&
      state.publications == [(1, 1)] && state.writer.accepted.length == 1 &&
      state.pendingAccepts.isEmpty && summary == [some [(0, 77), (1, 77)]] &&
      state.transcript.filter (fun event => match event with | .queued _ | .cancelled _ => true | _ => false) ==
        [.queued 0, .cancelled 0, .queued 1] &&
      (result.config.store.core.mems[0]?.map fun mem => (mem.bytes.extract 128 144).data) ==
        some #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]

#guard deferredRegression false false
#guard deferredRegression true true
#guard deferredRegression false false (some 160)
#guard deferredRegression true false (some 160)
#guard deferredRegression true false (some 65536)

private def rejectedSyncDefer : Bool :=
  match config false false false (.one 2 128) with
  | none => false
  | some start =>
    let host := Deferred.hostWithDeferred [] [callee false false] [⟨0⟩] "start"
    let result := Machine.run ready (specDispatch ready host) (core3Exec grow) Machine.Oracle.first 900 start
    result.outcome == .trap && result.config.host.publications.isEmpty &&
      result.config.host.pendingAccepts.isEmpty && result.config.host.refusals == [.wrongPassingMode] &&
      ownerSlots result.config.store == some (some (.resource ⟨0⟩), some (.resource ⟨1⟩))

#guard rejectedSyncDefer

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Examples
