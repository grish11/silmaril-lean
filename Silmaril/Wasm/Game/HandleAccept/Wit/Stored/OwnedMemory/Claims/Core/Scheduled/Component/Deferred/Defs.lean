module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Deferred

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

/-- This control import starts an unresolved accept. Its zero result acknowledges the
callback; the original caller receives the WIT result through its canonical result area. -/
def startType : V1.FuncType := ⟨[.int .i32], [.int .i32]⟩

def HostState.queue (state : HostState sig) (entry : PendingAccept) : HostState sig :=
  { state.record (.queued entry.ticket) with pendingAccepts := entry :: state.pendingAccepts }

def HostState.take (state : HostState sig) (entry : PendingAccept) : HostState sig :=
  { state with pendingAccepts := state.pendingAccepts.filter (·.caller != entry.caller) }

/-- The slot is looked up in its owning instance every time. A host queue entry by
itself does not grant permission to resume an unpublished or recycled subtask slot. -/
def linked (entry : PendingAccept) (store : CStore (core3 grow)) (index : Nat) : Bool :=
  (store.inst? entry.inst).bind (·.handles.get? index) == some (.waitable (.subtask entry.subtask))

/-- Do not enqueue a callback that cannot be reached. Leave the canonical lower
continuation in charge of trapping `tableFull` after the host returns. -/
def refuseTableFull (ticket : Nat) : Session grow sig (Ret (core3 grow)) := do
  hostSet ((← hostGet).record (.refused ticket .subtaskTableFull))
  return .cancel .none

def stage (callee : Callee sig) (caller : CallerId) (ticket : Nat) (subtask : SubtaskId)
    (cx : LiftLowerContext (core3 grow)) (args : List FlatValue) (pos : Nat)
    (ft : WIT.FuncType Empty RtId) (limits results : Nat) : Session grow sig (Ret (core3 grow)) := do
  if !callee.async_ then return ← reject ticket .wrongPassingMode
  let store ← getStore
  if (← currentInst?) != some callee.inst then return ← reject ticket .wrongContext
  if let .error issue := callee.check store subtask cx args pos ft (limits, results) then
    return ← reject ticket issue
  let some instance_ := store.inst? callee.inst | reject ticket .wrongContext
  if let .error issue := OwnedMemory.checkSchema (sig.payload callee.tag) then
    return ← refuseBeforeLift ticket caller (.accept (.claims (.lift (.schema issue))))
  if (instance_.addHandle? (.waitable (.subtask subtask))).isNone then
    return ← refuseTableFull ticket
  let current ← hostGet
  if current.pendingAccepts.any (fun entry => entry.caller == caller || entry.subtask == subtask) then
    return ← reject ticket .stalePendingAccept
  hostSet (HostState.queue current ⟨caller, subtask, callee.hostId, callee.inst, ticket⟩)
  return .cancel (.host caller.idx)

def begin (callee : Callee sig) (caller : CallerId) : Session grow sig (Ret (core3 grow)) := do
  let record ← getObj ArenaField.callers caller
  let state ← hostGet
  let ticket := state.nextTicket
  match record with
  | .lower subtask cx args pos ft limits results =>
    hostSet (state.enter callee.name callee.coreType args)
    stage callee caller ticket subtask cx args pos ft limits results
  | _ =>
    hostSet (state.enter callee.name callee.coreType [])
    reject ticket .wrongContext

structure StartPlan (grow : SingleThreaded.GrowOracle) (sig : Signature) where
  entry : PendingAccept
  callee : Callee sig
  context : LiftLowerContext (core3 grow)
  args : List FlatValue

def planStart (callees : List (Callee sig)) (state : HostState sig) (store : CStore (core3 grow))
    (inst : InstId) (index : Nat) : Except Issue (StartPlan grow sig) := do
  let some instance_ := store.inst? inst | throw .wrongContext
  if !instance_.mayLeave then throw .wrongContext
  let .some (.waitable (.subtask subtask)) := instance_.handles.get? index
    | throw .stalePendingAccept
  let [entry] := state.pendingAccepts.filter (fun entry => entry.inst == inst && entry.subtask == subtask)
    | throw .stalePendingAccept
  let callee ← match callees.filter (fun callee => callee.hostId == entry.callee && callee.inst == inst) with
    | [callee] => pure callee
    | [] => throw .unlinkedImport
    | _ => throw .ambiguousBinding
  if !callee.async_ then throw .wrongPassingMode
  let .some (.lower actual cx args pos ft limits results) := ArenaField.callers.get? store entry.caller
    | throw .stalePendingAccept
  let some pending := store.subtask? subtask | throw .stalePendingAccept
  if actual != subtask || pending.onCancel != .host entry.caller.idx then
    throw .stalePendingAccept
  callee.check store actual cx args pos ft (limits, results) (some index)
  return ⟨entry, callee, cx, args⟩

def start (callees : List (Callee sig)) (ticket : Nat) (index : Nat) :
    Session grow sig (List FlatValue) := do
  let store ← getStore
  let inst ← currentInst?
  let state ← hostGet
  match inst with
  | none => rejectBinding ticket .wrongContext
  | some inst =>
    match planStart callees state store inst index with
    | .error issue => rejectBinding ticket issue
    | .ok plan =>
      hostSet (HostState.take state plan.entry)
      let _ ← acceptCaller plan.callee plan.entry.caller plan.entry.ticket
        state.writer.accepted store plan.context plan.args
      writeCompletion (.returned ticket 0, [i32Flat 0])

def rejectCancellation : Session grow sig Unit := do
  let state ← hostGet
  hostSet (state.enter "cancel accept" ⟨[], []⟩ [])
  let _ ← rejectBinding state.nextTicket .stalePendingAccept

def planCancel (token : Nat) (inst : Option InstId) (state : HostState sig) (store : CStore (core3 grow)) :
    Option PendingAccept := do
  let [entry] := state.pendingAccepts.filter (·.caller.idx == token) | none
  let .some (.lower subtask cx ..) := ArenaField.callers.get? store entry.caller | none
  let pending ← store.subtask? subtask
  let index ← pending.index
  if inst != some entry.inst || subtask != entry.subtask || cx.inst != entry.inst ||
      pending.inst != entry.inst || pending.onCancel != .host token ||
      pending.state != .starting || !pending.cancellationRequested || !linked entry store index then
    none
  else some entry

def cancel (token : Nat) : Session grow sig Unit := do
  let store ← getStore
  let inst ← currentInst?
  let state ← hostGet
  match planCancel token inst state store with
  | none => rejectCancellation
  | some entry =>
    lowerOnResolve Limits.spec Quirks.none entry.caller none
    hostSet ((HostState.take (← hostGet) entry).record (.cancelled entry.ticket))

def dispatchStart (bindings : List (Binding sig)) (callees : List (Callee sig)) (control : String)
    (name : String) (type : V1.FuncType) (args : List FlatValue) : Session grow sig (List FlatValue) := do
  if name != control then return ← dispatchImport bindings name type args
  let state ← hostGet
  let ticket := state.nextTicket
  hostSet (state.enter name type args)
  if bindings.any (·.name == name) then return ← rejectBinding ticket .ambiguousBinding
  if type != startType then return ← rejectBinding ticket .wrongType
  let [.int .i32 index] := args | rejectBinding ticket .wrongType
  start callees ticket index.toNat

/-- Deferred acceptance stages only the reference caller's identity. The reference
lowering owns the pending slot, progress and cancellation; payload lifting occurs at
the explicit start import, not at queue time. Other callees use eager resolution.
With no deferred callees, there is no reserved control name or cancellation override. -/
def hostWithDeferred (bindings : List (Binding sig)) (callees : List (Callee sig))
    (deferred : List HostFuncId) (control : String) : HostImpl (core3 grow) (HostState sig) :=
  let eager := hostWithComponent (grow := grow) bindings callees
  if deferred.isEmpty then eager else { eager with
    funcs := fun id caller =>
      if deferred.contains id then
        match callees.filter (·.hostId == id) with
        | [callee] => begin callee caller
        | _ => eager.funcs id caller
      else eager.funcs id caller
    embedder := dispatchStart bindings callees control
    cancel }

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Deferred
