module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Value Silmaril.Wasm.Component.AsyncRef Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory (Tree)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims (State)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall

variable {sig : Signature} {grow : SingleThreaded.GrowOracle} {prof : ProfileKind}
  {ready : HostReady (HostState sig)} {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
  {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId}
  {segments : List (Seg (core3 grow) (HostState sig))} {rest : List (Activation (core3 grow) (HostState sig))}

theorem resolve_begin (ticket : Nat) (caller : CallerId) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer) (room : writer.accepted.length < 2 ^ 32)
    (pending : config.ctl = ⟨thread, .prog (resolveTree ticket caller tree), segments⟩ :: rest) :
    Machine.Step prof ready dispatch config .tau
      { config with ctl := ⟨thread, .prog (do
          lowerOnResolve Limits.spec Quirks.none caller (some [.variant 0 (some (Val.u32 writer.accepted.length))])
          completeResolvedTree ticket tree writer.accepted.length), segments⟩ :: rest } := by
  have step := Step.hostGet (prof := prof) (hr := ready) (dispatch := dispatch) pending
  simp only [Prog.bind, registered, Nat.not_le.mpr room, ite_false] at step
  exact step

private theorem complete_read (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer)
    (pending : config.ctl = ⟨thread, .prog (completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Machine.Step prof ready dispatch config .tau
      { config with ctl := ⟨thread, .prog (do
          let result ← (do
            if handle != writer.accepted.length then return .error .wrongResultType
            if writer.accepted.length ≥ 2 ^ 32 then return .error (.accept (.boundary .exhaustedHandles))
            hostSet (({ config.host with writer } : HostState sig).record (.published ticket writer.accepted.length))
            return .ok writer.accepted.length : Session grow sig (Except Issue Nat))
          match result with
          | .error issue => reject ticket issue
          | .ok published => do
            let _ ← writeCompletion (.returned ticket published, [])
            return .cancel .none), segments⟩ :: rest } := by
  have step := Step.hostGet (prof := prof) (hr := ready) (dispatch := dispatch) pending
  simp only [Prog.bind, registered, Option.any] at step
  exact step

theorem complete_commit (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer)
    (expected : handle = writer.accepted.length) (room : handle < 2 ^ 32)
    (pending : config.ctl = ⟨thread, .prog (completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau]
      { config with
        host := (({ config.host with writer } : HostState sig).record (.published ticket handle)).record
          (.returned ticket handle)
        ctl := ⟨thread, .prog (.pure (.cancel .none)), segments⟩ :: rest } := by
  subst handle
  refine .cons (complete_read ticket writer.accepted.length tree writer registered pending) ?_
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, Nat.not_le.mpr room]
  exact .cons (.hostSet rfl) (.cons (.hostGet rfl) (.cons (.hostSet rfl) (.refl _)))

theorem complete_stale (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer) (stale : handle ≠ writer.accepted.length)
    (pending : config.ctl = ⟨thread, .prog (completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .trap (.hostTrap "invalid mixed acceptor import binding")]
      (StepDefs.trapCfg
        { config with host := config.host.record (.bindingTrap ticket .wrongResultType) }) := by
  refine .cons (complete_read ticket handle tree writer registered pending) ?_
  simp only [bne_iff_ne.mpr stale, ite_true]
  exact .cons (.hostGet rfl) (.cons (.hostSet rfl) (.cons (.trap rfl) (.refl _)))

theorem resolve_caller (ticket handle : Nat) (caller : CallerId) (tree : Tree sig)
    (subtask : SubtaskId) (cx : LiftLowerContext (core3 grow)) (args : List FlatValue)
    (pos : Nat) (ft : WIT.FuncType Empty RtId) (params results : Nat)
    (callerRecord : ArenaField.callers.get? config.store caller =
      some (.lower subtask cx args pos ft params results))
    (pending : config.ctl = ⟨thread, .prog (do
      lowerOnResolve Limits.spec Quirks.none caller (some [.variant 0 (some (Val.u32 handle))])
      completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Step prof ready dispatch config .tau
      { config with ctl := ⟨thread, .prog (do
        maybeOnProgress subtask
        let flat ← lowerFlatValues Limits.spec Quirks.none cx results [.variant 0 (some (Val.u32 handle))]
          ft.result.toList (some ⟨args, pos⟩)
        Subtask.resolve subtask .returned flat
        completeResolvedTree ticket tree handle), segments⟩ :: rest } := by
  have step := Step.get (prof := prof) (hr := ready) (dispatch := dispatch) pending
  simpa [Prog.bind, callerRecord, Quirks.none, Prog.bind_assoc] using step

theorem resolve_commit (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
    (subtask : SubtaskId) (flat : List FlatValue) (record : Subtask)
    (live : config.store.subtask? subtask = some record)
    (registered : config.host.writer.register tree = .ok writer)
    (expected : handle = writer.accepted.length) (room : handle < 2 ^ 32)
    (pending : config.ctl = ⟨thread, .prog (do
      Subtask.resolve subtask .returned flat
      completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    let final : Config (core3 grow) (HostState sig) :=
      { config with
        store := config.store.subtaskResolveSt subtask .returned flat
        host := (({ config.host with writer } : HostState sig).record (.published ticket handle)).record
          (.returned ticket handle)
        ctl := ⟨thread, .prog (.pure (.cancel .none)), segments⟩ :: rest }
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau, .tau] final ∧
      final.store.subtask? subtask = some { record with state := .returned, flatResults := flat } := by
  refine ⟨.cons (.modify pending) (complete_commit ticket handle tree writer registered expected room rfl), ?_⟩
  change ArenaField.subtasks.get? _ _ = _
  rw [CStore.subtaskResolveSt, ArenaField.get?_modify_self]
  rw [CStore.subtask?] at live
  simp [live]

private theorem take_returned {store : CStore (core3 grow)} (subtask : SubtaskId)
    (record : Subtask) (index : Nat) (live : store.subtask? subtask = some record)
    (returned : record.state = .returned) (indexed : record.index = some index)
    (pending : record.common.pending = some (.subtask subtask)) :
    store.takeWaitableEvent (.subtask subtask) =
      ((store.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none })
        |>.deliverResolveSt subtask, some ⟨.subtask, index, SubtaskState.returned.toNat⟩) := by
  have cleared : (store.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none }).subtask? subtask =
      some { record with common := { record.common with pending := none } } := by
    change ArenaField.subtasks.get? _ _ = _
    rw [CStore.modifyWaitableCommon, ArenaField.get?_modify_self]
    rw [CStore.subtask?] at live
    simp [live]
  simp [CStore.takeWaitableEvent, live, pending, CStore.subtaskEvent, cleared, returned, indexed,
    SubtaskState.resolved]

theorem deliver_pending (subtask : SubtaskId) (record : Subtask) (index : Nat)
    (live : config.store.subtask? subtask = some record)
    (returned : record.state = .returned) (indexed : record.index = some index)
    (eventPending : record.common.pending = some (.subtask subtask))
    (resume : EventTuple → Session grow sig (Ret (core3 grow)))
    (pending : config.ctl = ⟨thread, .prog (Waitable.getPendingEvent (.subtask subtask) >>= resume),
      segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        store := (config.store.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none })
          |>.deliverResolveSt subtask
        ctl := ⟨thread, .prog (resume ⟨.subtask, index, SubtaskState.returned.toNat⟩), segments⟩ :: rest } := by
  have read := Step.get (prof := prof) (hr := ready) (dispatch := dispatch) pending
  simp only [Prog.bind, take_returned subtask record index live returned indexed eventPending] at read
  refine .cons read (.cons (.modify rfl) ?_)
  simp only [CStore.takeWaitableEventSt, take_returned subtask record index live returned indexed eventPending]
  exact .refl _

private theorem resultLayout (width : AddrType) :
    ABI.layout width resultType = ⟨.four, 2⟩ := by
  simp only [resultType, ABI.layout, ABI.layoutOption, ABI.primitiveLayout]
  rfl

private theorem resultTupleLayout (width : AddrType) :
    ABI.layout width (.tuple [resultType]) = ⟨.four, 2⟩ := by
  simp only [ABI.layout, ABI.layoutTypes, resultLayout]
  rfl

private theorem resultPayloadAlignment (width : AddrType) :
    ABI.maxCaseAlignment [ABI.layoutOption width (some (.prim .u32 : WIT.ClosedType RtId)),
      ABI.layoutOption width (none : Option (WIT.ClosedType RtId))] = .four := by
  simp only [ABI.layoutOption, ABI.layout, ABI.primitiveLayout]
  rfl

private theorem resultFlatCount (width : AddrType) :
    (ABI.flattenTypes width [resultType]).length = 2 := by
  simp [resultType, ABI.flattenTypes, ABI.flatten, ABI.flattenOption, ABI.flattenPrimitive]

private theorem store_result (cx : LiftLowerContext (core3 grow)) (out : Nat) (reply : Option Nat) :
    (store Limits.spec Quirks.none cx (.record [reply.elim (.variant 1 none)
      (fun handle => .variant 0 (some (Val.u32 handle)))]) (.tuple [resultType]) out : Session grow sig Unit) =
    (do
      let _ ← ptrType cx
      let _ ← ptrType cx
      let field := ABI.alignTo out .four
      let _ ← match reply with
        | none => storeInt cx 1 field 1
        | some handle =>
          storeInt cx 0 field 1
          storeInt cx handle (ABI.alignTo (field + 1) .four) 4
      pure ()) := by
  cases reply <;> simp only [store, storeTuple, resultLayout] <;>
    simp [resultType, store, resultPayloadAlignment, storeVariantHead, storeOpt, storePrim, Val.u32,
      IntKind.ofPrimitive, IntKind.width, IntKind.signed, discSize, ABI.discriminantAlignment,
      ABI.Alignment.bytes, Prog.bind_assoc]

theorem lower_result_program (cx : LiftLowerContext (core3 grow)) (cursor : FlatCursor)
    (maxResults : Nat) (indirect : maxResults ≤ 1) (reply : Option Nat) :
    (lowerFlatValues Limits.spec Quirks.none cx maxResults
      [reply.elim (.variant 1 none) (fun handle => .variant 0 (some (Val.u32 handle)))]
      [resultType] (some cursor) : Session grow sig (List FlatValue)) =
    (do
      let width ← ptrType cx
      let (pointer, _) ← cursor.next (ABI.pointerType width)
      let out := flatNat pointer
      trapIf (decide (out ≠ ABI.alignTo out .four)) .unalignedPointer
      checkInBounds cx out 8
      let _ ← ptrType cx
      let _ ← ptrType cx
      let field := ABI.alignTo out .four
      let _ ← match reply with
        | none => storeInt cx 1 field 1
        | some handle =>
          storeInt cx 0 field 1
          storeInt cx handle (ABI.alignTo (field + 1) .four) 4
      return []) := by
  simp [lowerFlatValues, resultFlatCount, resultTupleLayout, show maxResults < 2 by omega,
    spillPointer, ABI.Layout.size, ABI.Alignment.bytes, store_result, Prog.bind_assoc]
  cases reply <;> simp [Prog.bind_assoc]

theorem result_payload_offset (out : Nat) (aligned : out = ABI.alignTo out .four) :
    ABI.alignTo (ABI.alignTo out .four + 1) .four = out + 4 := by
  simp only [ABI.alignTo, ABI.Alignment.bytes] at aligned ⊢
  omega

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult
