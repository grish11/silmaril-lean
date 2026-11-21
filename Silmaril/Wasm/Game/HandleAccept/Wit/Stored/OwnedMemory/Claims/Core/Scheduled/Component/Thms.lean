module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Thms
import Silmaril.Wasm.Component.Reference.HostWrite.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.AsyncRef Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory (Tree)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims (State)
open Silmaril.Wasm.Component.Value

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

/-- Refusing before payload lift preserves component authorities, even if writing the
error result traps. It does not undo earlier effects or forbid result/subtask updates. -/
theorem refusal_frame (ticket : Nat) (caller : CallerId) (issue : Issue) (before : CStore (core3 grow)) :
    P.InvW (SameAuthority before) (fun _ => True)
      (refuseBeforeLift (grow := grow) (sig := sig) ticket caller issue) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.refusal_frame
    ticket caller issue before

/-- Given the same guarded caller record, the checked error and reference resolution
have identical continuations after the store read, including the indirect write and traps. -/
theorem resolve_error_agrees (ticket : Nat) (caller : CallerId) (snapshot : CStore (core3 grow))
    (subtask : SubtaskId) (cx : LiftLowerContext (core3 grow)) (args : List FlatValue) (pos : Nat)
    (ft : WIT.FuncType Empty RtId) (limits results : Nat)
    (record : ArenaField.callers.get? snapshot caller = some (.lower subtask cx args pos ft limits results))
    (type : ft.result = some resultType) (mode : results ≤ 1) :
    ∃ checked reference : CStore (core3 grow) → Session grow sig (Ret (core3 grow)),
      resolveError ticket caller = .op (S := Eff (core3 grow) (HostState sig)) .get checked ∧
      (do
        lowerOnResolve Limits.spec Quirks.none caller (some [.variant 1 none])
        pure (Ret.cancel (E := core3 grow) .none)) = .op (S := Eff (core3 grow) (HostState sig)) .get reference ∧
      checked snapshot = reference snapshot :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.resolve_error_agrees
    ticket caller snapshot subtask cx args pos ft limits results record type mode

/-- Registration before canonical result lowering is only a preview. At this step,
the reference program receives the candidate handle, and the writer is unchanged. -/
theorem resolve_begin {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ticket : Nat) (caller : CallerId) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer) (room : writer.accepted.length < 2 ^ 32)
    (pending : config.ctl = ⟨thread, .prog (resolveTree ticket caller tree), segments⟩ :: rest) :
    Step prof ready dispatch config .tau
      { config with ctl := ⟨thread, .prog (do
          lowerOnResolve Limits.spec Quirks.none caller (some [.variant 0 (some (Val.u32 writer.accepted.length))])
          completeResolvedTree ticket tree writer.accepted.length), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.resolve_begin
    ticket caller tree writer registered room pending

/-- Once the canonical result program returns, valid live registration with the checked
handle commits the root. This branch publishes before it records
the reply; completion does not overwrite or roll back the reached reference store. -/
theorem complete_commit {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer)
    (expected : handle = writer.accepted.length) (room : handle < 2 ^ 32)
    (pending : config.ctl = ⟨thread, .prog (completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau]
      { config with
        host := (({ config.host with writer } : HostState sig).record (.published ticket handle)).record
          (.returned ticket handle)
        ctl := ⟨thread, .prog (.pure (.cancel .none)), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.complete_commit
    ticket handle tree writer registered expected room pending

/-- If live registration instead predicts a different handle, record a typed
diagnostic and lock down the reached store without publishing or replying. -/
theorem complete_stale {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer) (stale : handle ≠ writer.accepted.length)
    (pending : config.ctl = ⟨thread, .prog (completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .trap (.hostTrap "invalid mixed acceptor import binding")]
      (StepDefs.trapCfg
        { config with host := config.host.record (.bindingTrap ticket .wrongResultType) }) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.complete_stale
    ticket handle tree writer registered stale pending

/-- The success path reads the reached caller record, using its actual length limit,
context and result cursor. If lowering traps, neither resolution nor publication runs. -/
theorem resolve_caller {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ticket handle : Nat) (caller : CallerId) (tree : Tree sig)
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
        completeResolvedTree ticket tree handle), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.resolve_caller
    ticket handle caller tree subtask cx args pos ft params results callerRecord pending

/-- Exact reference program for the indirect acceptor reply, in either memory width.
The typed cursor, alignment and full eight-byte range checks precede any write. The
error writes only its discriminant; success also writes the handle at offset four. -/
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
      return []) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.lower_result_program
    cx cursor maxResults indirect reply

theorem result_payload_offset (out : Nat) (aligned : out = ABI.alignTo out .four) :
    ABI.alignTo (ABI.alignTo out .four + 1) .four = out + 4 :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.result_payload_offset out aligned

/-- From the canonical tail after the result write, resolution and publication retain
the same subtask's index, lends and pending event. This does not deliver the event. -/
theorem resolve_commit {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
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
      final.store.subtask? subtask = some { record with state := .returned, flatResults := flat } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.resolve_commit
    ticket handle tree writer subtask flat record live registered expected room pending

/-- Delivery requires the actual queued event and an executing waitable continuation.
It clears the event, applies the reference lend release, and returns the recorded index. -/
theorem deliver_pending {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (subtask : SubtaskId) (record : Subtask) (index : Nat)
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
        ctl := ⟨thread, .prog (resume ⟨.subtask, index, SubtaskState.returned.toNat⟩), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.deliver_pending
    subtask record index live returned indexed eventPending resume pending

theorem host_checked (bindings : List (Binding sig)) (callees : List (Callee sig)) :
    HostImplSafe CheckedWrite (hostWithComponent (grow := grow) bindings callees) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.hostWithComponent_safe
    bindings callees

/-- The dispatcher conserves published roots, authority, and tickets across arbitrary
machine prefixes with checked initial continuations and checked host-frame programs.
The theorem includes typed refusals and canonical traps, not just successful returns. -/
theorem checked_of_steps (bindings : List (Binding sig)) (callees : List (Callee sig))
    {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (hostWithComponent bindings callees)) initial labels final)
    (safe : CfgSafe CheckedWrite initial) (runSafe : RunSafe CheckedWrite labels) :
    Extends initial.host final.host ∧ WriterRun initial.host.writer final.host.writer ∧
      PublicationDelta initial.host final.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.checked_of_component_steps
    bindings callees steps safe runSafe

/-- Arbitrary exports and internal scheduling from an ordinary session need no hypotheses
on the guest or its export sequence. Only injected raw programs need a write-policy proof. -/
theorem checked_of_session (bindings : List (Binding sig)) (callees : List (Callee sig))
    {prof : ProfileKind} {ready : HostReady (HostState sig)} (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (hostWithComponent bindings callees))
      (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels) :
    Extends state final.host ∧ WriterRun state.writer final.host.writer ∧ PublicationDelta state final.host :=
  checked_of_steps bindings callees steps (Component.Reference.HostWrite.cfgSafe_init _ _)
    (fun program member => (ordinary program member).elim)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall
