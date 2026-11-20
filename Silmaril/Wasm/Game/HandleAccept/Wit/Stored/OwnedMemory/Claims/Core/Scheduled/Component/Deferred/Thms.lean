module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Deferred.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Thms
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Publication.Defs
import Silmaril.Wasm.Component.Reference.HostWrite.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Deferred

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Execution.Core

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

/-- With no deferred callees, every run has the original eager dispatch, including
imports using the proposed control name. This equality also preserves trap labels. -/
theorem dispatch_no_deferred (bindings : List (Binding sig)) (callees : List (Callee sig))
    (control : String) (ready : HostReady (HostState sig)) :
    specDispatch ready (hostWithDeferred (grow := grow) bindings callees [] control) =
      specDispatch ready (hostWithComponent (grow := grow) bindings callees) := rfl

/-- A capacity refusal records the current ticket without queuing, lifting payloads,
or publishing. The original continuation receives the reference cancel token. -/
theorem stage_table_full_steps {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (config : Config (core3 grow) (HostState sig)) (thread : Runtime.ThreadId)
    (segments : List (Seg (core3 grow) (HostState sig))) (rest : List (Activation (core3 grow) (HostState sig)))
    (callee : Callee sig) (caller : CallerId) (ticket : Nat) (subtask : SubtaskId)
    (cx : LiftLowerContext (core3 grow)) (args : List FlatValue) (pos : Nat)
    (ft : WIT.FuncType Empty RtId) (limits results : Nat)
    (threadInfo : Runtime.Thread) (task : Task (core3 grow)) (instance_ : InstState)
    (onThread : config.store.thread? thread = some threadInfo)
    (onTask : config.store.task? threadInfo.task = some task) (current : task.inst = callee.inst)
    (live : config.store.inst? callee.inst = some instance_)
    (async : callee.async_ = true)
    (checked : callee.check config.store subtask cx args pos ft (limits, results) = .ok ())
    (schema : OwnedMemory.checkSchema (sig.payload callee.tag) = .ok ())
    (full : instance_.addHandle? (.waitable (.subtask subtask)) = none)
    (pending : config.ctl = ⟨some thread,
      .prog (stage callee caller ticket subtask cx args pos ft limits results), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau, .tau, .tau]
      { config with
        host := config.host.record (.refused ticket .subtaskTableFull)
        ctl := ⟨some thread, .prog (.pure (.cancel .none)), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.Deferred.stage_table_full_steps
    config thread segments rest callee caller ticket subtask cx args pos ft limits results threadInfo task
    instance_ onThread onTask current live async checked schema full pending

/-- At the reference allocation boundary, fullness traps and locks down the reached
store, leaving the host journal (including the recorded refusal) untouched. -/
theorem reference_table_full_steps {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (config : Config (core3 grow) (HostState sig)) (thread : Option Runtime.ThreadId)
    (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (inst : InstId) (subtask : SubtaskId)
    (instance_ : InstState) (live : config.store.inst? inst = some instance_)
    (full : instance_.addHandle? (.waitable (.subtask subtask)) = none)
    (next : Nat → Session grow sig (Ret (core3 grow)))
    (pending : config.ctl = ⟨thread, .prog (handlesAddSubtask inst subtask >>= next), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .trap .tableFull] (StepDefs.trapCfg config) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.Deferred.reference_table_full_steps
    config thread segments rest inst subtask instance_ live full next pending

/-- Recycling a waitable slot for another nominal subtask cannot authorize the former
callback. The actual start import also reselects against the live table. -/
theorem recycled_slot (entry : PendingAccept) (store : CStore (core3 grow)) (index : Nat)
    (replacement : SubtaskId) (fresh : replacement ≠ entry.subtask)
    (slot : (store.inst? entry.inst).bind (·.handles.get? index) = some (.waitable (.subtask replacement))) :
    linked entry store index = false := by
  simp [linked, slot, fresh]

/-- Staging does not lift payloads or change authority. A later `canonLower` step, not
this host callback, installs the reference waitable entry. -/
theorem stage_frame (callee : Callee sig) (caller : CallerId) (ticket : Nat) (subtask : SubtaskId)
    (cx : LiftLowerContext (core3 grow)) (args : List FlatValue) (pos : Nat)
    (ft : WIT.FuncType Empty RtId) (limits results : Nat) (before : CStore (core3 grow)) :
    P.InvW (SameAuthority before) (fun _ => True) (stage callee caller ticket subtask cx args pos ft limits results) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.Deferred.stage_frame
    callee caller ticket subtask cx args pos ft limits results before

/-- The pending-cancel callback does not move any owner, endpoint or error context.
Waitable state and delivery are left to the reference cancellation path. -/
theorem cancel_frame (token : Nat) (before : CStore (core3 grow)) :
    P.InvW (SameAuthority before) (fun _ => True) (cancel (grow := grow) (sig := sig) token) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.Deferred.cancel_frame
    token before

theorem host_checked (bindings : List (Binding sig)) (callees : List (Callee sig))
    (deferred : List HostFuncId) (control : String) :
    HostImplSafe CheckedWrite (hostWithDeferred (grow := grow) bindings callees deferred control) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.Deferred.host_safe
    bindings callees deferred control

/-- Queuing, starting, cancelling and refusals share the checked writer and journal
invariant across ordinary export prefixes, including intermediate callbacks and traps. -/
theorem checked_of_session (bindings : List (Binding sig)) (callees : List (Callee sig))
    (deferred : List HostFuncId) (control : String) {prof : ProfileKind} {ready : HostReady (HostState sig)}
    (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (hostWithDeferred bindings callees deferred control))
      (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels) :
    Extends state final.host ∧ WriterRun state.writer final.host.writer ∧ PublicationDelta state final.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.Deferred.checked_of_steps
    bindings callees deferred control steps (Reference.HostWrite.cfgSafe_init _ _) fun program member =>
      False.elim (ordinary program member)

/-- Across arbitrary ordinary export prefixes of the linked Core session, a
newly selectable root exists exactly for a publication in that handle's journal
position. Queued, cancelled and refused calls cannot create unjournaled roots. -/
theorem fresh_lookup_iff_publication (bindings : List (Binding sig)) (callees : List (Callee sig))
    (deferred : List HostFuncId) (control : String) {prof : ProfileKind} {ready : HostReady (HostState sig)}
    (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (hostWithDeferred bindings callees deferred control))
      (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels)
    {handle : BitVec 32} (fresh : state.writer.accepted.length < handle.toNat) :
    (Endpoints.Core.childFromHistory final.host.writer.accepted handle).isSome = true ↔
      ∃ ticket, final.host.publications[state.publications.length +
        (handle.toNat - (state.writer.accepted.length + 1))]? = some (ticket, handle.toNat) :=
  (checked_of_session bindings callees deferred control store state steps ordinary).2.2.fresh_lookup_iff fresh

/-- In the linked session, fresh root selection is equivalent to a registration step
and its matching journal append along an ordinary prefix. This applies to eager and
deferred callees and does not assume delivery or restore spent claims. -/
theorem fresh_lookup_iff_cut (bindings : List (Binding sig)) (callees : List (Callee sig))
    (deferred : List HostFuncId) (control : String) {prof : ProfileKind} {ready : HostReady (HostState sig)}
    (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (hostWithDeferred bindings callees deferred control))
      (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels)
    {handle : BitVec 32} {tree : OwnedMemory.Tree sig}
    (fresh : state.writer.accepted.length < handle.toNat) :
    Endpoints.Core.childFromHistory final.host.writer.accepted handle = some tree ↔
    PublicationCut (prof := prof) (ready := ready) (dispatch := specDispatch ready (hostWithDeferred bindings callees
      deferred control)) (Config.init store state) labels final handle tree :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.publication_cut_iff
    (host_checked bindings callees deferred control) steps (Reference.HostWrite.cfgSafe_init _ _)
    (fun program member => (ordinary program member).elim) fresh

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Deferred
