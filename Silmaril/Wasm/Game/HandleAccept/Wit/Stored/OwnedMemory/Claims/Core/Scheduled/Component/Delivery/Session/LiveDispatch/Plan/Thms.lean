module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.StringPlan.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Allocation.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.RecursiveTrails
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core
open ComponentCall.Delivery.FiniteSession
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core
open Stored.Endpoints.RecordLower

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind} {ready : HostReady (HostState sig)}
  {bindings : List (Binding sig)} {base : HostImpl (core3 grow) (HostState sig)}
  {start finish incoming : Config (core3 grow) (HostState sig)} {labels : Trace grow sig}
  {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}

/-- At the reached accepted-tree read, congruence on the indexed history gives
the canonical peer of the executed checked step without equating journals. -/
theorem compareReachedAcceptedLookup (handle : BitVec 32)
    (next : Option (Stored.OwnedMemory.Tree sig) → Session grow sig (Ret (core3 grow))) {thread frames rest label}
    (focus : start.ctl = ⟨thread, .prog (select handle >>= next), frames⟩ :: rest)
    (step : Step profile ready (specDispatch ready base) start label finish)
    (paired : HostFrame.Related.Paired older start incoming)
    (indexed : start.host.writer.IndexedClaimsAgree incoming.host.writer) :
    ∃ peer, ExecutedCallbackSegment profile ready base bindings older start incoming [label] [label] finish peer ∧
      finish.host.writer.IndexedClaimsAgree peer.host.writer :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.compareReachedAcceptedLookup
    handle next focus step paired indexed

/-- The actual registration probe classifies equal alias, exhaustion or next
handle observations without requiring equal writers. -/
theorem indexedClaims_registrationProbe {left right : Stored.OwnedMemory.Claims.State sig}
    (indexed : left.IndexedClaimsAgree right) (tree : Stored.OwnedMemory.Tree sig) :
    componentRegistration left tree = componentRegistration right tree :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.indexedClaims_registrationProbe indexed tree

open Stored.OwnedMemory.Claims in
/-- The raw registration probes after an asymmetric leaf spend can still
agree: a historical owner remains a conflict, and unrelated endpoints are not
observed. This neither projects a spend onto the canonical writer nor claims
that a subsequent probe executes. -/
theorem leafSpend_registrationProbe {update : Spend} {left right checked canonical : HostState sig}
    (flow : ExclusiveLeafWriterFlow update left right checked canonical)
    (together : left.writer.IndexedClaimsAgree right.writer) (tree : Stored.OwnedMemory.Tree sig)
    (frames : update.FramesRegistration left.writer tree) :
    componentRegistration checked.writer tree = componentRegistration canonical.writer tree :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.leafSpend_registrationProbe
    flow together tree frames

/-- Compare an executed shared host read of a recursive claim plan after its store read.
Neither side commits the prospective dry-run spends. -/
theorem compareReachedRecordPrepare (plan : List Object)
    (next : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))) {thread frames rest label}
    (focus : start.ctl = ⟨thread, .prog (.op .hostGet (fun state =>
      next (Stored.OwnedMemory.Claims.Record.prepare start.store state.writer plan))), frames⟩ :: rest)
    (step : Step profile ready (specDispatch ready base) start label finish)
    (paired : HostFrame.Related.Paired older start incoming)
    (agrees : start.host.writer.LiveClaimsAgree incoming.host.writer) :
    ∃ peer, ExecutedCallbackSegment profile ready base bindings older start incoming [label] [label] finish peer ∧
      finish.host.writer.LiveClaimsAgree peer.host.writer :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.compareReachedRecordPrepare
    plan next focus step paired agrees

/-- The scheduled spend commits the identity-specific update to each reached writer.
The continuation sees separate journals and no restored claim. -/
theorem compareClaimSpend (update : Spend) (next : Session grow sig (Ret (core3 grow))) {thread frames rest}
    (focus : start.ctl = ⟨thread, .prog (claims.spend update >>= fun _ => next), frames⟩ :: rest)
    (paired : HostFrame.Related.Paired older start incoming)
    (agrees : start.host.writer.LiveClaimsAgree incoming.host.writer) :
    let after := { start with
      host := { start.host with writer := update.apply start.host.writer }
      ctl := ⟨thread, .prog next, frames⟩ :: rest }
    ∃ peer, ExecutedCallbackSegment profile ready base bindings older start incoming [.tau, .tau] [.tau, .tau] after peer ∧
      after.host.writer.LiveClaimsAgree peer.host.writer :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.compareClaimSpend
    update next focus paired agrees

/-- A synchronous readiness read under a host-independent policy needs
no hypothesis on the writer or the existence of runnable candidates. -/
theorem ClosedSyncReadyRead.fixed (policy : Nat → Bool) {task inst thread frames rest}
    (focused : start.ctl = ⟨thread, .prog (.op .hostGet (fun _ =>
      syncLiftCandidates task (start.store.instCandidates policy inst))), frames⟩ :: rest) :
    ClosedSyncReadyRead (fun _ => policy) start :=
  ⟨task, inst, thread, frames, rest, focused, LinkedCallback.ReadyAgreement.fixed policy start inst⟩

theorem ClosedSyncReadyRead.closed_host_read (read : ClosedSyncReadyRead ready start) : ClosedHostRead start :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.closedSyncRead read

/-- Close the actual scheduler read when no reached blocked candidate consults the host. The
continuation can still choose, resume a saved frame, or have no runnable candidate. -/
theorem ClosedHostRead.tick (next : List ThreadId → Session grow sig (Ret (core3 grow))) {thread frames rest}
    (focused : start.ctl = ⟨thread, .prog (.op .hostGet (fun host => next (start.store.candidates (ready host)))), frames⟩ :: rest)
    (closed : ∀ candidate ∈ start.store.waiting, ∀ entry, start.store.thread? candidate = some entry →
      entry.blocked = true → ∀ query, entry.readyCond ≠ some (.host query)) : ClosedHostRead start :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.closedTickRead next focused closed

/-- Derive the closed readiness frontier directly from the machine tick program, without asking
for a candidate or a replay continuation. The prefix stops before taking the choice. -/
theorem ClosedHostRead.reached_tick (enabled : StepDefs.HostReadyCfg start)
    (closed : let entered := StepDefs.enterHostSt start.store
      ∀ candidate ∈ entered.waiting, ∀ entry, entered.thread? candidate = some entry →
        entry.blocked = true → ∀ query, entry.readyCond ≠ some (.host query)) :
    ∃ atRead, Steps profile ready (specDispatch ready base) start [.host .tick, .tau, .tau] atRead ∧ ClosedHostRead atRead :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.reachedClosedTickRead enabled closed

/-- Started cancellation samples the reached implicit thread alone. A store-only readiness
condition makes this read closed without assuming that cancellation immediately delivers. -/
theorem ClosedHostRead.cancel (target : ThreadId) (next : Bool → Session grow sig (Ret (core3 grow))) {thread frames rest}
    (focused : start.ctl = ⟨thread, .prog (.op .hostGet (fun host => next (start.store.threadReady (ready host) target))), frames⟩ :: rest)
    (closed : ∀ entry, start.store.thread? target = some entry → entry.blocked = true →
      ∀ query, entry.readyCond ≠ some (.host query)) : ClosedHostRead start :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.closedCancelRead target next focused closed

/-- Compose two consecutive executed callback segments without imposing
equality of their journals or of their full traces. -/
theorem ExecutedCallbackSegment.append {middle peer last : Config (core3 grow) (HostState sig)}
    {checkLeading canonLeading checkTrailing canonTrailing : Trace grow sig}
    (first : ExecutedCallbackSegment profile ready base bindings older start incoming checkLeading canonLeading middle peer)
    (second : ExecutedCallbackSegment profile ready base bindings older middle peer checkTrailing canonTrailing finish last) :
    ExecutedCallbackSegment profile ready base bindings older start incoming
      (checkLeading ++ checkTrailing) (canonLeading ++ canonTrailing) finish last :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.appendExecutedCallbacks first second

/-- Derive the closed part of an actual checked callback. A reached give,
protected pop, or genuine open boundary keeps its original checked tail. -/
theorem cut_executed_callback
    (run : Steps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ExecutedCallbackCut profile ready base bindings older start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutExecutedCallback run paired

/-- Consume the reached caller read, host snapshot and entry assignment only if the actual
checked derivation executes them. Each import gets its own ticket and host snapshot. -/
theorem cut_component_lower_entry (callee : ComponentCall.Callee sig) (caller : CallerId)
    {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat}
    {cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (focused : start.ctl = cursor.control (ComponentCall.invoke callee caller))
    (record : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (run : Steps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    let entered := fun (state : Config (core3 grow) (HostState sig)) (atSite : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) =>
      { state with
        host := state.host.enter callee.name callee.coreType args
        ctl := atSite.control (ComponentCall.invokeLower callee caller state.host subtask cx args pos ft limits results) }
    (∃ peerCursor suffix, labels = [.tau, .tau, .tau] ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming [.tau, .tau, .tau] [.tau, .tau, .tau]
        (entered start cursor) (entered incoming peerCursor) ∧
      PairedComponentSite older (entered start cursor) (entered incoming peerCursor) cursor peerCursor ∧
      Steps profile ready (specDispatch ready base) (entered start cursor) suffix finish) ∨ labels.length < 3 :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutComponentLowerEntry
    callee caller focused record run paired

/-- Compare the actual entry up to each side’s own child preflight. An input
ending before the final read retains both reached endpoints and all occurrences,
even if the unreached child decisions would disagree. -/
theorem cut_component_preflight (callee : ComponentCall.Callee sig) (caller : CallerId)
    {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat}
    {active : ThreadId} {frames rest} {entry : Runtime.Thread} {task : Runtime.Task (core3 grow)}
    (focused : start.ctl = ⟨some active, .prog (ComponentCall.invoke callee caller), frames⟩ :: rest)
    (record : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (liveThread : ArenaField.threads.get? start.store active = some entry)
    (liveTask : ArenaField.tasks.get? start.store entry.task = some task)
    (context : task.inst = callee.inst)
    (admitted : callee.check start.store subtask cx args pos ft (limits, results) = .ok ())
    (run : Steps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    (∃ peerFrames peerRest suffix,
      let check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨some active, frames, rest⟩
      let canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨some active, peerFrames, peerRest⟩
      let reached := componentPreflightAt callee caller cx args start check
      let peer := componentPreflightAt callee caller cx args incoming canon
      incoming.ctl = canon.control (ComponentCall.invoke callee caller) ∧ labels = List.replicate 7 .tau ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming (List.replicate 7 .tau) (List.replicate 7 .tau) reached peer ∧
      PairedComponentSite older reached peer check canon ∧ Steps profile ready (specDispatch ready base) reached suffix finish) ∨
      ∃ canon, ComponentEarlyPrefix profile ready base bindings older ⟨some active, frames, rest⟩ canon start incoming labels finish 7 :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutComponentPreflight
    callee caller focused record liveThread liveTask context admitted run paired

open ReturnFrame.Occurrence in
/-- An executed component host-function call under the fixed dispatcher
installs the matched invoked program and caller occurrence on both sides.
Every older active or saved occurrence follows the actual push. -/
theorem cut_linked_component_install {callees : List (ComponentCall.Callee sig)}
    {hostId : HostFuncId} {caller : CallerId} {callee : ComponentCall.Callee sig}
    {thread frames rest resume label next}
    (linked : callees.filter (·.hostId == hostId) = [callee])
    (focused : start.ctl = ⟨thread, .prog (.op (.call (.hostFunc hostId caller)) resume), frames⟩ :: rest)
    (taken : Step profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start label next)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ peerFrames peerRest,
      let call := ComponentCall.invoke callee caller
      let reached := { start with ctl := ⟨thread, .prog call, .prog resume :: frames⟩ :: rest }
      let peer := { incoming with ctl := ⟨thread, .prog call, .prog resume :: peerFrames⟩ :: peerRest }
      label = .tau ∧ next = reached ∧ HostFrame.Related.Paired older reached peer ∧
      OccurrenceTransport profile ready (ComponentCall.hostWithComponent bindings callees) bindings
        start incoming [.tau] [.tau] reached peer [some (.active 0 0)] ∧
      segmentAt (segmentStorage reached) (.active 0 0) = some (.prog resume) ∧
      segmentAt (segmentStorage peer) (.active 0 0) = some (.prog resume) ∧
      Outside older (segmentStorage reached) (segmentStorage peer) (some (.active 0 0)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutLinkedComponentInstall
    linked focused taken paired

open ReturnFrame.Occurrence in
/-- Classify the admitted component body from the actual entry. Before the
preflight, pair only the reached steps. At preflight, compare the demanded
decisions and follow the corresponding refusal or observer/registration body.
Only an executed marked reply may expose a worker residual. -/
theorem cut_admitted_component (callee : ComponentCall.Callee sig) (caller : CallerId)
    {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat}
    {active : ThreadId} {frames rest} {entry : Runtime.Thread} {task : Runtime.Task (core3 grow)}
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (focused : start.ctl = ⟨some active, .prog (ComponentCall.invoke callee caller), frames⟩ :: rest)
    (record : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (liveThread : ArenaField.threads.get? start.store active = some entry)
    (liveTask : ArenaField.tasks.get? start.store entry.task = some task)
    (context : task.inst = callee.inst)
    (admitted : callee.check start.store subtask cx args pos ft (limits, results) = .ok ())
    (paired : HostFrame.Related.Paired wider start incoming)
    (leftInstalled : segmentAt (segmentStorage start) (.active 0 0) = some (.prog first))
    (rightInstalled : segmentAt (segmentStorage incoming) (.active 0 0) = some (.prog second))
    (outside : Outside older (segmentStorage start) (segmentStorage incoming) (some (.active 0 0)))
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ComponentAdmissionCut profile ready base bindings older wider callee caller cx args
      ⟨some active, frames, rest⟩ first second start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutAdmittedComponent
    callee caller focused record liveThread liveTask context admitted paired leftInstalled rightInstalled outside run

/-- Classify the body after an actual linked component install, including
finite prefixes that end inside entry, refusal, or publication. The same
installed continuation is tracked across the reached body, not replayed. -/
theorem classify_linked_component_admission {callees : List (ComponentCall.Callee sig)}
    {hostId : HostFuncId} {caller : CallerId} {callee : ComponentCall.Callee sig}
    {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat}
    {active : ThreadId} {frames rest resume label next} {entry : Runtime.Thread} {task : Runtime.Task (core3 grow)}
    (linked : callees.filter (·.hostId == hostId) = [callee])
    (focused : start.ctl = ⟨some active, .prog (.op (.call (.hostFunc hostId caller)) resume), frames⟩ :: rest)
    (taken : Step profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start label next)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) next labels finish)
    (paired : HostFrame.Related.Paired older start incoming)
    (record : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (liveThread : ArenaField.threads.get? start.store active = some entry)
    (liveTask : ArenaField.tasks.get? start.store entry.task = some task)
    (context : task.inst = callee.inst)
    (admitted : callee.check start.store subtask cx args pos ft (limits, results) = .ok ()) :
    ∃ peerFrames peerRest,
      let body := ComponentCall.invoke callee caller
      let peer := { incoming with ctl := ⟨some active, .prog body, .prog resume :: peerFrames⟩ :: peerRest }
      label = .tau ∧
      OccurrenceTransport profile ready (ComponentCall.hostWithComponent bindings callees) bindings
        start incoming [.tau] [.tau] next peer [some (.active 0 0)] ∧
      ComponentAdmissionCut profile ready (ComponentCall.hostWithComponent bindings callees) bindings older older callee caller cx args
        ⟨some active, .prog resume :: frames, rest⟩ resume resume next peer labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.classifyLinkedComponentAdmission
    linked focused taken run paired record liveThread liveTask context admitted

/-- Cut the finite checked worker derivation at the actual boundary. A reached
component install is classified from the fixed dispatcher and live arena guards.
Missing or ambiguous linkage compares the executed diagnostic prefix and lockdown
when reached; admission compares the exact installed body and marked reply. -/
theorem classify_component_worker_prefix {callees : List (ComponentCall.Callee sig)}
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ComponentWorkerCut profile ready bindings callees older start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.classifyComponentWorkerPrefix run paired

/-- Consume the actual entry and admitted guard steps, then expose the shared pre-lift
decision with separate tickets and every enclosing occurrence intact. A finite checked
run ending earlier does not authorize a completed admission. -/
theorem cut_component_admitted (callee : ComponentCall.Callee sig) (caller : CallerId)
    {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat}
    {active : ThreadId} {frames rest} {entry : Runtime.Thread} {task : Runtime.Task (core3 grow)}
    (focused : start.ctl = ⟨some active, .prog (ComponentCall.invoke callee caller), frames⟩ :: rest)
    (record : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (liveThread : ArenaField.threads.get? start.store active = some entry)
    (liveTask : ArenaField.tasks.get? start.store entry.task = some task)
    (context : task.inst = callee.inst)
    (admitted : callee.check start.store subtask cx args pos ft (limits, results) = .ok ())
    (observed : callee.ChildObservationsAgree start.host.writer.accepted incoming.host.writer.accepted start.store cx args)
    (run : Steps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    let plan := callee.childPreflight start.host.writer.accepted start.store cx args
    let reached := fun (state : Config (core3 grow) (HostState sig)) atFrames atRest =>
      { state with
        host := state.host.enter callee.name callee.coreType args
        ctl := ⟨some active, .prog (ComponentCall.acceptPlanned callee caller state.host.nextTicket plan), atFrames⟩ :: atRest }
    (∃ peerFrames peerRest suffix, labels = List.replicate 7 .tau ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming (List.replicate 7 .tau) (List.replicate 7 .tau)
        (reached start frames rest) (reached incoming peerFrames peerRest) ∧
      PairedComponentSite older (reached start frames rest) (reached incoming peerFrames peerRest)
        ⟨some active, frames, rest⟩ ⟨some active, peerFrames, peerRest⟩ ∧
      Steps profile ready (specDispatch ready base) (reached start frames rest) suffix finish) ∨ labels.length < 7 :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutComponentAdmitted
    callee caller focused record liveThread liveTask context admitted observed run paired

/-- Continue a reached lift branch through the actual lower-on-start protocol. Both
stores retain any progress-event update and the checked residual starts at argument
lifting, not at a presumed payload return. -/
theorem cut_component_lift_start (callee : ComponentCall.Callee sig) (caller : CallerId)
    {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat} (record : Subtask)
    {planned : Option (List (Stored.OwnedMemory.Tree sig))} {leftTicket rightTicket : Nat}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (ComponentCall.acceptPlanned callee caller leftTicket (.ok planned)))
    (rightFocus : incoming.ctl = canon.control (ComponentCall.acceptPlanned callee caller rightTicket (.ok planned)))
    (callerRecord : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (live : start.store.subtask? subtask = some record)
    (run : Steps profile ready (specDispatch ready base) start labels finish)
    (paired : PairedComponentSite older start incoming check canon) :
    let count := if record.index.isSome then 4 else 3
    let reached := fun (state : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) ticket =>
      let queued := if record.index.isSome then state.store.setPendingSt (.subtask subtask) (.subtask subtask) else state.store
      { state with
        store := LowerSt.startSt subtask queued
        ctl := cursor.control (do
          let (values, next) ← Stored.OwnedMemory.liftFlatValuesWith Limits.spec cx
            (Stored.OwnedMemory.flatCarrier Limits.spec Quirks.none cx) limits ⟨args, pos⟩ (ft.params.map (·.2))
          modifyStore (LowerSt.setCallerPosSt caller next.pos)
          ComponentCall.acceptPayload callee caller ticket planned values) }
    (∃ suffix, labels = List.replicate count .tau ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming (List.replicate count .tau) (List.replicate count .tau)
        (reached start check leftTicket) (reached incoming canon rightTicket) ∧
      PairedComponentSite older (reached start check leftTicket) (reached incoming canon rightTicket) check canon ∧
      Steps profile ready (specDispatch ready base) (reached start check leftTicket) suffix finish) ∨ labels.length < count :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutComponentLiftStart
    callee caller record leftFocus rightFocus callerRecord live run paired

/-- Consume the actual checked derivation while the focused programs run the
same store-local body with different continuations. The finite prefix ends
at an executed result, a trap, exhaustion, or the first other operation. -/
theorem cut_component_store_body {Result : Type} (body : Session grow sig Result)
    (checkNext canonNext : Result → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (body >>= checkNext))
    (rightFocus : incoming.ctl = canon.control (body >>= canonNext))
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon checkNext canonNext reached peer suffix ∧
      reached.host = start.host ∧ peer.host = incoming.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutComponentStoreBody
    body checkNext canonNext False.elim leftFocus rightFocus paired run

/-- Extract the reached poll result (including an empty poll) or the selection
shared with wait. The same executed shuffle is used on the peer. Taking an
event reads and updates the live store; no particular producer or pending
record is assumed. An exhausted prefix need not reach the buffer program. -/
theorem cut_waitable_selection (poll : Bool) (ws : WsetId)
    (checkNext canonNext : AsyncRef.EventTuple → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control ((if poll then wsetPoll ws else wsetGetPendingEvent ws) >>= checkNext))
    (rightFocus : incoming.ctl = canon.control ((if poll then wsetPoll ws else wsetGetPendingEvent ws) >>= canonNext))
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon checkNext canonNext reached peer suffix True ∧
      reached.host = start.host ∧ peer.host = incoming.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutComponentStoreBody
    _ checkNext canonNext (fun _ => Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.waitableSelectionEffects poll ws)
    leftFocus rightFocus paired run

/-- Follow the actual public poll or wait entry, including the defining-instance
check, argument decoder, current-instance checks and handle lookup. A reached
trap or exhausted prefix does not supply a waitable set or a caller reply. -/
theorem cut_waitable_callout_entry (poll : Bool) (mem : (core3 grow).MemAddr) (inst : InstId) (args : List FlatValue)
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (specDispatch ready base (.hostCallout (waitableCalloutHost poll mem inst) args)))
    (rightFocus : incoming.ctl = canon.control (specDispatch ready (LiveDispatch.host bindings base)
      (.hostCallout (waitableCalloutHost poll mem inst) args)))
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon (waitableCalloutBody poll mem) (waitableCalloutBody poll mem)
        reached peer suffix True ∧ reached.host = start.host ∧ peer.host = incoming.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutWaitableCalloutEntry
    poll mem inst args leftFocus rightFocus paired run

/-- Compare the wait's reached readiness read and scheduler choice. The
non-early case includes the waiting-record write, but not the block. Neither
case has yet selected or consumed an event. -/
theorem cut_waitable_wait_decision (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry)
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (waitableCalloutBody false mem entry))
    (rightFocus : incoming.ctl = canon.control (waitableCalloutBody false mem entry))
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon (waitableWaitAfterDecision mem entry) (waitableWaitAfterDecision mem entry)
        reached peer suffix True ∧ reached.host = start.host ∧ peer.host = incoming.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutWaitableWaitDecision
    mem entry leftFocus rightFocus paired run

open ReturnFrame.Occurrence in
/-- Consume the actual non-early wait block, if the checked derivation reaches
it. The original Core caller moves to the saved location along with the
post-wait program. The same edit accounts for every other occurrence,
including replacement of an older saved slot. No event has been selected. -/
theorem cut_waitable_wait_park (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry)
    {thread core resume frames rest peerFrames peerRest}
    (leftFocus : start.ctl = ⟨some thread, .prog (waitableWaitAfterDecision mem entry (some thread)), .core core resume :: frames⟩ :: rest)
    (rightFocus : incoming.ctl = ⟨some thread, .prog (waitableWaitAfterDecision mem entry (some thread)),
      .core core resume :: peerFrames⟩ :: peerRest)
    (paired : PairedComponentSite older start incoming ⟨some thread, .core core resume :: frames, rest⟩
      ⟨some thread, .core core resume :: peerFrames, peerRest⟩)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    (labels = [] ∧ finish = start) ∨
      ∃ suffix,
        let reached := { (start.setCont thread (some ⟨some thread, .prog (waitableWaitContinue mem entry), .core core resume :: frames⟩)) with
          store := StepDefs.threadStatusSt thread .blocked start.store, ctl := rest }
        let peer := { (incoming.setCont thread (some ⟨some thread, .prog (waitableWaitContinue mem entry), .core core resume :: peerFrames⟩)) with
          store := StepDefs.threadStatusSt thread .blocked incoming.store, ctl := peerRest }
        labels = .tau :: suffix ∧ Steps profile ready (specDispatch ready base) reached suffix finish ∧
        HostFrame.Related.Paired older reached peer ∧
        OccurrenceTransport profile ready base bindings start incoming [.tau] [.tau] reached peer ∧
        Trail profile ready (specDispatch ready base) start (some (.active 0 0)) [.tau] reached (some (.saved thread.idx 0)) ∧
        Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming (some (.active 0 0))
          [.tau] peer (some (.saved thread.idx 0)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutWaitableWaitPark
    mem entry leftFocus rightFocus paired run

open ReturnFrame.Occurrence in
/-- Compare the executed resumption of a reached saved wait program, including
its Core slot. The live saved-slot read, not any earlier event, identifies
the resumed program; no delivery or Core pop has occurred at the resume. -/
theorem cut_waitable_wait_resume (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry)
    {waiter resumer afterResume frames rest core resume savedFrames label next}
    (scheduled : start.ctl = ⟨resumer, .prog (.op (.resumeThread waiter) afterResume), frames⟩ :: rest)
    (found : start.cont? waiter = some ⟨some waiter, .prog (waitableWaitContinue mem entry), .core core resume :: savedFrames⟩)
    (step : Step profile ready (specDispatch ready base) start label next)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ peerFrames peerRest peerSaved,
      let check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨some waiter, .core core resume :: savedFrames,
        ⟨resumer, .prog (afterResume ()), frames⟩ :: rest⟩
      let canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨some waiter, .core core resume :: peerSaved,
        ⟨resumer, .prog (afterResume ()), peerFrames⟩ :: peerRest⟩
      let reached := { (start.setCont waiter none) with
        store := StepDefs.threadStatusSt waiter .running start.store
        ctl := check.control (waitableWaitContinue mem entry) }
      let peer := { (incoming.setCont waiter none) with
        store := StepDefs.threadStatusSt waiter .running incoming.store
        ctl := canon.control (waitableWaitContinue mem entry) }
      label = .tau ∧ next = reached ∧ PairedComponentSite older reached peer check canon ∧
      OccurrenceTransport profile ready base bindings start incoming [.tau] [.tau] reached peer ∧
      Trail profile ready (specDispatch ready base) start (some (.saved waiter.idx 0)) [.tau] reached (some (.active 0 0)) ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming (some (.saved waiter.idx 0))
        [.tau] peer (some (.active 0 0)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutWaitableWaitResume
    mem entry scheduled found step paired

open ReturnFrame.Occurrence in
/-- Recover the public waitable callout and both original caller occurrences
from an executed Core install. Older active and saved marks are transported
across the push; the new mark denotes the installed caller, not the reply. -/
theorem cut_waitable_callout_install (poll : Bool) (mem : (core3 grow).MemAddr) (inst : InstId) (args : List FlatValue)
    {thread core resume frames rest label next}
    (focused : start.ctl = ⟨thread, .core core resume, frames⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (waitableCalloutHost poll mem inst) args)
    (taken : Step profile ready (specDispatch ready base) start label next)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ peerFrames peerRest,
      let caller : Seg (core3 grow) (HostState sig) := .core core resume
      let check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨thread, caller :: frames, rest⟩
      let canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨thread, caller :: peerFrames, peerRest⟩
      let request := Call.hostCallout (waitableCalloutHost poll mem inst) args
      let reached := { start with ctl := check.control (specDispatch ready base request) }
      let peer := { incoming with ctl := canon.control (specDispatch ready (LiveDispatch.host bindings base) request) }
      label = .tau ∧ next = reached ∧ PairedComponentSite older reached peer check canon ∧
      OccurrenceTransport profile ready base bindings start incoming [.tau] [.tau] reached peer [some (.active 0 0)] ∧
      segmentAt (segmentStorage reached) (.active 0 0) = some caller ∧
      segmentAt (segmentStorage peer) (.active 0 0) = some caller :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutWaitableCalloutInstall
    poll mem inst args focused calling taken paired

open ReturnFrame.Occurrence in
/-- Follow an executed public poll from its Core install through the reached
selection and buffer program. The returned case has already consumed the
original Core frame; its residual comes from the same checked derivation.
Finite exhaustion (including at reply focus) and traps do not pop it. -/
theorem cut_public_poll (mem : (core3 grow).MemAddr) (inst : InstId) (args : List FlatValue)
    {thread core resume frames rest label installed}
    (focused : start.ctl = ⟨thread, .core core resume, frames⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (waitableCalloutHost true mem inst) args)
    (step : Step profile ready (specDispatch ready base) start label installed)
    (run : Steps profile ready (specDispatch ready base) installed labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ peerFrames peerRest leading suffix reached peer,
      let caller : Seg (core3 grow) (HostState sig) := .core core resume
      let check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨thread, caller :: frames, rest⟩
      let canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨thread, caller :: peerFrames, peerRest⟩
      label :: labels = (.tau :: leading) ++ suffix ∧
      (∃ mark, OccurrenceTransport profile ready base bindings start incoming (.tau :: leading) (.tau :: leading) reached peer [mark]) ∧
      (reached.ctl ≠ [] → OccurrenceTransport profile ready base bindings start incoming (.tau :: leading) (.tau :: leading)
        reached peer [some (.active 0 0)]) ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon waitableFlatReply waitableFlatReply reached peer suffix True ∧
      WaitableCalloutExit profile ready base bindings older reached peer suffix finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutPublicPoll
    mem inst args focused calling step run paired

open ReturnFrame.Occurrence in
/-- Follow the post-wait program, including the actual waiting-count decrement,
live event selection and buffer writes. A missing or consumed event can trap;
only an executed pop at the returned focus resumes the Core caller. -/
theorem cut_waitable_wait_delivery (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry)
    {thread core resume frames rest peerFrames peerRest}
    (leftFocus : start.ctl = ⟨thread, .prog (waitableWaitContinue mem entry), .core core resume :: frames⟩ :: rest)
    (rightFocus : incoming.ctl = ⟨thread, .prog (waitableWaitContinue mem entry), .core core resume :: peerFrames⟩ :: peerRest)
    (paired : PairedComponentSite older start incoming ⟨thread, .core core resume :: frames, rest⟩
      ⟨thread, .core core resume :: peerFrames, peerRest⟩)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older ⟨thread, .core core resume :: frames, rest⟩
        ⟨thread, .core core resume :: peerFrames, peerRest⟩ waitableFlatReply waitableFlatReply reached peer suffix True ∧
      WaitableCalloutExit profile ready base bindings older reached peer suffix finish ∧
      (reached.ctl ≠ [] → ∀ place,
        Prefix profile ready (specDispatch ready base) start place leading reached place ∧
        Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place leading peer place) ∧
      reached.host = start.host ∧ peer.host = incoming.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutWaitableWaitDelivery
    mem entry leftFocus rightFocus paired run

open ReturnFrame.Occurrence in
/-- Cross the executed saved wait resume and keep its actual checked residual
through the fresh delivery program. Event selection uses the reached store,
and the saved Core occurrence is tracked independently of the event. -/
theorem cut_resumed_wait_delivery (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry)
    {waiter resumer afterResume frames rest core resume savedFrames label next}
    (scheduled : start.ctl = ⟨resumer, .prog (.op (.resumeThread waiter) afterResume), frames⟩ :: rest)
    (found : start.cont? waiter = some ⟨some waiter, .prog (waitableWaitContinue mem entry), .core core resume :: savedFrames⟩)
    (step : Step profile ready (specDispatch ready base) start label next)
    (run : Steps profile ready (specDispatch ready base) next labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ leading suffix reached peer check canon,
      label :: labels = (.tau :: leading) ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming (.tau :: leading) (.tau :: leading) reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon waitableFlatReply waitableFlatReply reached peer suffix True ∧
      WaitableCalloutExit profile ready base bindings older reached peer suffix finish ∧
      (reached.ctl ≠ [] →
        Trail profile ready (specDispatch ready base) start (some (.saved waiter.idx 0))
          (.tau :: leading) reached (some (.active 0 0)) ∧
        Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming (some (.saved waiter.idx 0))
          (.tau :: leading) peer (some (.active 0 0))) ∧
      reached.host = start.host ∧ peer.host = incoming.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutResumedWaitDelivery
    mem entry scheduled found step run paired

/-- Follow the same actual run from selection through event-buffer writes. A
returned frontier records the event and code together. A late buffer trap
keeps the earlier event consumption and does not run either continuation. -/
theorem cut_waitable_delivery (poll : Bool) (ws : WsetId) (cx : LiftLowerContext (core3 grow)) (ptr : Nat)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control ((if poll then wsetPoll ws else wsetGetPendingEvent ws) >>= fun event =>
      unpackEvent cx ptr event >>= checkNext))
    (rightFocus : incoming.ctl = canon.control ((if poll then wsetPoll ws else wsetGetPendingEvent ws) >>= fun event =>
      unpackEvent cx ptr event >>= canonNext))
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon (fun outcome : AsyncRef.EventTuple × Nat => checkNext outcome.2)
        (fun outcome => canonNext outcome.2) reached peer suffix True ∧
      reached.host = start.host ∧ peer.host = incoming.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutWaitableDelivery
    poll ws cx ptr checkNext canonNext check canon leftFocus rightFocus paired run

open ReturnFrame.Occurrence in
/-- Follow the reached admitted argument observer, from the live caller read
through direct or spilled lifting and the caller-position write. Only a reached
result enters payload validation with the common values and distinct tickets.
On a live cut it preserves ABI shape and the exact active/saved locations,
not the position, memory, or handle state. A trap still takes lockdown. -/
theorem cut_component_observed_arguments (callee : ComponentCall.Callee sig) (caller : CallerId)
    {planned : Option (List (Stored.OwnedMemory.Tree sig))} {leftTicket rightTicket : Nat}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (ComponentCall.acceptPlanned callee caller leftTicket (.ok planned)))
    (rightFocus : incoming.ctl = canon.control (ComponentCall.acceptPlanned callee caller rightTicket (.ok planned)))
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon (ComponentCall.acceptPayload callee caller leftTicket planned)
        (ComponentCall.acceptPayload callee caller rightTicket planned) reached peer suffix True ∧
      reached.host = start.host ∧ peer.host = incoming.host ∧
      (reached.ctl ≠ [] → (∀ id, LowerSt.callerShape reached.store id = LowerSt.callerShape start.store id) ∧
        ∀ place, Prefix profile ready (specDispatch ready base) start place leading reached place ∧
          Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place leading peer place) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutObservedArguments
    callee caller leftFocus rightFocus paired run

/-- Follow the real preflight-refusal path without lifting the rejected payload.
Only a reached skip result enters the ticket-specific refusal continuations. -/
theorem cut_component_skipped_arguments (callee : ComponentCall.Callee sig) (caller : CallerId) (issue : Scheduled.Issue)
    {leftTicket rightTicket : Nat} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (ComponentCall.acceptPlanned callee caller leftTicket (.error issue)))
    (rightFocus : incoming.ctl = canon.control (ComponentCall.acceptPlanned callee caller rightTicket (.error issue)))
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier (Result := List Unit) older check canon (fun _ => ComponentCall.resolveRefused leftTicket caller issue)
        (fun _ => ComponentCall.resolveRefused rightTicket caller issue) reached peer suffix ∧
      reached.host = start.host ∧ peer.host = incoming.host :=
  cut_component_store_body (ComponentCall.skipArguments caller) _ _ leftFocus rightFocus paired run

open AsyncRef in
/-- Record the actual shared preflight refusal under each side's ticket and
consume the reached caller read. The common result-lowering focus is not a
delivered reply, and may still trap before resolving the subtask. -/
theorem cut_component_resolve_refused (caller : CallerId) (issue : Scheduled.Issue)
    {leftTicket rightTicket : Nat} {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (ComponentCall.resolveRefused leftTicket caller issue))
    (rightFocus : incoming.ctl = canon.control (ComponentCall.resolveRefused rightTicket caller issue))
    (record : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (resultType : ft.result = some ComponentCall.resultType) (indirect : results ≤ 1)
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    let common : Session grow sig (Ret (core3 grow)) := do
      maybeOnProgress subtask
      let flat ← lowerFlatValues Limits.spec Quirks.none cx results [.variant 1 none]
        [ComponentCall.resultType] (some ⟨args, pos⟩)
      Subtask.resolve subtask .returned flat
      return .cancel .none
    let reached := fun (state : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) ticket =>
      { state with host := state.host.record (.refused ticket issue), ctl := cursor.control common }
    (∃ suffix, labels = [.tau, .tau, .tau] ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming [.tau, .tau, .tau] [.tau, .tau, .tau]
        (reached start check leftTicket) (reached incoming canon rightTicket) ∧
      HostFrame.Related.Paired older (reached start check leftTicket) (reached incoming canon rightTicket) ∧
      Steps profile ready (specDispatch ready base) (reached start check leftTicket) suffix finish) ∨
    ComponentEarlyPrefix profile ready base bindings older check canon start incoming labels finish 3 :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutComponentResolveRefused
    caller issue leftFocus rightFocus record resultType indirect paired run

open AsyncRef in
/-- Cross the executed argument skip and refusal journaling as one cut. The
skipped caller position and result guards come from the starting caller and
successful linked check, not a second post-skip caller premise. -/
theorem cut_component_admitted_refusal (callee : ComponentCall.Callee sig) (caller : CallerId) (issue : Scheduled.Issue)
    {leftTicket rightTicket : Nat} {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat} {index : Option Nat} (record : Subtask)
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (ComponentCall.acceptPlanned callee caller leftTicket (.error issue)))
    (rightFocus : incoming.ctl = canon.control (ComponentCall.acceptPlanned callee caller rightTicket (.error issue)))
    (callerRecord : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (live : start.store.subtask? subtask = some record)
    (admitted : callee.check start.store subtask cx args pos ft (limits, results) index = .ok ())
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    let count := if record.index.isSome then 8 else 7
    let common : Session grow sig (Ret (core3 grow)) := do
      maybeOnProgress subtask
      let flat ← lowerFlatValues Limits.spec Quirks.none cx results [.variant 1 none]
        [ComponentCall.resultType] (some ⟨args, args.length - 1⟩)
      Subtask.resolve subtask .returned flat
      return .cancel .none
    (∃ suffix reached peer, labels = List.replicate count .tau ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming (List.replicate count .tau) (List.replicate count .tau) reached peer ∧
      reached.ctl = check.control common ∧ peer.ctl = canon.control common ∧
      HostFrame.Related.Paired older reached peer ∧ Steps profile ready (specDispatch ready base) reached suffix finish) ∨
    ComponentEarlyPrefix profile ready base bindings older check canon start incoming labels finish count :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutAdmittedRefusal
    callee caller issue record leftFocus rightFocus callerRecord live admitted paired run

/-- Compare the actual common refusal tail through progress, result-buffer lowering
and subtask resolution. A pending certified operation exhausts the finite checked
input; a trap keeps the reached effects and never reaches the common reply focus. -/
theorem cut_component_admitted_refusal_result (callee : ComponentCall.Callee sig) (caller : CallerId)
    (issue : Scheduled.Issue)
    {leftTicket rightTicket : Nat} {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat} {index : Option Nat} (record : Subtask)
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (ComponentCall.acceptPlanned callee caller leftTicket (.error issue)))
    (rightFocus : incoming.ctl = canon.control (ComponentCall.acceptPlanned callee caller rightTicket (.error issue)))
    (callerRecord : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (live : start.store.subtask? subtask = some record)
    (admitted : callee.check start.store subtask cx args pos ft (limits, results) index = .ok ())
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    (∃ leading suffix reached peer, labels = leading ++ suffix ∧ suffix.length < labels.length ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier (Result := Unit) older check canon (fun _ => .pure (.cancel .none))
        (fun _ => .pure (.cancel .none)) reached peer suffix True) ∨
    ComponentEarlyPrefix profile ready base bindings older check canon start incoming labels finish (if record.index.isSome then 8 else 7) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutAdmittedRefusalResult
    callee caller issue record leftFocus rightFocus callerRecord live admitted paired run

open ReturnFrame.Occurrence in
/-- Consume the executed residual of a shared component refusal with the original
caller occurrence marked. An exhausted reply focus or a lost mark does not
resume the caller, and a pop at this cut does not deliver an event. -/
theorem cut_component_admitted_refusal_marked_reply (callee : ComponentCall.Callee sig) (caller : CallerId)
    (issue : Scheduled.Issue)
    {leftTicket rightTicket : Nat} {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat} {index : Option Nat} (record : Subtask)
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (ComponentCall.acceptPlanned callee caller leftTicket (.error issue)))
    (rightFocus : incoming.ctl = canon.control (ComponentCall.acceptPlanned callee caller rightTicket (.error issue)))
    (callerRecord : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (live : start.store.subtask? subtask = some record)
    (admitted : callee.check start.store subtask cx args pos ft (limits, results) index = .ok ())
    (paired : PairedComponentSite wider start incoming check canon)
    (leftInstalled : segmentAt (segmentStorage start) (.active 0 0) = some (.prog first))
    (rightInstalled : segmentAt (segmentStorage incoming) (.active 0 0) = some (.prog second))
    (outside : Outside older (segmentStorage start) (segmentStorage incoming) (some (.active 0 0)))
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    (∃ leading suffix reached peer, labels = leading ++ suffix ∧ suffix.length < labels.length ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier (Result := Unit) wider check canon (fun _ => .pure (.cancel .none))
        (fun _ => .pure (.cancel .none)) reached peer suffix True ∧
      ComponentMarkedReplyTail profile ready base bindings older start incoming reached peer leading
        check first second suffix finish) ∨
    ComponentEarlyPrefix profile ready base bindings wider check canon start incoming labels finish (if record.index.isSome then 8 else 7) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutAdmittedRefusalMarkedReply
    callee caller issue record leftFocus rightFocus callerRecord live admitted paired leftInstalled rightInstalled outside run

/-- Cross the successful checked payload branch at a live caller. The two
registration probes need only agree on success and the returned handle.
Only an executed result body reaches publication; before that, the paired
cut keeps the exact finite prefix or the reached lockdown. -/
theorem cut_component_successful_payload (callee : ComponentCall.Callee sig) (caller : CallerId)
    (first payload : Stored.OwnedMemory.Observed) (children : List (Stored.OwnedMemory.Tree sig))
    {valid : Stored.OwnedMemory.Payload (sig.payload callee.tag)}
    (validated : Stored.OwnedMemory.checkValue (sig.payload callee.tag) payload = .ok valid)
    {leftTicket rightTicket handle : Nat} {leftWriter rightWriter : Stored.OwnedMemory.Claims.State sig}
    {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (ComponentCall.acceptPayload callee caller leftTicket (some children) [first, payload]))
    (rightFocus : incoming.ctl = canon.control (ComponentCall.acceptPayload callee caller rightTicket (some children) [first, payload]))
    (paired : PairedComponentSite older start incoming check canon)
    (record : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (resultType : ft.result = some ComponentCall.resultType) (indirect : results ≤ 1)
    (leftLive : start.host.writer.register (.node callee.tag valid children) = .ok leftWriter)
    (rightLive : incoming.host.writer.register (.node callee.tag valid children) = .ok rightWriter)
    (leftHandle : handle = leftWriter.accepted.length) (rightHandle : handle = rightWriter.accepted.length)
    (room : handle < 2 ^ 32) (run : Steps profile ready (specDispatch ready base) start labels finish) :
    let tree : Stored.OwnedMemory.Tree sig := .node callee.tag valid children
    (∃ leading suffix reached peer,
      labels = leading ++ suffix ∧ suffix.length < labels.length ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier (Result := Unit) older check canon
        (fun _ => ComponentCall.completeResolvedTree leftTicket tree handle)
        (fun _ => ComponentCall.completeResolvedTree rightTicket tree handle) reached peer suffix True ∧
      reached.host = start.host ∧ peer.host = incoming.host) ∨
    ComponentEarlyPrefix profile ready base bindings older check canon start incoming labels finish 2 :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutSuccessfulPayload
    callee caller first payload children validated leftFocus rightFocus paired record resultType indirect
    leftLive rightLive leftHandle rightHandle room run

/-- Follow the actual successful payload residual through the result writes
and live publication. A finite prefix or trap does not produce a common reply;
publication itself exposes only the reply focus, not the caller pop or delivery. -/
theorem cut_component_successful_publication (callee : ComponentCall.Callee sig) (caller : CallerId)
    (first payload : Stored.OwnedMemory.Observed) (children : List (Stored.OwnedMemory.Tree sig))
    {valid : Stored.OwnedMemory.Payload (sig.payload callee.tag)}
    (validated : Stored.OwnedMemory.checkValue (sig.payload callee.tag) payload = .ok valid)
    {leftTicket rightTicket handle : Nat} {leftWriter rightWriter : Stored.OwnedMemory.Claims.State sig}
    {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (ComponentCall.acceptPayload callee caller leftTicket (some children) [first, payload]))
    (rightFocus : incoming.ctl = canon.control (ComponentCall.acceptPayload callee caller rightTicket (some children) [first, payload]))
    (paired : PairedComponentSite older start incoming check canon)
    (record : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (resultType : ft.result = some ComponentCall.resultType) (indirect : results ≤ 1)
    (leftLive : start.host.writer.register (.node callee.tag valid children) = .ok leftWriter)
    (rightLive : incoming.host.writer.register (.node callee.tag valid children) = .ok rightWriter)
    (leftHandle : handle = leftWriter.accepted.length) (rightHandle : handle = rightWriter.accepted.length)
    (room : handle < 2 ^ 32) (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentAcceptedFrontier older check canon (.node callee.tag valid children) handle reached peer suffix ∧
      (suffix = [] ∨ reached.ctl = [] ∨ (start.host.writer.LiveClaimsAgree incoming.host.writer →
        reached.host.writer.LiveClaimsAgree peer.host.writer)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutSuccessfulPublication
    callee caller first payload children validated leftFocus rightFocus paired record resultType indirect
    leftLive rightLive leftHandle rightHandle room run

open ReturnFrame.Occurrence in
/-- Transport the installed caller from successful validation through live
publication, deriving the peer's handle from reached claim and index agreement.
Use only the actual checked residual to compare a marked pop.
A pending prefix, trap or lost occurrence does not enter the caller. -/
theorem cut_component_successful_marked_reply (callee : ComponentCall.Callee sig) (caller : CallerId)
    (argument payload : Stored.OwnedMemory.Observed) (children : List (Stored.OwnedMemory.Tree sig))
    {valid : Stored.OwnedMemory.Payload (sig.payload callee.tag)}
    (validated : Stored.OwnedMemory.checkValue (sig.payload callee.tag) payload = .ok valid)
    {leftTicket rightTicket handle : Nat} {leftWriter : Stored.OwnedMemory.Claims.State sig}
    {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (ComponentCall.acceptPayload callee caller leftTicket (some children) [argument, payload]))
    (rightFocus : incoming.ctl = canon.control (ComponentCall.acceptPayload callee caller rightTicket (some children) [argument, payload]))
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : PairedComponentSite wider start incoming check canon)
    (record : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (resultType : ft.result = some ComponentCall.resultType) (indirect : results ≤ 1)
    (leftLive : start.host.writer.register (.node callee.tag valid children) = .ok leftWriter)
    (claims : start.host.writer.RegistrationChecksAgree incoming.host.writer (.node callee.tag valid children))
    (length : start.host.writer.accepted.length = incoming.host.writer.accepted.length)
    (leftHandle : handle = leftWriter.accepted.length)
    (room : handle < 2 ^ 32)
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (leftInstalled : segmentAt (segmentStorage start) (.active 0 0) = some (.prog first))
    (rightInstalled : segmentAt (segmentStorage incoming) (.active 0 0) = some (.prog second))
    (outside : Outside older (segmentStorage start) (segmentStorage incoming) (some (.active 0 0)))
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentAcceptedFrontier wider check canon (.node callee.tag valid children) handle reached peer suffix ∧
      ComponentMarkedReplyTail profile ready base bindings older start incoming reached peer leading
        check first second suffix finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutSuccessfulMarkedReply
    callee caller argument payload children validated leftFocus rightFocus paired record resultType indirect
    leftLive claims length leftHandle room leftInstalled rightInstalled outside run

open ReturnFrame.Occurrence in
/-- Starting at the admitted observer, consume only its executed prefix.
Re-read the caller with the reached cursor and validate the actual observations.
Follow the reached typed refusal, binding trap or live registration branch.
Registration disagreement retains the two actual programs after the host read.
Consume the caller pop only if the checked run executes it.
The original installed caller is tracked across the entire composed cut. -/
theorem cut_component_observed_acceptance (callee : ComponentCall.Callee sig) (caller : CallerId)
    {planned : Option (List (Stored.OwnedMemory.Tree sig))} {leftTicket rightTicket : Nat}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat} {index : Option Nat}
    (leftFocus : start.ctl = check.control (ComponentCall.acceptPlanned callee caller leftTicket (.ok planned)))
    (rightFocus : incoming.ctl = canon.control (ComponentCall.acceptPlanned callee caller rightTicket (.ok planned)))
    (paired : PairedComponentSite wider start incoming check canon)
    (original : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (admitted : callee.check start.store subtask cx args pos ft (limits, results) index = .ok ())
    (leftInstalled : segmentAt (segmentStorage start) (.active 0 0) = some (.prog first))
    (rightInstalled : segmentAt (segmentStorage incoming) (.active 0 0) = some (.prog second))
    (outside : Outside older (segmentStorage start) (segmentStorage incoming) (some (.active 0 0)))
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer, labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentObservedAcceptance profile ready base bindings older wider callee caller leftTicket rightTicket
        planned check canon first second start incoming reached peer leading suffix finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutObservedAcceptance
    callee caller leftFocus rightFocus paired original admitted leftInstalled rightInstalled outside run

/-- Rejoin at an actually executed completion. The two live registrations must confirm
the handle written earlier; their writers and diagnostic tickets need not agree. -/
theorem cut_component_publication {tree : Stored.OwnedMemory.Tree sig} {handle leftTicket rightTicket : Nat}
    {leftWriter rightWriter : Stored.OwnedMemory.Claims.State sig}
    {leftCursor rightCursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = leftCursor.control (ComponentCall.completeResolvedTree leftTicket tree handle))
    (rightFocus : incoming.ctl = rightCursor.control (ComponentCall.completeResolvedTree rightTicket tree handle))
    (site : PairedComponentSite older start incoming leftCursor rightCursor)
    (leftLive : start.host.writer.register tree = .ok leftWriter) (rightLive : incoming.host.writer.register tree = .ok rightWriter)
    (leftHandle : handle = leftWriter.accepted.length) (rightHandle : handle = rightWriter.accepted.length)
    (room : handle < 2 ^ 32) (run : Steps profile ready (specDispatch ready base) start labels finish) :
    let replied := fun (state : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
        (ticket : Nat) (writer : Stored.OwnedMemory.Claims.State sig) =>
      { state with
        host := (({ state.host with writer } : HostState sig).record (.published ticket handle)).record
          (.returned ticket handle)
        ctl := cursor.control (.pure (.cancel .none)) }
    (∃ suffix, labels = [.tau, .tau, .tau, .tau] ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming [.tau, .tau, .tau, .tau] [.tau, .tau, .tau, .tau]
        (replied start leftCursor leftTicket leftWriter) (replied incoming rightCursor rightTicket rightWriter) ∧
      HostFrame.Related.Paired older (replied start leftCursor leftTicket leftWriter) (replied incoming rightCursor rightTicket rightWriter) ∧
      Stored.Endpoints.Core.childFromHistory leftWriter.accepted (BitVec.ofNat 32 handle) = some tree ∧
      Stored.Endpoints.Core.childFromHistory rightWriter.accepted (BitVec.ofNat 32 handle) = some tree ∧
      Steps profile ready (specDispatch ready base) (replied start leftCursor leftTicket leftWriter) suffix finish) ∨
    ComponentEarlyPrefix profile ready base bindings older leftCursor rightCursor start incoming labels finish 4 :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutComponentPublication
    leftFocus rightFocus site leftLive rightLive leftHandle rightHandle room run

/-- Fold the actual checked callback with a local rule for reached give
installs. The rule may use the fold on strictly shorter checked subruns. -/
theorem fold_callback_slices (cross : CallbackGiveCrossing profile ready base bindings)
    (run : Steps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    CallbackSlice profile ready base bindings older start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.foldCallbackSlices cross run paired

/-- Rebase both paths of a checked-only reply through an enclosing visitor's
actual prefix. After the refusal each active or saved occurrence has its
own checked and canonical endpoint; the residual is still checked only. -/
theorem CheckedOnlyGiveReply.prepend {route : GiveEffectRoute} {destination ticket issue}
    {left right checkStop canonStop : Config (core3 grow) (HostState sig)}
    {checkPrefix canonPrefix checkBody canonBody trailing : Trace grow sig} {marks}
    (leading : OccurrenceTransport profile ready base bindings start incoming checkPrefix canonPrefix left right marks)
    (reply : CheckedOnlyGiveReply profile ready base bindings route destination ticket issue left right checkStop canonStop
      checkBody canonBody trailing finish) :
    CheckedOnlyGiveReply profile ready base bindings route destination ticket issue start incoming checkStop canonStop
      (checkPrefix ++ checkBody) (canonPrefix ++ canonBody) trailing finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.prependCheckedOnlyReply leading reply

/-- Strip the reached silent install and compare only its actual callback
tail. Both visitors can consume the resulting exact callback index. -/
theorem PairedAllocatorInstall.slice_callback
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    {checkEntry canonEntry : Config (core3 grow) (HostState sig)} {checkCount canonCount : Nat}
    (installed : PairedAllocatorInstall profile ready base bindings older first second start incoming checkEntry canonEntry
      checkCount canonCount)
    (positive : 0 < checkCount) (run : Steps profile ready (specDispatch ready base) start labels finish)
    (compare : ShorterCallbackSlices profile ready base bindings labels.length) :
    InstalledCallbackSlice profile ready base bindings older first second checkEntry canonEntry checkCount labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.sliceInstalledCallback installed positive run compare

/-- Classify the actual checked callback derivation without choosing an
allocator return or supplying an independent callback execution. Only
reached synchronous reads with compatible candidate queries are crossed. -/
theorem ClosedCallbackPrefix.classify_actual {protectedReturn}
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ClassifiedCallbackRun bindings profile ready base protectedReturn start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.classifyActual run

open ReturnFrame.Occurrence in
/-- Feed the actual callback prefix and next give installation to the live
selector. The extracted checked tail is not authorized on the canonical
side merely by reaching the request. -/
theorem ActualCallbackReplay.reached_give {callees : List (ComponentCall.Callee sig)} {protectedReturn label trailing}
    {reached next : Config (core3 grow) (HostState sig)} {mark : Option Location}
    {retained : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (replay : ActualCallbackReplay bindings profile ready (ComponentCall.hostWithComponent bindings callees)
      protectedReturn start labels reached)
    (install : GiveInstall bindings (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) reached label next)
    (actual : Step profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) reached label next)
    (tail : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) next trailing finish)
    (covers : ∀ first second, older first second → protectedReturn first)
    (paired : HostFrame.Related.Paired older start incoming)
    (outside : Outside retained (segmentStorage start) (segmentStorage incoming) mark) :
    Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start (labels ++ label :: trailing) finish ∧
    ClassifiedWorkerTail profile ready bindings callees older start incoming (labels ++ label :: trailing) finish
      (WorkerOccurrencePrefix profile ready bindings callees retained start incoming mark) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.actualCallbackGive
    replay install actual tail covers paired outside

/-- Cross the checked front of a selected nested give using its actual
residual derivation. The paired canonical entry is still pending. A shorter
checked run does not witness a guard trap, checked reply, or body entry. -/
theorem ReachedRecursiveGive.align_entry {route : GiveEffectRoute} {request : CoreGiveRequest bindings start}
    {selection : request.Selected route} {callees : List (ComponentCall.Callee sig)}
    (entry : ReachedRecursiveGive profile ready callees selection older incoming)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish) :
    RecursiveGiveEntryAlignment profile ready callees selection older incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.alignRecursiveEntry entry run

open ReturnFrame.Occurrence in
/-- An extracted finite allocator prefix gives the actual reached store and
marked occurrence. There is no allocator return premise; a lost mark is
not replaced by an equal saved or active continuation. -/
theorem ActualCallbackReplay.allocator_prefix {protectedReturn}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (replay : ActualCallbackReplay bindings profile ready base protectedReturn start labels finish)
    (covers : ∀ first second, changes first second → protectedReturn first)
    (paired : HostFrame.Related.Paired changes start incoming)
    (outside : Outside older (segmentStorage start) (segmentStorage incoming) (some (.active 0 0))) :
    ∃ reached mark, AllocatorMark profile ready base bindings older start incoming labels labels finish reached mark ∧
      HostFrame.Related.Paired changes finish reached ∧
      ComparedOccurrencePaths profile ready base bindings start incoming (PayloadPrefix.visible labels) finish reached :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.actualAllocatorPrefix
    replay covers paired outside

/-- The allocating string action saves the real shorter program, while
all enclosing marks retain their actual active/saved coordinate trails. -/
theorem ActualCallbackReplay.string_install (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (checkAt : start.ctl = check.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= checkNext))
    (canonAt : incoming.ctl = canon.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= canonNext)) :
    let first := PayloadPrefix.stringPlanResume cx steps checkNext
    let second := PayloadPrefix.stringPlanResume cx steps canonNext
    let checkEntry := LinkedCallback.stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext start check
    let canonEntry := stringAllocatorEntry (specDispatch ready (LiveDispatch.host bindings base)) cx ptr oldSize alignment size incoming canon second
    ActualCallbackReplay bindings profile ready base (fun resume => (∃ peer, older resume peer) ∨ resume = first) checkEntry labels finish →
    ActualAllocatorOccurrencePrefix profile ready base bindings older (ReturnFrame.Extend older first second) start incoming checkEntry canonEntry
      [.tau] [.tau] labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.actualStringInstall
    cx ptr oldSize alignment size steps checkNext canonNext frame checkAt canonAt

/-- The real guarded list/map allocation uses the reached width and
authority check, and keeps the placement mode of the canonical suffix. -/
theorem ActualCallbackReplay.collection_install (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Field) (output : Stored.Lower.Output) (index : Nat)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (width : (core3 grow).memAddrType? incoming.store.core destination.memory = some destination.width)
    (prepared : Stored.OwnedMemory.Claims.Record.prepare start.store start.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : start.ctl = check.control (Stored.OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let area := layout destination.width element
    let first := PayloadPrefix.checkedCollectionResume destination inst entries area index output checkNext
    let second := PayloadPrefix.canonicalCollectionResume destination inst entries area output canonNext
      (CanonicalTree.EntryMode.forOutput destination.width type output)
    let checkEntry := PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start check first
    let canonEntry := PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base)) incoming canon second
    ActualCallbackReplay bindings profile ready base (fun resume => (∃ peer, older resume peer) ∨ resume = first) checkEntry labels finish →
    ActualAllocatorOccurrencePrefix profile ready base bindings older (ReturnFrame.Extend older first second) start incoming checkEntry canonEntry
      [.tau, .tau, .tau] [.tau, .tau] labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.actualCollectionInstall
    destination inst type element entries output index checkNext canonNext frame width prepared checkAt canonAt

/-- An actual Core engine step in the callback needs no host-write,
dispatch or readiness premise. The reached store need not equal the old one. -/
theorem ClosedCallbackPrefix.core_internal {protectedReturn thread core next frames rest store coreNext}
    (focused : start.ctl = ⟨thread, .core core next, frames⟩ :: rest)
    (running : (core3 grow).status start.store.core core = .running ∨ (core3 grow).status start.store.core core = .stuck)
    (executed : (core3 grow).Internal (start.store.core, core) (store, coreNext))
    (tail : ClosedCallbackPrefix bindings profile ready base protectedReturn
      { start with store := { start.store with core := store }, ctl := ⟨thread, .core coreNext next, frames⟩ :: rest } labels finish) :
    ClosedCallbackPrefix bindings profile ready base protectedReturn start (.core :: labels) finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.coreInternal focused running executed tail

/-- Replay a finite classified callback under the live canonical dispatcher.
Ordinary steps may change the reached store (including guest writes and
growth); confined gives take their real status replies. Accepted observations
are retained on both sides of this prefix, not by arbitrary hooks or later pops. -/
theorem ClosedCallbackPrefix.replay {protectedReturn}
    (path : ClosedCallbackPrefix bindings profile ready base protectedReturn start labels finish)
    (embedder : base.embedder = (Core.Scheduled.host (grow := grow) bindings).embedder)
    (covers : ∀ first second, older first second → protectedReturn first)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ checkedLabels canonLabels reached,
      Steps profile ready (specDispatch ready base) start checkedLabels finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonLabels reached ∧
      HostFrame.Related.Paired older finish reached ∧
      PayloadPrefix.visible checkedLabels = labels ∧ PayloadPrefix.visible canonLabels = labels ∧
      Core3.Grows start.store.core finish.store.core ∧
      finish.host.writer.accepted = start.host.writer.accepted ∧ reached.host.writer.accepted = incoming.host.writer.accepted :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.replay path embedder covers paired

/-- The real string allocation or resize installs the shorter plan on both
sides. Compare the finite callback under the live overlay, without requiring
it to return and without losing older active or suspended frames. -/
theorem ClosedCallbackPrefix.string_realloc (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (checkAt : start.ctl = check.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= checkNext))
    (canonAt : incoming.ctl = canon.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (path : ClosedCallbackPrefix bindings profile ready base
      (fun resume => (∃ peer, older resume peer) ∨ resume = PayloadPrefix.stringPlanResume cx steps checkNext)
      (LinkedCallback.stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext start check) labels finish) :
    ∃ checkedLabels canonLabels reached mark,
      Steps profile ready (specDispatch ready base) start (.tau :: checkedLabels) finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming (.tau :: canonLabels) reached ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older (PayloadPrefix.stringPlanResume cx steps checkNext)
        (PayloadPrefix.stringPlanResume cx steps canonNext)) finish reached ∧
      PayloadPrefix.visible checkedLabels = labels ∧ PayloadPrefix.visible canonLabels = labels ∧
      Core3.Grows start.store.core finish.store.core ∧
      finish.host.writer.accepted = start.host.writer.accepted ∧ reached.host.writer.accepted = incoming.host.writer.accepted ∧
      AllocatorMark profile ready base bindings older
        (LinkedCallback.stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext start check)
        (stringAllocatorEntry (specDispatch ready (LiveDispatch.host bindings base)) cx ptr oldSize alignment size incoming canon
          (PayloadPrefix.stringPlanResume cx steps canonNext)) checkedLabels canonLabels finish reached mark ∧
      OccurrenceTransport profile ready base bindings start incoming (.tau :: checkedLabels) (.tau :: canonLabels) finish reached [mark] :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.stringReallocPrefix
    cx ptr oldSize alignment size steps checkNext canonNext frame checkAt canonAt embedder path

/-- Replay a reached dynamic collection allocation under the live dispatcher.
The saved canonical continuation retains its allocation-time placement mode
(including indirect maps). The dry run is only for entry: it is not evidence
that a claim remains live after an allocator return. -/
theorem ClosedCallbackPrefix.collection_alloc (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Field) (output : Stored.Lower.Output) (index : Nat)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (width : (core3 grow).memAddrType? incoming.store.core destination.memory = some destination.width)
    (prepared : Stored.OwnedMemory.Claims.Record.prepare start.store start.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : start.ctl = check.control (Stored.OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let area := layout destination.width element
    let first := PayloadPrefix.checkedCollectionResume destination inst entries area index output checkNext
    let second := PayloadPrefix.canonicalCollectionResume destination inst entries area output canonNext
      (CanonicalTree.EntryMode.forOutput destination.width type output)
    ClosedCallbackPrefix bindings profile ready base (fun resume => (∃ peer, older resume peer) ∨ resume = first)
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start check first) labels finish →
    ∃ checkedLabels canonLabels reached mark,
      Steps profile ready (specDispatch ready base) start ([.tau, .tau, .tau] ++ checkedLabels) finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming ([.tau, .tau] ++ canonLabels) reached ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older first second) finish reached ∧
      PayloadPrefix.visible checkedLabels = labels ∧ PayloadPrefix.visible canonLabels = labels ∧
      Core3.Grows start.store.core finish.store.core ∧
      finish.host.writer.accepted = start.host.writer.accepted ∧ reached.host.writer.accepted = incoming.host.writer.accepted ∧
      AllocatorMark profile ready base bindings older
        (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start check first)
        (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
          incoming canon second) checkedLabels canonLabels finish reached mark ∧
      ComparedOccurrencePaths profile ready base bindings start incoming labels finish reached ∧
      OccurrenceTransport profile ready base bindings start incoming ([.tau, .tau, .tau] ++ checkedLabels)
        ([.tau, .tau] ++ canonLabels) finish reached [mark] :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.collectionPrefix
    destination inst type element entries output index checkNext canonNext frame width prepared checkAt canonAt embedder

/-- Compare every original coordinate through the actual collection install and
finite callback cut. Only a return of that installed occurrence triggers the
reached range checks and fresh checked reservation. Neither branch assumes
preserved guest bytes or authority, and the canonical child is still pending. -/
theorem ClosedCallbackPrefix.collection_alloc_occurrences (destination : RecordDestination) (inst : InstId)
    (type element : Stored.TypeOf) (entries : List Field) (output : Stored.Lower.Output) (index : Nat)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (width : (core3 grow).memAddrType? incoming.store.core destination.memory = some destination.width)
    (prepared : Stored.OwnedMemory.Claims.Record.prepare start.store start.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : start.ctl = check.control (Stored.OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let area := layout destination.width element
    let mode := CanonicalTree.EntryMode.forOutput destination.width type output
    let first := PayloadPrefix.checkedCollectionResume destination inst entries area index output checkNext
    ClosedCallbackPrefix bindings profile ready base (fun resume => (∃ peer, older resume peer) ∨ resume = first)
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start check first) labels finish →
    ∃ checkLabels canonLabels reached mark,
      AllocatorMark profile ready base bindings older
        (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start check first)
        (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
          incoming canon (PayloadPrefix.canonicalCollectionResume destination inst entries area output canonNext mode))
        checkLabels canonLabels finish reached mark ∧
      ComparedOccurrencePaths profile ready base bindings start incoming labels finish reached ∧
      (∀ (pointer : Nat) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
        mark = some (.active 0 0) →
        finish.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer)) →
        CollectionRangeOccurrences profile ready base bindings older start incoming finish reached labels
          cursor destination area entries.length pointer (Field.listObjects entries)
          (fun addr verdict => PayloadPrefix.checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext)
          (fun addr => PayloadPrefix.canonicalCollectionTail destination inst entries area output addr mode >>= canonNext)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.collectionOccurrences
    destination inst type element entries output index checkNext canonNext frame width prepared checkAt canonAt embedder

/-- Compare a nested dynamic child's live admission and classified callbacks.
Refusal before allocation takes no canonical step. Advance to the recursive
bodies only after the marked return, live range checks and fresh reservation. -/
theorem collection_paths_from (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (checkAt : start.ctl = check.control (OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {leftStart rightStart : Config (core3 grow) (HostState sig)} {offset : Nat}
    (leading : ComparedSlots profile ready base bindings leftStart rightStart labels start incoming offset) :
    LiveCollectionEntry profile ready base bindings older destination inst type element entries index output checkNext canonNext
      start incoming check canon (fun _ _ _ _ _ _ _ => True) leftStart rightStart labels offset :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.collectionEntryPathsFrom
    destination inst type element entries index output checkNext canonNext frame checkAt canonAt embedder leading

theorem collection_paths (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (checkAt : start.ctl = check.control (OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    LiveCollectionEntry profile ready base bindings older destination inst type element entries index output checkNext canonNext
      start incoming check canon :=
  collection_paths_from destination inst type element entries index output checkNext canonNext frame checkAt canonAt embedder
    ⟨[], [], fun _ => .done _ _, fun _ => .done _ _, rfl, rfl⟩

/-- For either actual public give route, the successful admission branch
compares lists of arbitrary depth ending in nominal leaves. The compiler
supplies each child; siblings and descriptors run only after common success.
The comparison retains the reached effects and stops at the actual reply
programs, without requiring allocator return or comparing later delivery. -/
theorem linked_nominal_list_body {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (depth : Nat) (element : Stored.TypeOf) (family : NominalListType depth element)
    (schema : sig.payload site.tag = .list element)
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedNominalListBody profile ready base bindings older site depth element incoming) base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedNominalListBody
    site linked depth element family schema paired selected embedder

/-- Both linked give routes run non-string map keys before their possibly
allocating values. Values are derived from the compiler and compared by
the recursive list rule at the reached slots. Memory maps use the outer
allocation's placement mode; flat maps take the actual width reads. -/
theorem linked_map_list_body {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (key : WIT.KeyType) (keyData : PayloadPrefix.LocalDataType (.prim key.toPrimitive))
    (depth : Nat) (element : Stored.TypeOf) (family : NominalListType depth element)
    (schema : sig.payload site.tag = .map key element)
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedMapListBody profile ready base bindings older site key depth element incoming) base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedMapListBody
    site linked key keyData depth element family schema paired selected embedder

/-- The linked compiler derives children of arbitrarily interleaved list
and map nodes on both public routes. String keys and values can allocate
at any depth. Reached allocation ranges and growth justify scalar and
string placement without fixing guest bytes. Nominal fields transfer only
after their reached live checks. Option/result tags reach only the selected
arm, at its slot under the full sum layout. Fixed arrays reuse the same
placed element traversal after the real canonical width read. -/
theorem linked_recursive_collection_body {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) {type : Stored.TypeOf} (family : RecursiveCollectionType type)
    (collection : CollectionRoot type) (schema : sig.payload site.tag = type)
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedRecursiveCollectionBody profile ready base bindings older site incoming type) base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedRecursiveCollectionBody
    site linked family collection schema paired selected embedder

/-- After the recursive entries reach descriptor publication, use their
accumulated occurrence trails to return to the original parked Core caller.
A descriptor trap keeps the reached effects without executing either reply. -/
theorem LiveListPublish.rejoin {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {checked canonical left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {callerLabels seen offset}
    (caller : ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready base) site.checked
      (.active 0 0) callerLabels checked (.active 0 offset))
    (leading : ComparedSlots profile ready base bindings checked canonical seen left right offset)
    (publish : LiveListPublish profile ready base bindings route.output site.reply site.referenceReply
      (fun _ => LinkedCallback.ChildFrameOver older) left right check canon) :
    CollectionSegmentReplies profile ready base bindings older site checked canonical (fun _ => False) offset :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.rejoinPublished
    site caller leading publish

/-- On either linked public give route, derive the list or map trail from
the actual compiler output and reached callbacks. Success rejoins the
original callers via the real descriptor publication. A reached nested
typed refusal runs only the checked reply, preserving the exact stopped
canonical configuration and preceding effects. Traps and finite suspended
prefixes need not reach a reply. -/
theorem linked_collection_rejoin_paths {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) {type : Stored.TypeOf} (family : RecursiveCollectionType type)
    (collection : CollectionRoot type) (schema : sig.payload site.tag = type)
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedCollectionRejoinPaths profile ready base bindings older site incoming type) base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedCollectionRejoinPaths
    site linked family collection schema paired selected embedder

/-- Both linked give routes use the same reached, decreasing string plan.
After an actual allocator return, compare the memory descriptor or flat words
and rejoin the original callers. A finite parked prefix does not need to return. -/
theorem linked_string_rejoin_paths {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (schema : sig.payload site.tag = .prim .string)
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedStringRejoinPaths profile ready base bindings older site incoming) base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedStringRejoinPaths
    site linked schema paired selected embedder

/-- Compare a placed memory root of the supported recursive fragment,
including top-level strings, records, tuples, fixed arrays and active sums.
The actual public entry guards supply placement and the compiled field;
both original caller replies or the exact stopped/trapped paths follow
from its recursive traversal. -/
theorem linked_memory_rejoin_paths {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (linked : site.Linked bindings) (family : RecursiveCollectionType (sig.payload site.tag))
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedMemoryRejoinPaths profile ready base bindings older site incoming) base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedMemoryRejoinPaths
    site linked family paired selected embedder

/-- Follow the actual public flat program for the recursive fragment,
including active sum arms, allocating collections, strings, and transfer
leaves. The compiler supplies each reached child; only common success
joins both callers. -/
theorem linked_flat_aggregate_rejoin_paths {type : Stored.TypeOf} (site : PayloadRoot.Site grow sig (.flat type))
    (linked : site.Linked bindings) (family : RecursiveCollectionType (sig.payload site.tag))
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedFlatAggregateRejoinPaths profile ready base bindings older site incoming) base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedFlatAggregateRejoinPaths
    site linked family paired selected embedder

/-- Derive all-location paths through the reached flat body from the linked
compiler and the live request. The installed caller is followed separately;
at its reply slot, success pops on both sides and a typed late refusal pops
only on checked. Traps and finite suspensions do not promise a reply. -/
theorem linked_flat_occurrence_body {type : Stored.TypeOf} (site : PayloadRoot.Site grow sig (.flat type))
    (linked : site.Linked bindings) (family : RecursiveCollectionType (sig.payload site.tag))
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedFlatOccurrenceBody profile ready base bindings older site incoming) base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedFlatOccurrenceBody
    site linked family paired selected embedder

/-- Derive the reached memory body, including allocations inside compiled
children, and classify the marked original caller's success or late stop. -/
theorem linked_memory_occurrence_body {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (linked : site.Linked bindings) (family : RecursiveCollectionType (sig.payload site.tag))
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedMemoryOccurrenceBody profile ready base bindings older site incoming) base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedMemoryOccurrenceBody
    site linked family paired selected embedder

/-- Rebase the derived body and reply paths to each original request origin.
A checked-only reply moves checked origins through the pop, while canonical
origins stop at the exact unexecuted suffix. -/
theorem public_occurrence_exit_from_request {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {entered left right : Config (core3 grow) (HostState sig)} {checkLabels canonLabels seen : Trace grow sig}
    {verdict : Except Stored.Endpoints.RecordLower.Issue route.output.Result}
    (checked : site.EntryPrefix profile ready base checkLabels site.checked)
    (canonical : ∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place canonLabels entered (site.entryPlace place))
    (checkQuiet : PayloadPrefix.visible checkLabels = []) (canonQuiet : PayloadPrefix.visible canonLabels = [])
    (body : PublicOccurrenceExit profile ready base bindings older site entered verdict seen left right) :
    ∃ (checkBody canonBody : Trace grow sig) (mark : Option ReturnFrame.Occurrence.Location),
      ReturnFrame.Occurrence.Trail profile ready (specDispatch ready base) site.checked (some (.active 0 0)) checkBody left mark ∧
      ReturnFrame.Occurrence.Trail profile ready (specDispatch ready (LiveDispatch.host bindings base))
        entered (some (.active 0 0)) canonBody right mark ∧
      RequestExitOccurrences profile ready base bindings site.start incoming seen left right ∧
      (mark = some (.active 0 0) → ∃ checked canonical,
        RequestExitOccurrences profile ready base bindings site.start incoming seen checked canonical ∧
        RequestExitKind older verdict right checked canonical) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.rebasePublicOccurrenceExit
    site checked canonical checkQuiet canonQuiet body

open ReturnFrame.Occurrence in
/-- A reached common public reply enables actual worker replay and closed
delivery at the resumed pair, under the same fixed live dispatcher. The
reply paths originate at the original request, not a reset caller. -/
theorem public_occurrence_exit_worker {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {callees : List (ComponentCall.Callee sig)} {entered left right : Config (core3 grow) (HostState sig)}
    {checkLabels canonLabels observed : Trace grow sig} {value : route.output.Result}
    (checked : site.EntryPrefix profile ready (ComponentCall.hostWithComponent bindings callees) checkLabels site.checked)
    (canonical : ∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
      incoming place canonLabels entered (site.entryPlace place))
    (checkQuiet : PayloadPrefix.visible checkLabels = []) (canonQuiet : PayloadPrefix.visible canonLabels = [])
    (body : PublicOccurrenceExit profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site entered (.ok value)
      observed left right) :
    let base := ComponentCall.hostWithComponent bindings callees
    ∃ (checkBody canonBody : Trace grow sig) (mark : Option Location),
      Trail profile ready (specDispatch ready base) site.checked (some (.active 0 0)) checkBody left mark ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) entered (some (.active 0 0)) canonBody right mark ∧
      (mark = some (.active 0 0) → ∃ checked canonical,
        RequestExitOccurrences profile ready base bindings site.start incoming observed checked canonical ∧
        RejoinedWorkerTail profile ready bindings callees older checked canonical) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.rejoinedOccurrenceWorker
    site checked canonical checkQuiet canonQuiet body

open ReturnFrame.Occurrence in
/-- Carry the original active and saved origins from the actual public pop
to the next classified worker cut. Only actual continuation steps advance
the paths; a divergent lookup or substituted pop remains a boundary. -/
theorem public_occurrence_exit_tracked_worker {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {callees : List (ComponentCall.Callee sig)} {entered left right : Config (core3 grow) (HostState sig)}
    {checkLabels canonLabels observed : Trace grow sig} {value : route.output.Result}
    (checked : site.EntryPrefix profile ready (ComponentCall.hostWithComponent bindings callees) checkLabels site.checked)
    (canonical : ∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
      incoming place canonLabels entered (site.entryPlace place))
    (checkQuiet : PayloadPrefix.visible checkLabels = []) (canonQuiet : PayloadPrefix.visible canonLabels = [])
    (body : PublicOccurrenceExit profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site entered (.ok value)
      observed left right) :
    let base := ComponentCall.hostWithComponent bindings callees
    ∃ (checkBody canonBody : Trace grow sig) (mark : Option Location),
      Trail profile ready (specDispatch ready base) site.checked (some (.active 0 0)) checkBody left mark ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) entered (some (.active 0 0)) canonBody right mark ∧
      (mark = some (.active 0 0) → ∃ checked canonical,
        RequestWorkerTail profile ready bindings callees older site.start incoming observed checked canonical ∧
        RejoinedWorkerTail profile ready bindings callees older checked canonical) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.rejoinedTrackedWorker
    site checked canonical checkQuiet canonQuiet body

/-- A finite callback prefix has a comparison even when it has not returned.
On the actual marked return, both public collection routes take the reached
range verdict. If the range passes but live preparation refuses, only the
checked machine records a completion and rejoins its original caller. -/
theorem linked_collection_return_failures {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) {type : Stored.TypeOf} (family : RecursiveCollectionType type)
    (collection : CollectionRoot type) (schema : sig.payload site.tag = type)
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (match type with
      | .list element => LinkedCollectionReturnFailures profile ready base bindings older site incoming type element
      | .map key element => LinkedCollectionReturnFailures profile ready base bindings older site incoming type
          (.record (ABI.mapEntryFields key element))
      | _ => False) base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedCollectionReturnFailures
    site linked family collection schema paired selected embedder

/-- Both public routes finish the actual allocating string key before
entering its recursively allocating map/list value. The same compiler
evidence discharges both the key plan and the value recursion. -/
theorem linked_string_recursive_map_body {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (family : RecursiveCollectionType element)
    (schema : sig.payload site.tag = .map .string element)
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedStringRecursiveMapBody profile ready base bindings older site element incoming) base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedStringRecursiveMapBody
    site linked element family schema paired selected embedder

/-- Consume the installed allocator frame only at its actual top return.
The canonical continuation is recovered by following its occurrence from the
install, not by comparing continuation code at the reached position. -/
theorem AllocatorMark.pop {checkEntry canonEntry : Config (core3 grow) (HostState sig)} {checkTrace canonTrace : Trace grow sig}
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {value : Ret (core3 grow)}
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (marked : AllocatorMark profile ready base bindings older checkEntry canonEntry checkTrace canonTrace finish incoming (some (.active 0 0)))
    (paired : HostFrame.Related.Paired wider finish incoming)
    (returning : finish.ctl = { check with frames := .prog first :: check.frames }.control (.pure value))
    (installed : ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage canonEntry) (.active 0 0) = some (.prog second)) :
    ∃ canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
      LinkedCallback.ChildFrameOver older finish incoming check canon ∧
      Step profile ready (specDispatch ready base) finish .tau { finish with ctl := check.control (first value) } ∧
      Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau
        { incoming with ctl := canon.control (second value) } ∧
      ReturnFrame.Occurrence.RetainsBelowTop profile ready (specDispatch ready base) checkEntry (checkTrace ++ [.tau])
        { finish with ctl := check.control (first value) } ∧
      ReturnFrame.Occurrence.RetainsBelowTop profile ready (specDispatch ready (LiveDispatch.host bindings base))
        canonEntry (canonTrace ++ [.tau]) { incoming with ctl := canon.control (second value) } :=
  let ⟨canon, frame, lhs, rhs, checkTracks, canonTracks, _, _⟩ :=
    Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.pop marked paired returning installed
  ⟨canon, frame, lhs, rhs, checkTracks, canonTracks⟩

/-- A real marked allocator pop gives cumulative trails for every older
active or saved occurrence, not just the slots below the caller. -/
theorem AllocatorMark.pop_movement {checkEntry canonEntry : Config (core3 grow) (HostState sig)} {checkTrace canonTrace : Trace grow sig}
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {value : Ret (core3 grow)}
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (marked : AllocatorMark profile ready base bindings older checkEntry canonEntry checkTrace canonTrace finish incoming (some (.active 0 0)))
    (paired : HostFrame.Related.Paired wider finish incoming)
    (returning : finish.ctl = { check with frames := .prog first :: check.frames }.control (.pure value))
    (installed : ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage canonEntry) (.active 0 0) = some (.prog second)) :
    ∃ canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
      LinkedCallback.ChildFrameOver older finish incoming check canon ∧
      incoming.ctl = { canon with frames := .prog second :: canon.frames }.control (.pure value) ∧
      CoupledOccurrencePaths profile ready base bindings checkEntry canonEntry (checkTrace ++ [.tau]) (canonTrace ++ [.tau])
        { finish with ctl := check.control (first value) } { incoming with ctl := canon.control (second value) } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.popMovement marked paired returning installed

open ReturnFrame.Occurrence in
/-- Align the marked allocator return with the actual checked derivation.
A return focus at the end of a finite run does not advance either machine;
only the executed pop advances canonical, retires the allocator's mark while
preserving enclosing ones, and gives a shorter checked tail. -/
theorem AllocatorMark.align_actual_pop
    {checkEntry canonEntry last : Config (core3 grow) (HostState sig)} {checkTrace canonTrace : Trace grow sig}
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {value : Ret (core3 grow)} {mark : Option Location}
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (marked : AllocatorMark profile ready base bindings older checkEntry canonEntry checkTrace canonTrace start incoming mark)
    (paired : HostFrame.Related.Paired wider start incoming)
    (returning : start.ctl = { check with frames := .prog first :: check.frames }.control (.pure value))
    (installed : segmentAt (segmentStorage canonEntry) (.active 0 0) = some (.prog second))
    (run : Steps profile ready (specDispatch ready base) start labels last) :
    ActualMarkedPop profile ready base bindings older checkEntry canonEntry start incoming checkTrace canonTrace mark
      check first second value labels last :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.alignAllocatorPop
    marked paired returning installed run

/-- Match the real descriptor publication against the checked residual before
entering the next compiled continuation. -/
theorem LiveValueCommit.drive_actual {output : Stored.Lower.Output}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output}
    {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output}
    {published : LinkedCallback.MemorySequence.ValueFinish grow sig output}
    (commit : LiveValueCommit profile ready base bindings output checkNext canonNext published start incoming check canon)
    (actual : Steps profile ready (specDispatch ready base) start labels finish) :
    ValueCommitRun profile ready base bindings output checkNext canonNext published start incoming check canon labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.driveValueCommit commit actual

/-- Drive a linked collection field from the original checked residual.
Only the actually executed marked pop can reach the fresh range verdict. -/
theorem LiveCollectionOccurrenceEntry.drive_actual {destination : RecordDestination} {inst : InstId} {type element : Stored.TypeOf}
    {entries : List Field} {index budget : Nat} {output : Stored.Lower.Output}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output}
    {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {seen : Trace grow sig} {initial reference : Config (core3 grow) (HostState sig)}
    {visit : Nat → Nat → TrailFinish grow sig} {sink : RefusalSink grow sig}
    (body : LiveCollectionOccurrenceEntry profile ready base bindings older destination inst type element entries index output
      checkNext canonNext initial reference start incoming seen check canon visit sink)
    (same : start.store = incoming.store)
    (width : (core3 grow).memAddrType? incoming.store.core destination.memory = some destination.width)
    (actual : Steps profile ready (specDispatch ready base) start labels finish)
    (bounded : labels.length ≤ budget) (compare : ShorterCallbackSlices profile ready base bindings budget) :
    CollectionRunSlice profile ready base bindings older destination inst type element entries index output checkNext canonNext
      start incoming check canon labels finish seen visit :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.driveCollectionSlice
    body same width actual bounded compare

open PayloadPrefix LinkedCallback.MemorySequence in
/-- Traverse a reached `list<string>` allocation using the actual residual.
Each successful string publication supplies the growth and reached continuations
for the next element. A finite callback cut keeps its exact installed mark. -/
theorem drive_string_list_body (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (index pointer bytes : Nat) (output : Stored.Lower.Output) {root : Field} {schema : Stored.TypeOf} {budget : Nat}
    (rootLayout : root.LayoutMatches schema)
    (fits : Stored.Lower.fits Quirks.none destination.encoding destination.width schema root.value = true)
    (allocates : Field.AllocatorFor destination.realloc root)
    (path : root.Descendant (.dynamic (.list (.prim .string)) (.prim .string) entries))
    (matched : Field.LayoutMatches (.dynamic (.list (.prim .string)) (.prim .string) entries) (.list (.prim .string)))
    (emitted : Field.Emitted (.dynamic (.list (.prim .string)) (.prim .string) entries))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (width : (core3 grow).memAddrType? start.store.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? start.store.core destination.memory = some bytes)
    (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon) :
    let element : Stored.TypeOf := .prim .string
    let area := layout destination.width element
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.list element) output
    pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
    start.ctl = check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) →
    incoming.ctl = canon.control (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) →
    Steps profile ready (specDispatch ready base) start labels finish → labels.length ≤ budget →
    ShorterCallbackSlices profile ready base bindings budget →
    StringRunSlice profile ready base bindings older
      (fun _ lhs rhs cursor peer => ∃ value, LinkedCallback.ChildFrameOver older lhs rhs cursor peer ∧
        Core3.Grows start.store.core lhs.store.core ∧ lhs.ctl = cursor.control (checkNext (.ok value)) ∧ rhs.ctl = peer.control (canonNext value))
      start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.driveStringListBody
    destination inst entries index pointer bytes output rootLayout fits allocates path matched emitted embedder width sized checkNext canonNext frame

open PayloadPrefix LinkedCallback.MemorySequence in
/-- Compose the executed post-pop range, every reached string element and the
list descriptor while preserving the original checked residual and trails. -/
theorem drive_string_list_after_range (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (index pointer bytes : Nat) (output : Stored.Lower.Output) {root : Field} {schema : Stored.TypeOf} {budget : Nat}
    (rootLayout : root.LayoutMatches schema)
    (fits : Stored.Lower.fits Quirks.none destination.encoding destination.width schema root.value = true)
    (allocates : Field.AllocatorFor destination.realloc root)
    (path : root.Descendant (.dynamic (.list (.prim .string)) (.prim .string) entries))
    (matched : Field.LayoutMatches (.dynamic (.list (.prim .string)) (.prim .string) entries) (.list (.prim .string)))
    (emitted : Field.Emitted (.dynamic (.list (.prim .string)) (.prim .string) entries))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    {check canon : Cursor (E := core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {checked canonical trailing : Trace grow sig}
    (frame : LinkedCallback.ChildFrameOver older left right check canon)
    (split : labels = checked ++ trailing) (seen : visible checked = visible canonical)
    (width : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (grown : Core3.Grows start.store.core left.store.core)
    (bounded : labels.length ≤ budget) (compare : ShorterCallbackSlices profile ready base bindings budget) :
    let element : Stored.TypeOf := .prim .string
    let area := layout destination.width element
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.list element) output
    pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
    left.ctl = check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) →
    right.ctl = canon.control (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) →
    AlignedCollectionRange profile ready base bindings start incoming left right checked canonical [] trailing finish →
    (∃ remaining, remaining ≠ [] ∧ Steps profile ready (specDispatch ready base) finish remaining left) ∨
    StringRunSlice profile ready base bindings older
      (fun _ lhs rhs cursor peer => ∃ value, LinkedCallback.ChildFrameOver older lhs rhs cursor peer ∧
        Core3.Grows start.store.core lhs.store.core ∧ lhs.ctl = cursor.control (checkNext (.ok value)) ∧ rhs.ctl = peer.control (canonNext value))
      start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.driveStringListAfterRange
    destination inst entries index pointer bytes output rootLayout fits allocates path matched emitted embedder checkNext canonNext
    frame split seen width sized grown bounded compare

open PayloadPrefix LinkedCallback.MemorySequence in
/-- Once the admitted list's range is actually reached, consume the nominal
element suffix in order. Publication is entered only after every element
returns; a guard refusal leaves canonical at the exact unexecuted suffix. -/
theorem drive_nominal_list_body (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (entries : List Field) (index pointer : Nat) (output : Stored.Lower.Output)
    (nominal : NominalElement element)
    (matched : Field.LayoutMatches (.dynamic (.list element) element entries) (.list element))
    (emitted : Field.Emitted (.dynamic (.list element) element entries))
    (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon) :
    let area := layout destination.width element
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.list element) output
    start.ctl = check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) →
    incoming.ctl = canon.control (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) →
    Steps profile ready (specDispatch ready base) start labels finish →
    AllocatedElementRun profile ready base bindings older checkNext canonNext
      (ElementStop destination inst entries area.size pointer
        (publishCanonical destination inst pointer entries.length output canonNext)) check canon start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.driveNominalListBody
    destination inst element entries index pointer output nominal matched emitted checkNext canonNext frame

open PayloadPrefix LinkedCallback.MemorySequence in
/-- Use the executed range split from `LiveCollectionOccurrenceEntry.drive_actual`.
The body never runs when the checked prefix ends inside the range. -/
theorem drive_nominal_list_after_range (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (entries : List Field) (index pointer : Nat) (output : Stored.Lower.Output)
    (nominal : NominalElement element)
    (matched : Field.LayoutMatches (.dynamic (.list element) element entries) (.list element))
    (emitted : Field.Emitted (.dynamic (.list element) element entries))
    (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    {check canon : Cursor (E := core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {checked canonical trailing : Trace grow sig}
    (frame : LinkedCallback.ChildFrameOver older left right check canon)
    (split : labels = checked ++ trailing) (seen : visible checked = visible canonical) :
    let area := layout destination.width element
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.list element) output
    left.ctl = check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) →
    right.ctl = canon.control (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) →
    AlignedCollectionRange profile ready base bindings start incoming left right checked canonical [] trailing finish →
    (∃ remaining, remaining ≠ [] ∧ Steps profile ready (specDispatch ready base) finish remaining left) ∨
    AllocatedElementRun profile ready base bindings older checkNext canonNext
      (ElementStop destination inst entries area.size pointer
        (publishCanonical destination inst pointer entries.length output canonNext)) check canon start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.driveNominalListAfterRange
    destination inst element entries index pointer output nominal matched emitted checkNext canonNext frame split seen

/-- A reached marked collection return uses the live memory and claim table.
Both paths take the actual range checks under their respective dispatchers.
Invalid range traps both; valid range hands the checked suffix its fresh
verdict without running any children, and keeps the canonical entry mode. -/
theorem AllocatorMark.collection_range (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Field) (output : Stored.Lower.Output) (index pointer : Nat)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {canonStart checked canonical : Config (core3 grow) (HostState sig)}
    {checkEntry canonEntry cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let area := layout destination.width element
    let mode := CanonicalTree.EntryMode.forOutput destination.width type output
    let first := PayloadPrefix.checkedCollectionResume destination inst entries area index output checkNext
    let second := PayloadPrefix.canonicalCollectionResume destination inst entries area output canonNext mode
    AllocatorMark profile ready base bindings older
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start checkEntry first)
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        canonStart canonEntry second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer)) →
    (core3 grow).memAddrType? start.store.core destination.memory = some destination.width →
    Core3.Grows start.store.core checked.store.core →
    CollectionRangeCut profile ready base bindings older checked canonical cursor destination area entries.length pointer
      (Field.listObjects entries)
      (fun addr verdict => PayloadPrefix.checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext)
      (fun addr => PayloadPrefix.canonicalCollectionTail destination inst entries area output addr mode >>= canonNext) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.collectionRange
    destination inst type element entries output index pointer checkNext canonNext

/-- Finish a reached allocating list root on either scheduled public give
route. The compiler certificate determines the entries. The installed mark
and its lower-slot trail identify the original Core caller; a returned pointer
does not promise successful range checks, element writes or publication. -/
theorem AllocatorMark.local_list_replies {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field)
    (data : PayloadPrefix.LocalDataType element) (field : site.field = .dynamic (.list element) element entries) (pointer : Nat)
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let area := layout site.destination.width element
    let first := PayloadPrefix.checkedCollectionResume site.destination site.inst entries area 0 route.output site.reply
    let second := PayloadPrefix.canonicalCollectionResume site.destination site.inst entries area route.output site.referenceReply
    AllocatorMark profile ready base bindings older
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    CollectionReplies profile ready base bindings older site checked canonical
      (PayloadPrefix.canonicalCollectionTail site.destination site.inst entries area route.output pointer >>= site.referenceReply) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.localListReplies
    site linked element entries data field pointer

/-- Compare every compiled nominal list element after the actual allocator
return on either public give route. Live guards run in sequence against the
reached writer and store. The descriptor is published only after all children
return; a refusal rejoins only the checked caller at the reached stop. -/
theorem AllocatorMark.nominal_list_replies {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field)
    (nominal : NominalElement element) (field : site.field = .dynamic (.list element) element entries) (pointer : Nat)
    (admitted : OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let area := layout site.destination.width element
    let first := PayloadPrefix.checkedCollectionResume site.destination site.inst entries area 0 route.output site.reply
    let second := PayloadPrefix.canonicalCollectionResume site.destination site.inst entries area route.output site.referenceReply
    AllocatorMark profile ready base bindings older
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    CollectionSegmentReplies profile ready base bindings older site checked canonical
      (ListReturnStop site.destination site.inst entries area route.output pointer site.referenceReply) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.nominalListReplies
    site linked element entries nominal field pointer admitted

/-- Replay a reached memory-map return through every compiled data entry,
descriptor writes, and the original public `givePayload` caller reply.
The canonical offsets are those selected when the allocation was installed. -/
theorem AllocatorMark.local_map_replies {outputPointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory outputPointer))
    (linked : site.Linked bindings) (key : WIT.KeyType) (element : Stored.TypeOf) (entries : List Field)
    (keyData : PayloadPrefix.LocalDataType (.prim key.toPrimitive)) (valueData : PayloadPrefix.LocalDataType element)
    (field : site.field = .dynamic (.map key element) (.record (mapEntryFields key element)) entries) (pointer : Nat)
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let area := layout site.destination.width (.record (mapEntryFields key element))
    let mode := CanonicalTree.EntryMode.memoryMap site.destination.width key element
    let output := (GiveEffectRoute.memory outputPointer).output
    let first := PayloadPrefix.checkedCollectionResume site.destination site.inst entries area 0 output site.reply
    let second := PayloadPrefix.canonicalCollectionResume site.destination site.inst entries area output site.referenceReply mode
    AllocatorMark profile ready base bindings older
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    CollectionReplies profile ready base bindings older site checked canonical
      (PayloadPrefix.canonicalCollectionTail site.destination site.inst entries area output pointer mode >>= site.referenceReply) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.localMapReplies
    site linked key element entries keyData valueData field pointer

/-- Replay local string effects and finite classified allocator prefixes at
both reached stores. Only a pop of the marked natural-pointer return enters
the smaller plan, with older frame substitutions and Core growth retained. -/
theorem string_plan_replay (cx : LiftLowerContext (core3 grow)) (pointer : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {origin : CStore (core3 grow)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (checkAt : left.ctl = check.control (runStoreSteps cx pointer steps >>= checkNext))
    (canonAt : right.ctl = canon.control (runStoreSteps cx pointer steps >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {ends : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop}
    (finish : ∀ pointer lhs rhs check canon, LinkedCallback.ChildFrameOver older lhs rhs check canon →
      Core3.Grows origin.core lhs.store.core → lhs.ctl = check.control (checkNext pointer) →
      rhs.ctl = canon.control (canonNext pointer) → ends pointer lhs rhs check canon) :
    LiveStringReplay profile ready base bindings older cx checkNext canonNext ends steps.length left right check canon :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.stringReplay
    cx pointer steps checkNext canonNext frame growth checkAt canonAt embedder finish

/-- Drive the compiled string field with the actual checked run. A finite
callback can leave the allocation open; only a matched, executed pop of the
installed occurrence advances to the smaller plan. -/
theorem StringValueThen.drive_actual {destination : RecordDestination} {inst : InstId} {key : LinkedCallback.StringField}
    {output : Stored.Lower.Output} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output}
    {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output} {budget : Nat}
    {describe : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop}
    (field : StringValueThen profile ready base bindings older destination inst key output start incoming check canon checkNext canonNext describe)
    (actual : Steps profile ready (specDispatch ready base) start labels finish)
    (bounded : labels.length ≤ budget) (compare : ShorterCallbackSlices profile ready base bindings budget) :
    StringRunSlice profile ready base bindings older describe start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.driveStringValue field actual bounded compare

/-- Continue past allocation only through the actual memory descriptor
write or flat emission, returning its checked residual at the reached state. -/
theorem StringValueThen.drive_commit {destination : RecordDestination} {inst : InstId} {key : LinkedCallback.StringField}
    {output : Stored.Lower.Output} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output}
    {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output} {budget : Nat}
    {published : LinkedCallback.MemorySequence.ValueFinish grow sig output}
    (field : StringValueThen profile ready base bindings older destination inst key output start incoming check canon checkNext canonNext
      (fun _ => LiveValueCommit profile ready base bindings output checkNext canonNext published))
    (actual : Steps profile ready (specDispatch ready base) start labels finish)
    (bounded : labels.length ≤ budget) (compare : ShorterCallbackSlices profile ready base bindings budget) :
    StringRunSlice profile ready base bindings older
      (fun _ lhs rhs cursor peer => ∃ value, published value lhs rhs cursor peer) start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.driveStringCommit field actual bounded compare

/-- Extend an already reached occurrence pair through every reached string
instruction and classified allocator cut, including repeated marked returns. -/
theorem string_plan_occurrences {cx : LiftLowerContext (core3 grow)}
    {checkNext canonNext : Nat → Session grow sig (Ret (core3 grow))}
    {leftStart rightStart left right : Config (core3 grow) (HostState sig)}
    {ends : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop}
    {finish : Nat → Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig}
    {length : Nat} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {seen : Trace grow sig}
    (leading : ComparedOccurrencePaths profile ready base bindings leftStart rightStart seen left right)
    (run : LiveStringReplay profile ready base bindings older cx checkNext canonNext ends length left right check canon)
    (next : ∀ pointer observed lhs rhs cursor peer, ends pointer lhs rhs cursor peer →
      ComparedOccurrencePaths profile ready base bindings leftStart rightStart observed lhs rhs →
      finish pointer observed lhs rhs cursor peer) :
    LiveStringOccurrences profile ready base bindings older cx checkNext canonNext leftStart rightStart finish length left right check canon seen :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.stringOccurrences leading run next

/-- Extend the incoming occurrence paths through a reached string field, or
through the placed string key of a map, and its actual decreasing plan. -/
theorem string_value_occurrence_paths {destination : RecordDestination} {inst : InstId} {key : LinkedCallback.StringField}
    {output : Stored.Lower.Output} {left right : Config (core3 grow) (HostState sig)}
    {seen : Trace grow sig}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output}
    {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output}
    {ends : Nat → LinkedCallback.MemorySequence.Finish grow sig}
    {finish : Nat → Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig}
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (run : StringValueThen profile ready base bindings older destination inst key output left right check canon checkNext canonNext ends)
    (next : ∀ pointer observed lhs rhs cursor peer, ends pointer lhs rhs cursor peer →
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs → finish pointer observed lhs rhs cursor peer) :
    StringValueOccurrencePaths profile ready base bindings older destination inst key output start incoming left right check canon
      checkNext canonNext finish seen :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.stringValueOccurrencePaths leading run next

/-- Compare the actual string-key plan in either map placement mode. Static
fit and allocator availability follow the compiled descendant path. Compare
finite classified callback prefixes; only the reached marked return resumes
the residual plan. The live descriptor precedes the value continuation. -/
theorem string_map_key (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) (key : LinkedCallback.StringField) (value root : Field) {schema : Stored.TypeOf}
    (layoutRoot : root.LayoutMatches schema)
    (fitRoot : Stored.Lower.fits Quirks.none destination.encoding destination.width schema root.value = true)
    (allocator : Field.AllocatorFor destination.realloc root)
    (path : Field.Descendant root (.aggregate (.record (mapEntryFields .string element)) [key.field, value]))
    (origin : CStore (core3 grow)) (basePtr bytes count entryIndex issueIndex : Nat)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout destination.width (.record (mapEntryFields .string element))).alignment)
    (bounds : basePtr + count * (layout destination.width (.record (mapEntryFields .string element))).size ≤ bytes)
    (entry : entryIndex < count)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core right.store.core)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let cx := destination.context inst
    let type : Stored.TypeOf := .record (mapEntryFields .string element)
    let ptr := basePtr + entryIndex * (layout destination.width type).size
    let keySlot := fun reached => alignTo ptr (layout reached key.field.type).alignment
    let valueSlot := fun keyWidth reached => alignTo
      (keySlot keyWidth + (layout keyWidth key.field.type).size) (layout reached value.type).alignment
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) output
    let afterKey := fun keyWidth (_ : Unit) => mapFieldPlacement cx mode fun reached =>
      CanonicalTree.field Limits.spec Quirks.none cx destination.width value (.memory (valueSlot keyWidth reached)) >>= canonNext
    let following := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
      | .error issue => pure (.error issue)
      | .ok () => OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1
          (.memory (valueSlot destination.width destination.width))) >>= fun result => checkNext (result.mapError (.nested issueIndex))
    left.ctl = check.control (OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
      (.aggregate type [key.field, value]) issueIndex (.memory ptr) >>= checkNext) →
    right.ctl = canon.control (mapFieldPlacement cx mode fun reached =>
      CanonicalTree.field Limits.spec Quirks.none cx destination.width key.field (.memory (keySlot reached)) >>= afterKey reached) →
    StringKeyReplay profile ready base bindings older origin destination inst key (keySlot destination.width) left right check canon
      following (afterKey destination.width) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.stringMapKey
    destination inst element output key value root layoutRoot fitRoot allocator path origin basePtr bytes count entryIndex issueIndex
    width sized aligned bounds entry checkNext canonNext frame growth embedder

/-- After the real key descriptor, check the nominal value against the
reached store and writer. A late refusal stops before canonical value
placement, while a later trap retains the descriptor and earlier effects. -/
theorem string_key_nominal_value (origin : CStore (core3 grow)) (destination : RecordDestination) (inst : InstId)
    (element : Stored.TypeOf) (output : Stored.Lower.Output) (key : LinkedCallback.StringField) (value : Field) (address issueIndex : Nat)
    (nominal : NominalElement element) (matched : value.LayoutMatches element) (emitted : value.Emitted)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} :
    StringKeyNominalValue profile ready base bindings older origin destination inst element output key value address issueIndex
      left right check canon checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.stringKeyNominalValue
    origin destination inst element output key value address issueIndex nominal matched emitted width checkNext canonNext

/-- Accumulate actual paired paths and occurrence trails from string replay.
Finite callback prefixes compare at the reached states without popping;
only the marked return can advance the residual plan. -/
theorem LiveStringReplay.paths {cx : LiftLowerContext (core3 grow)}
    {checkNext canonNext : Nat → Session grow sig (Ret (core3 grow))}
    {leftStart rightStart : Config (core3 grow) (HostState sig)}
    {first : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop}
    {second : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Trace grow sig → Prop}
    (next : ∀ ptr lhs rhs check canon seen, first ptr lhs rhs check canon →
      ComparedSlots profile ready base bindings leftStart rightStart seen lhs rhs → second ptr lhs rhs check canon seen)
    {length : Nat} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {seen : Trace grow sig}
    (leading : ComparedSlots profile ready base bindings leftStart rightStart seen left right)
    (run : LiveStringReplay profile ready base bindings older cx checkNext canonNext first length left right check canon) :
    LiveStringPaths profile ready base bindings older cx checkNext canonNext leftStart rightStart second length left right check canon seen :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.stringPaths next leading run

/-- Derive the selected string key, nominal value and allocator option from
the linked public compiler result. Compare the actual entry programs under
the two dispatchers, after a successful root fit and reached range check. -/
theorem linked_string_map_entry {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field) (index : Fin entries.length)
    (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    (fits : Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
    (origin : CStore (core3 grow)) (basePtr bytes : Nat)
    (width : (core3 grow).memAddrType? origin.core site.destination.memory = some site.destination.width)
    (sized : (core3 grow).memSize? origin.core site.destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout site.destination.width (.record (mapEntryFields .string element))).alignment)
    (bounds : basePtr + entries.length * (layout site.destination.width (.record (mapEntryFields .string element))).size ≤ bytes)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core right.store.core)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    LinkedStringMapEntry profile ready base bindings older site element entries index origin basePtr left right check canon
      checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedStringMapEntry
    site linked element entries index nominal field fits origin basePtr bytes width sized aligned bounds checkNext canonNext frame growth embedder
      _ (fun _ _ _ _ _ grown _ _ => grown)

/-- Compare every reached string-key nominal map entry in either public
give. Advance only on actual returns, retaining the stopped value suffix,
the reached trap, or the finite classified allocator prefix at each entry. -/
theorem linked_string_map_traversal {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field) (index : Nat)
    (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    (fits : Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
    (origin : CStore (core3 grow)) (basePtr bytes : Nat)
    (width : (core3 grow).memAddrType? origin.core site.destination.memory = some site.destination.width)
    (sized : (core3 grow).memSize? origin.core site.destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout site.destination.width (.record (mapEntryFields .string element))).alignment)
    (bounds : basePtr + entries.length * (layout site.destination.width (.record (mapEntryFields .string element))).size ≤ bytes)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core right.store.core)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (atSuffix : LinkedStringMapAt site element entries index basePtr left right check canon checkNext canonNext) :
    LinkedStringMapTraversal profile ready base bindings older site element entries index origin basePtr left right check canon
      checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedStringMapTraversal
    site linked element entries index nominal field fits origin basePtr bytes width sized aligned bounds checkNext canonNext frame growth embedder atSuffix
      _ (fun _ _ _ _ _ _ _ => trivial)

/-- After the outer range and fresh preparation succeed, compare the actual
recursive map body through descriptor publication. Refused or suspended
children cannot enter the descriptor; a descriptor trap retains reached writes. -/
theorem linked_string_map_body {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field)
    (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    (fits : Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
    (basePtr bytes : Nat)
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (width : (core3 grow).memAddrType? left.store.core site.destination.memory = some site.destination.width)
    (sized : (core3 grow).memSize? left.store.core site.destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout site.destination.width (.record (mapEntryFields .string element))).alignment)
    (bounds : basePtr + entries.length * (layout site.destination.width (.record (mapEntryFields .string element))).size ≤ bytes)
    (frame : LinkedCallback.ChildFrameOver older left right check canon)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let area := layout site.destination.width (.record (mapEntryFields .string element))
    let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map .string element) route.output
    left.ctl = check.control (PayloadPrefix.checkedCollectionTail site.destination site.inst entries area 0 route.output basePtr (.ok ()) >>= site.reply) →
    right.ctl = canon.control (PayloadPrefix.canonicalCollectionTail site.destination site.inst entries area route.output basePtr mode >>= site.referenceReply) →
    LinkedStringMapBody profile ready base bindings older site element entries basePtr left right check canon :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedStringMapBody
    site linked element entries nominal field fits basePtr bytes width sized aligned bounds frame embedder

/-- Follow the marked outer allocator return through reached alignment, bounds,
and fresh preparation. An invalid range traps without reply; typed preparation
refusal replies on checked only. A successful check starts the recursive map
body with exact visible range prefixes and the original caller occurrence. -/
theorem AllocatorMark.string_map_return {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field)
    (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    (fits : Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
    (pointer : Nat) (admitted : OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace}
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let entryType : Stored.TypeOf := .record (mapEntryFields .string element)
    let area := layout site.destination.width entryType
    let output := route.output
    let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map .string element) output
    let first := PayloadPrefix.checkedCollectionResume site.destination site.inst entries area 0 output site.reply
    let second := PayloadPrefix.canonicalCollectionResume site.destination site.inst entries area output site.referenceReply mode
    AllocatorMark profile ready base bindings older
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    LinkedStringMapReturn profile ready base bindings older site element entries pointer checked canonical check :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedStringMapReturn
    site linked element entries nominal field fits pointer admitted embedder

/-- Track the actual reached nominal guard, spend and store. A refusal
keeps the canonical field pending; a reached trap keeps earlier effects. -/
theorem reached_handle_field_paths {item : Field} {index address offset : Nat}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig}
    (leading : ComparedSlots profile ready base bindings start incoming labels left right offset)
    (same : left.store = right.store)
    (run : LinkedCallback.HandleFieldThenBetween profile ready (specDispatch ready base)
      (specDispatch ready (LiveDispatch.host bindings base)) item index (.memory address) left right check canon
      checkNext canonNext (fun () => finish))
    (next : ∀ seen lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming seen lhs rhs offset →
      finish lhs rhs cursor peer → visit seen lhs rhs cursor peer) :
    HandlePathsThen profile ready base bindings start incoming labels offset item index checkNext visit left right check :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.handleFieldPaths leading same run
    (fun _ _ _ _ _ _ _ _ _ _ => True.intro) True.intro
    (fun seen lhs rhs cursor peer tracks _ => next seen lhs rhs cursor peer tracks)

/-- Carry the key's actual allocator and descriptor path into the value,
including the width read of the reached canonical placement. -/
theorem LiveStringMapEntryThen.paths {destination : RecordDestination} {inst : InstId} {element : Stored.TypeOf}
    {output : Stored.Lower.Output} {field value : Field} {index slot offset : Nat}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {compare : LinkedCallback.MemorySequence.FieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : Nat → TrailFinish grow sig}
    (leading : ComparedSlots profile ready base bindings start incoming labels left right offset)
    (run : LiveStringMapEntryThen profile ready base bindings older destination inst element output
      field value index slot compare checkNext canonNext finish left right check canon)
    (next : ∀ ptr seen lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming seen lhs rhs offset → lhs.store = rhs.store →
      compare value 1 ptr lhs rhs cursor peer (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish →
      visit ptr seen lhs rhs cursor peer) :
    LiveStringMapEntryPaths profile ready base bindings older destination inst element output start incoming labels offset
      field value index slot checkNext canonNext visit left right check canon :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.stringMapEntryPaths leading run next

/-- Compose actual bounds and width reads with the certified child programs
of a heterogeneous record or tuple, without a per-child trace premise. -/
theorem leaf_aggregate_field_lifts {destination : RecordDestination} {inst : InstId} {type : Stored.TypeOf} {offset : Nat}
    (leaves : TrailLeafAggregate type) :
    LiftsFieldPaths profile ready base bindings start incoming offset
      (liveCollectionField profile ready base bindings older destination inst type)
      (aggregateFieldPaths profile ready base bindings destination inst type
        (liveLeafPaths profile ready base bindings older destination inst start incoming offset)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.leafAggregateLift leaves

/-- Lift the reached scalar, string and nominal memory programs to an
all-location continuation, distinguishing a checked refusal from a trap. -/
theorem memory_leaf_occurrence_lift {destination : RecordDestination} {inst : InstId} {type : Stored.TypeOf} {sink : RefusalSink grow sig}
    (covers : sink.CoversOccurrences profile ready base bindings start incoming) (leaf : TrailLeafType type) :
    LiftsFieldOccurrencePaths profile ready base bindings start incoming
      (liveCollectionField profile ready base bindings older destination inst type)
      (leafOccurrencePaths profile ready base bindings older destination inst start incoming sink type) sink :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.leafOccurrenceLift covers leaf

/-- Accumulate every occurrence through actual canonical sibling focus
and the reached compiled child. A stop or a trap never advances siblings. -/
theorem memory_sequence_occurrence_paths {mode : LinkedCallback.MemorySequence.Track}
    {destination : RecordDestination} {inst : InstId}
    {child : LinkedCallback.MemorySequence.FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    {entries : List Field} {index address : Nat} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {sink : RefusalSink grow sig} {seen : Trace grow sig}
    (lift : LiftsFieldOccurrencePaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (same : left.store = right.store)
    (run : LinkedCallback.MemorySequence.ReplayBetween profile ready (specDispatch ready (LiveDispatch.host bindings base))
      mode destination inst child checkNext canonNext finish entries index address left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    replayBetweenPaths profile ready base bindings mode destination inst paths checkNext canonNext visit
      entries index address seen left right check canon :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.replayBetweenOccurrencePathsFrom
    lift leading same run admitted next

/-- Fold the enclosing-mark invariant through the actual canonical sibling
focus reads and the reached child continuations. -/
theorem memory_sequence_occurrence_transport {mode : LinkedCallback.MemorySequence.Track}
    {destination : RecordDestination} {inst : InstId}
    {child : LinkedCallback.MemorySequence.FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    {entries : List Field} {index address : Nat} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {sink : RefusalSink grow sig} {seen : Trace grow sig}
    (lift : LiftsFieldTransportPaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (run : LinkedCallback.MemorySequence.ReplayBetween profile ready (specDispatch ready (LiveDispatch.host bindings base))
      mode destination inst child checkNext canonNext finish entries index address left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    replayBetweenPaths profile ready base bindings mode destination inst paths checkNext canonNext visit
      entries index address seen left right check canon :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.replayBetweenTransportFrom
    lift leading run admitted next

/-- Transport the incoming invariant through the actual descriptor program.
An actual trap preserves the reached store and does not enter the visitor. -/
theorem descriptor_occurrence_transport {output : Stored.Lower.Output}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output}
    {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output}
    {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {finish : LinkedCallback.MemorySequence.ValueFinish grow sig output} {visit : TrailFinish grow sig} {seen : Trace grow sig}
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (run : LiveValueCommit profile ready base bindings output checkNext canonNext finish left right check canon)
    (next : ∀ value observed lhs rhs cursor peer,
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs →
      finish value lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    LocalTransportThen profile ready base bindings start incoming seen visit :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.RecursiveTrails.descriptorTransport leading run next

/-- Carry all enclosing marks through a reached string-key map entry,
including any indirect placement read before the value's program. -/
theorem string_map_entry_occurrence_transport {destination : RecordDestination} {inst : InstId} {element : Stored.TypeOf}
    {output : Stored.Lower.Output} {field value : Field} {index slot : Nat}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {compare : LinkedCallback.MemorySequence.FieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : Nat → TrailFinish grow sig} {seen : Trace grow sig}
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (run : LiveStringMapEntryThen profile ready base bindings older destination inst element output
      field value index slot compare checkNext canonNext finish left right check canon)
    (next : ∀ ptr observed lhs rhs cursor peer,
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs →
      compare value 1 ptr lhs rhs cursor peer (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish →
      visit ptr observed lhs rhs cursor peer) :
    StringMapEntryTransport profile ready base bindings older destination inst element output start incoming visit
      field value index slot checkNext canonNext seen left right check canon :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.stringMapEntryTransport leading run next

/-- Start the all-location induction from the actual compiler and linked
entry, then execute the original Core caller's successful return only if
its installed occurrence survives at the reached reply slot. -/
theorem linked_memory_transport_body {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (linked : site.Linked bindings) (family : RecursiveCollectionType (sig.payload site.tag))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {incoming : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedMemoryTransportBody profile ready base bindings older site incoming) base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedMemoryTransportBody site linked family paired selected embedder

/-- Align the derived occurrence paths with the actual checked execution.
The next dispatch sees only the residual after the executed original pop. -/
theorem align_public_transport_worker {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {callees : List (ComponentCall.Callee sig)} {entered left right : Config (core3 grow) (HostState sig)}
    {checkEntry canonEntry seen : Trace grow sig} {value : route.output.Result}
    (body : PublicSuccessTransport profile ready (ComponentCall.hostWithComponent bindings callees) bindings older
      site incoming entered checkEntry canonEntry value seen left right)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) site.start labels finish) :
    PublicTransportWorkerAlignment profile ready bindings callees older site incoming left right checkEntry canonEntry seen labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.alignPublicTransportWorker site body run

/-- Derive the worker cut from the linked memory request and its actual
checked run. At a reached success, only an executed original caller pop
exposes a shorter suffix and the next fixed-dispatch boundary. -/
theorem linked_memory_worker_body {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    {callees : List (ComponentCall.Callee sig)}
    (linked : site.Linked bindings) (family : RecursiveCollectionType (sig.payload site.tag))
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : (ComponentCall.hostWithComponent bindings callees).embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) site.start labels finish) :
    PayloadRoot.Cut site profile ready bindings (LinkedMemoryWorkerBody profile ready bindings callees older site incoming labels finish)
      (ComponentCall.hostWithComponent bindings callees) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedMemoryWorkerBody
    site linked family paired selected embedder run

/-- Derive the flat worker cut with the actual emitted words and recursive
body paths. Only a surviving and executed original caller pop releases a
shorter checked residual; late typed refusals keep the stopped canonical site. -/
theorem linked_flat_worker_body {type : Stored.TypeOf} (site : PayloadRoot.Site grow sig (.flat type))
    {callees : List (ComponentCall.Callee sig)}
    (linked : site.Linked bindings) (family : RecursiveCollectionType (sig.payload site.tag))
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : (ComponentCall.hostWithComponent bindings callees).embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) site.start labels finish) :
    PayloadRoot.Cut site profile ready bindings (LinkedFlatWorkerBody profile ready bindings callees older site incoming labels finish)
      (ComponentCall.hostWithComponent bindings callees) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedFlatWorkerBody
    site linked family paired selected embedder run

/-- Apply the recursive memory or flat visitor to the checked tail at the
extracted installation. An actual common reply carries enclosing occurrences
into the next classified worker cut; a late typed reply is checked-only. -/
theorem GiveInstall.actual_selected_give {route : GiveEffectRoute} {request : CoreGiveRequest bindings start}
    (selection : request.Selected route) {callees : List (ComponentCall.Callee sig)} {label}
    {next : Config (core3 grow) (HostState sig)}
    (install : GiveInstall bindings (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start label next)
    (tail : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) next labels finish)
    (family : RecursiveGiveDomain selection) (paired : HostFrame.Related.Paired older start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle = some selection.tree) :
    ActualSelectedGive profile ready callees selection older incoming (label :: labels) finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.actualSelectedGive selection install tail family paired selected

/-- Derive every child lift by induction on the compiled recursive memory
schema, including heterogeneous fields and the selected sum arm. No child
histories are supplied as premises. -/
theorem recursive_allocating_occurrence_transport {destination : RecordDestination} {inst : InstId} {type : Stored.TypeOf}
    {sink : RefusalSink grow sig} (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (family : RecursiveAllocatingTransportType type) :
    LiftsFieldTransportPaths profile ready base bindings start incoming
      (liveCollectionField profile ready base bindings older destination inst type)
      (recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink type) sink :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.RecursiveTrails.recursiveAllocatingTransport covers family

/-- Heterogeneous records and tuples select the scalar, string or nominal
child rule from the compiled slot's declared schema. The actual bounds read,
each reached sibling and its eventual stop carry the cumulative history. -/
theorem memory_leaf_aggregate_occurrences {destination : RecordDestination} {inst : InstId} {type : Stored.TypeOf}
    {sink : RefusalSink grow sig} (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (leaves : TrailLeafAggregate type) :
    LiftsFieldOccurrencePaths profile ready base bindings start incoming
      (liveCollectionField profile ready base bindings older destination inst type)
      (aggregateFieldPaths profile ready base bindings destination inst type
        (leafOccurrencePaths profile ready base bindings older destination inst start incoming sink)) sink :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.leafAggregateOccurrenceLift covers leaves

/-- Derive cumulative occurrence paths through compiled fixed strides,
heterogeneous fields and the selected arm of each sum. The reached leaf
program supplies effects and stops; the schema supplies the child rule. -/
theorem structural_memory_occurrences {destination : RecordDestination} {inst : InstId} {type : Stored.TypeOf}
    {sink : RefusalSink grow sig} (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (family : StructuralMemoryOccurrenceType type) :
    LiftsFieldOccurrencePaths profile ready base bindings start incoming
      (liveCollectionField profile ready base bindings older destination inst type)
      (structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink type) sink :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.RecursiveTrails.structuralFieldOccurrences covers family

/-- Extend a cumulative history through a reached dynamic allocation,
including the exact stopped canonical suffix on fresh reservation failure. -/
theorem collection_entry_occurrences {destination : RecordDestination} {inst : InstId} {type element : Stored.TypeOf}
    {entries : List Field} {index : Nat} {output : Stored.Lower.Output}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output}
    {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {visit : Nat → Nat → LinkedCallback.MemorySequence.Finish grow sig} {path : Nat → Nat → TrailFinish grow sig}
    {sink : RefusalSink grow sig} (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming labels left right)
    (run : LiveCollectionEntry profile ready base bindings older destination inst type element entries index output checkNext canonNext
      left right check canon (fun pointer bytes _ => visit pointer bytes))
    (next : ∀ pointer bytes observed lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs →
      visit pointer bytes lhs rhs cursor peer → path pointer bytes observed lhs rhs cursor peer) :
    LiveCollectionOccurrenceEntry profile ready base bindings older destination inst type element entries index output checkNext canonNext
      start incoming left right labels check canon path sink :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.RecursiveTrails.collectionEntryOccurrences covers admitted leading run next

/-- Track active and saved occurrences through the actual tag store. A tag
trap takes neither branch; successful entry uses only the selected child. -/
theorem LiveSumThen.paths {destination : RecordDestination} {inst : InstId}
    {child : LinkedCallback.MemorySequence.FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    {arms : List (Option Stored.TypeOf)} {selected : Option Field} {index address offset : Nat}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (lift : selected.isSome = true → LiftsFieldPaths profile ready base bindings start incoming offset child paths)
    (leading : ComparedSlots profile ready base bindings start incoming labels left right offset)
    (run : LiveSumThen profile ready base bindings destination inst child arms selected index address
      checkNext canonNext finish left right check canon)
    (next : ∀ seen lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming seen lhs rhs offset → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit seen lhs rhs cursor peer) :
    LocatedLocalPathsThen profile ready base bindings start incoming left right labels offset
      (match selected with
      | none => visit
      | some item => paths item 0 (PayloadPrefix.sumPayloadAddress destination.width arms address)
          (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext visit) := by
  cases selected <;> exact
    Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.sumPathsFrom lift leading run True.intro next

/-- Compare the reached string-key nominal map paths through the original public
caller rejoins. A finite suspended key keeps its accumulated occurrence path;
late refusal rejoins only checked and traps execute neither reply. -/
theorem AllocatorMark.string_map_paths {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field)
    (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    (fits : Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
    (pointer : Nat) (admitted : OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace}
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let entryType : Stored.TypeOf := .record (mapEntryFields .string element)
    let area := layout site.destination.width entryType
    let output := route.output
    let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map .string element) output
    let first := PayloadPrefix.checkedCollectionResume site.destination site.inst entries area 0 output site.reply
    let second := PayloadPrefix.canonicalCollectionResume site.destination site.inst entries area output site.referenceReply mode
    AllocatorMark profile ready base bindings older
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    LinkedStringMapReturnPaths profile ready base bindings older site element entries pointer checked canonical check :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedStringMapReturnPaths
    site linked element entries nominal field fits pointer admitted embedder

/-- Use the real linked admission and canonical entry on either public
string-key nominal map route. The placed branch compares classified finite
allocator prefixes; only a marked return can feed the caller rejoins. -/
theorem linked_string_map_dispatch {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field) (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedStringMapDispatch profile ready base bindings older site element entries incoming)
      base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedStringMapDispatch
    site linked element entries nominal field paired selected embedder

/-- Traverse the actual map lowering for either public give after a reached allocator return.
The compiler determines each scalar key and nominal value; successful keys
remain written if a later value refuses or traps. Flat entries read the
reached width at their own field boundaries; memory entries use the captured
width. Only a completed map publishes the descriptor and rejoins both callers. -/
theorem AllocatorMark.nominal_map_replies {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (key : WIT.KeyType) (element : Stored.TypeOf) (entries : List Field)
    (keyData : PayloadPrefix.LocalDataType (.prim key.toPrimitive)) (nominal : NominalElement element)
    (field : site.field = .dynamic (.map key element) (.record (mapEntryFields key element)) entries) (pointer : Nat)
    (admitted : OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let entryType : Stored.TypeOf := .record (mapEntryFields key element)
    let area := layout site.destination.width entryType
    let output := route.output
    let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map key element) output
    let first := PayloadPrefix.checkedCollectionResume site.destination site.inst entries area 0 output site.reply
    let second := PayloadPrefix.canonicalCollectionResume site.destination site.inst entries area output site.referenceReply mode
    AllocatorMark profile ready base bindings older
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    CollectionSegmentReplies profile ready base bindings older site checked canonical
      (MapReturnStop site.destination site.inst key element entries output pointer site.referenceReply) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.nominalMapReplies
    site linked key element entries keyData nominal field pointer admitted

/-- At a reached owner, endpoint, or error-context leaf, use the live
checked writer, not the enclosing dry run. Neither branch dispatches a
callback at this leaf. A checked refusal leaves canonical before the leaf;
after a successful check the actual spend survives a later canonical trap. -/
theorem reached_handle_field (destination : RecordDestination) (inst : InstId) (item : Field) (handle : CanonicalHandle item)
    (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {origin : CStore (core3 grow)} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (checkAt : left.ctl = check.control (OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width item output >>= canonNext)) :
    LinkedCallback.HandleFieldThenBetween profile ready (specDispatch ready base) (specDispatch ready (LiveDispatch.host bindings base))
      item index output left right check canon checkNext canonNext (fun value reached reference lhs rhs =>
        LinkedCallback.ChildFrameOver older reached reference lhs rhs ∧ Core3.Grows origin.core reached.store.core ∧
        reached.ctl = lhs.control (checkNext (.ok value)) ∧ reference.ctl = rhs.control (canonNext value)) :=
  frame.handle_field_then_between destination inst item handle index output checkNext canonNext growth checkAt canonAt
    (fun _ _ _ _ _ related grown lhs rhs => ⟨related, grown, lhs, rhs⟩)

/-- On a valid reached range with failed live preparation, execute exactly
the checked refusal reply. This applies to the actual map entry mode as
well as ordinary list placement; canonical never enters those children. -/
theorem CollectionRangeCut.refused_reply {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (type element : Stored.TypeOf) (entries : List Field) (index pointer bytes : Nat)
    {checked canonical : Config (core3 grow) (HostState sig)} {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {leading issue} :
    let area := layout site.destination.width element
    let child := PayloadPrefix.canonicalCollectionTail site.destination site.inst entries area route.output pointer
      (CanonicalTree.EntryMode.forOutput site.destination.width type route.output) >>= site.referenceReply
    let reply := route.reply site.destination site.start.host.nextTicket
      (.error (LinkedCallback.CollectionVisit.afterAllocation index issue))
    CollectionRangeCut profile ready base bindings older checked canonical check site.destination area entries.length pointer
      (Field.listObjects entries)
      (fun addr live => PayloadPrefix.checkedCollectionTail site.destination site.inst entries area index route.output addr live >>= site.reply)
      (fun addr => PayloadPrefix.canonicalCollectionTail site.destination site.inst entries area route.output addr
        (CanonicalTree.EntryMode.forOutput site.destination.width type route.output) >>= site.referenceReply) →
    ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready base) site.checked (.active 0 0) leading checked (.active 0 1) →
    (core3 grow).memSize? checked.store.core site.destination.memory = some bytes →
    pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
    Stored.OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .error issue →
    ∃ (canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (checkedLabels canonLabels : Trace grow sig)
      (segments : List (Seg (core3 grow) (HostState sig))),
      (∀ label ∈ checkedLabels, label = .tau) ∧ (∀ label ∈ canonLabels, label = .tau) ∧
      Steps profile ready (specDispatch ready base) checked (checkedLabels ++ [.tau, .tau, .tau])
        { checked with
          host := checked.host.record reply.1
          ctl := ⟨check.thread, .core ((core3 grow).resume checked.store.core site.core (.values reply.2)) site.resume,
            segments⟩ :: check.rest } ∧
      ReturnFrame.Occurrence.RetainsBelowTop profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical canonLabels
        { canonical with ctl := canon.control child } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.refusalReply site type element entries index pointer bytes

theorem NestedPlan.source (plan : NestedPlan bindings profile ready base start labels finish) :
    Steps profile ready (specDispatch ready base) start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.source plan

/-- Decompose an actual prefix at its reached foci. Local steps replay fully;
nonlocal steps still go through the live request/read/return classifier. -/
theorem NestedPlan.of_steps (run : Steps profile ready (specDispatch ready base) start labels finish) :
    NestedPlan bindings profile ready base start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.planOfSteps run

/-- Derive a closed reentry edge at the reached caller and binding under the
same component dispatcher used by the worker. No checked body, padding,
or older-frame equality is supplied by the caller of the theorem. -/
theorem linked_closed_give_plan {callees : List (ComponentCall.Callee sig)} (callout : LinkedCallback.ClosedGive bindings start) :
    ∃ count, NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) start
      (List.replicate count .tau) callout.resume :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.closedGivePlan callout rfl

/-- Reuse the allocator's finite callback classification rather than
flattening closed reentries and classified readiness reads into raw steps.
The endpoint may still be parked. Unclassified steps retain the ordinary
live replay boundaries. -/
theorem NestedPlan.of_callback_prefix {protectedReturn}
    (path : LinkedCallback.PrefixFor profile ready bindings protectedReturn start labels finish) :
    ∃ trace, NestedPlan bindings profile ready (Scheduled.host bindings) start trace finish ∧
      PayloadPrefix.visible trace = labels :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.callbackPlan path

/-- Lift the very trace used to track an allocator occurrence, not another
prefix with the same visible labels. The resulting plan still classifies
ordinary steps at the live dispatcher boundary. -/
theorem NestedPlan.of_callback_trace {right reference : Config (core3 grow) (HostState sig)} {referenceLabels}
    (trace : LinkedCallback.ReplayTrace profile ready bindings start labels finish right referenceLabels reference) :
    NestedPlan bindings profile ready (Scheduled.host bindings) start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.callbackPlanExact trace

/-- The substituted canonical body has its own exact callback classifications,
including the actual confined caller and readiness read at each reentry. -/
theorem NestedPlan.of_callback_peer {right reference : Config (core3 grow) (HostState sig)} {referenceLabels}
    (trace : LinkedCallback.ReplayTrace profile ready bindings start labels finish right referenceLabels reference) :
    NestedPlan bindings profile ready (Scheduled.host bindings) right referenceLabels reference :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.callbackPeerPlanExact trace

/-- Lift the exact classified reference trace to the fixed component worker
dispatcher. The actual confined reentry cannot invoke a direct dispatch,
and each readiness read keeps its own reached agreement. Unclassified
segments can still end at an explicit dispatch lookup boundary. -/
theorem linked_callback_peer_plan {right reference : Config (core3 grow) (HostState sig)} {referenceLabels}
    {callees : List (ComponentCall.Callee sig)}
    (trace : LinkedCallback.ReplayTrace profile ready bindings start labels finish right referenceLabels reference) :
    CallbackOverlayPlan bindings profile ready callees right referenceLabels reference ∨
      CallbackOverlayCut bindings profile ready callees right referenceLabels reference :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedCallbackPeer trace

/-- Extract the canonical body plan from a reached public give comparison.
It uses the same trace as the recursive traversal and does not rebuild a plan
from unclassified steps. Component-only dispatch extensions are not asserted
compatible by this theorem. -/
theorem rejoined_give_body_plan {route : GiveEffectRoute} {site : PayloadRoot.Site grow sig route}
    {value : route.output.Result} {checked reference : Config (core3 grow) (HostState sig)}
    (comparison : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings checked reference) :
    ∃ checkLabels referenceLabels,
      Steps profile ready (specDispatch ready (Scheduled.host bindings)) site.checked checkLabels checked ∧
      NestedPlan bindings profile ready (Scheduled.host bindings) (site.reference site.referenceReply) referenceLabels reference ∧
      PayloadPrefix.visible checkLabels = PayloadPrefix.visible referenceLabels :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.rejoinedBodyPlan comparison

/-- At the reached linked memory give, use the public entry guards and the
compiled recursive body. A preflight refusal becomes a checked reply and a
stopped live canonical prefix, not a canonical error. A placement trap is
also a stopped prefix: canonical store requires valid root placement. -/
theorem linked_memory_admission {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} :
    ∃ depth, RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedRejoinedMemory site depth profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.memoryAdmission site linked

/-- The flat ABI uses the same admission split and the recursive flat body
with its actual memory-emitting descendants. -/
theorem linked_flat_admission {schema : Stored.TypeOf} (site : PayloadRoot.Site grow sig (.flat schema))
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} :
    ∃ flatDepth entryDepth, RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedRejoinedFlat site flatDepth entryDepth profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.flatAdmission site linked

/-- Join a recursive public give's reached checked and canonical bodies to
the actual caller replies. This constructs the replay plan from the compared
paths; it does not assume that a reached nested callout can be replayed. -/
theorem compared_give_plan {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {entryLabels checkLabels canonLabels reached reference checked baseline} (value : route.output.Result)
    (entry : Transition profile ready base site.start (.give route .entered) entryLabels site.checked)
    (left : Steps profile ready (specDispatch ready base) site.checked checkLabels reached)
    (right : Steps profile ready (specDispatch ready base) (site.reference site.referenceReply) canonLabels reference)
    (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels)
    (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline) :
    NestedPlan bindings profile ready base site.start (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.comparedGive
    site linked value entry left right seen replies

/-- For either recursive public give that reaches its successful caller
rejoin, build the session plan on the Core binding dispatcher without a
separate child/body plan. Finite checked refusal and trap are not successful
rejoins. When run live, an intervening nested give may still cut the plan. -/
theorem rejoined_give_plan {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {entryLabels reached reference} (value : route.output.Result)
    (entry : Transition profile ready (Scheduled.host bindings) site.start (.give route .entered) entryLabels site.checked)
    (compared : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference) :
    ∃ checkLabels checked baseline,
      NestedPlan bindings profile ready (Scheduled.host bindings) site.start (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked ∧
      LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.rejoinedGive site linked value entry compared

/-- Classify the successful recursive rejoin under the worker's linked
dispatcher. No agreement premise is needed at ordinary allocation, local
operations or Core callouts. An unequal direct install is exposed at its
actual common-prefix cut, not converted to a refusal or canonical trap. -/
theorem linked_rejoined_give_plan {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {callees : List (ComponentCall.Callee sig)} {entryLabels reached reference} (value : route.output.Result)
    (entry : Transition profile ready (ComponentCall.hostWithComponent bindings callees)
      site.start (.give route .entered) entryLabels site.checked)
    (compared : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference) :
    LinkedGiveExit bindings profile ready callees site entryLabels value reached reference :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedRejoinedGive site linked value entry compared

/-- Derive entry and the recursive success continuation at the reached memory
give. The caller supplies neither a body comparison nor a replay plan. -/
theorem linked_memory_exit {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} :
    ∃ depth, RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedMemoryBody site depth profile ready bindings (fun reached reference =>
        ∃ entryLabels, LinkedGiveExit bindings profile ready callees site entryLabels () reached reference)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedMemoryExit site linked

/-- The flat give specializes the same reached-entry construction, with its
computed ABI words in the returned comparison. -/
theorem linked_flat_exit {schema : Stored.TypeOf} (site : PayloadRoot.Site grow sig (.flat schema))
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} :
    ∃ flatDepth entryDepth, RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedFlatResult site flatDepth entryDepth profile ready bindings (fun value reached reference =>
        ∃ entryLabels, LinkedGiveExit bindings profile ready callees site entryLabels value reached reference)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedFlatExit site linked

/-- At a reached Core give with successful ABI selection, compute the
compiler outcome and obtain the corresponding public checked path. If the
body is entered, its recursive continuation comes from the actual compiler,
without a supplied body comparison or replay plan. -/
theorem CoreGiveRequest.Selected.linked_admission {route : GiveEffectRoute} {request : CoreGiveRequest bindings start}
    (selection : request.Selected route) {callees : List (ComponentCall.Callee sig)} :
    ReachedGiveAdmission profile ready callees selection :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.reachedGiveAdmission selection

/-- Reach both sides of the compiler boundary under the linked worker
dispatchers. Compilation supplies the checked refusal or recursive exit;
the canonical side is at the actual pending program, not a status reply. -/
theorem CoreGiveRequest.Selected.paired_linked_admission {route : GiveEffectRoute} {request : CoreGiveRequest bindings start}
    (selection : request.Selected route) {callees : List (ComponentCall.Callee sig)}
    (paired : HostFrame.Related.Paired older start incoming)
    (reads : ∀ handle, request.lookupDemand = some handle →
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted handle) :
    ∃ entryLabels entered, entryLabels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming entryLabels entered ∧
      HostFrame.Related.Paired older selection.canonicalPending entered ∧
      ReachedGiveAdmission profile ready callees selection :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.pairedLinkedAdmission selection paired reads

/-- Follow a classified delivery interleaving to an actually selected give.
The reached lookup and compiler cut follow from the starting accepted
observations even when the interleaving registered new roots. -/
theorem CoreGiveRequest.Selected.linked_admission_after_interleaving {route : GiveEffectRoute}
    {request : CoreGiveRequest bindings finish} (selection : request.Selected route)
    {callees : List (ComponentCall.Callee sig)} {actions incoming outgoing}
    (between : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      start incoming actions labels finish outgoing)
    (roots : incoming.writer.accepted = start.host.writer.accepted) :
    ∃ entryLabels canonical, entryLabels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
        (HostFrame.replace start incoming) (labels ++ entryLabels) canonical ∧
      HostFrame.Related.Paired (fun _ _ => False) selection.canonicalPending canonical ∧
      canonical.host.writer.accepted = finish.host.writer.accepted ∧
      ReachedGiveAdmission profile ready callees selection :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedAdmissionAfterInterleaving selection between roots

/-- A closed allocator prefix that reaches another selected give derives the
live lookup from the observations at entry to the prefix. The nested canonical
emitter is installed with all older frames still paired; the reached checked
compiler determines the next branch. The nested body is not assumed equivalent. -/
theorem ClosedCallbackPrefix.linked_admission {route : GiveEffectRoute} {request : CoreGiveRequest bindings finish}
    (selection : request.Selected route) {callees : List (ComponentCall.Callee sig)} {protectedReturn}
    (path : ClosedCallbackPrefix bindings profile ready (ComponentCall.hostWithComponent bindings callees)
      protectedReturn start labels finish)
    (covers : ∀ first second, older first second → protectedReturn first)
    (paired : HostFrame.Related.Paired older start incoming)
    (roots : start.host.writer.accepted = incoming.host.writer.accepted) :
    ∃ checkedLabels canonLabels entryLabels canonical,
      Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start checkedLabels finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming (canonLabels ++ entryLabels) canonical ∧
      PayloadPrefix.visible checkedLabels = labels ∧ PayloadPrefix.visible (canonLabels ++ entryLabels) = labels ∧
      HostFrame.Related.Paired older selection.canonicalPending canonical ∧
      canonical.host.writer.accepted = finish.host.writer.accepted ∧ ReachedGiveAdmission profile ready callees selection :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedAdmissionAfterCallback
    selection path covers paired roots

/-- When the checked compiler refuses, only that side rejoins the caller.
The canonical run ends before its emitter; neither side undoes the
interleaving and their accepted observations agree at the cut. -/
theorem CoreGiveRequest.Selected.compiler_refusal_after_interleaving {route : GiveEffectRoute}
    {request : CoreGiveRequest bindings finish} (selection : request.Selected route)
    {callees : List (ComponentCall.Callee sig)} {actions incoming outgoing}
    (between : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      start incoming actions labels finish outgoing)
    (roots : incoming.writer.accepted = start.host.writer.accepted) {issue : Stored.Endpoints.RecordLower.Issue}
    (refused : selection.preflight = .error issue) :
    ∃ count entryLabels canonical, entryLabels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        start (labels ++ List.replicate count .tau) (selection.compilerRefused issue) ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
        (HostFrame.replace start incoming) (labels ++ entryLabels) canonical ∧
      HostFrame.Related.Paired (fun _ _ => False) selection.canonicalPending canonical ∧
      canonical.host.writer.accepted = (selection.compilerRefused issue).host.writer.accepted :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.compilerRefusalAfterInterleaving selection between roots refused

/-- The reached compiler refusal is a finite session edge. On the live
canonical side, replay stops before the emitter, including when the
checked path continues after its typed Core reply. -/
theorem CoreGiveRequest.Selected.compiler_refusal_plan {route : GiveEffectRoute} {request : CoreGiveRequest bindings start}
    (selection : request.Selected route) {issue : Stored.Endpoints.RecordLower.Issue}
    (refused : selection.preflight = .error issue)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    ∃ count, NestedPlan bindings profile ready base start (List.replicate count .tau) (selection.compilerRefused issue) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.compilerRefusalPlan selection refused embedder

/-- Classify the actual matched body prefix of a typed refusal or canonical
trap. Reaching a refusal does not pop a canonical caller or emit its checked
error there. A canonical trap is compared with its reached store, not the
entry store. Neither branch requires an unvisited callback suffix. -/
theorem linked_stopped_give_plan {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {callees : List (ComponentCall.Callee sig)} {entryLabels checkLabels canonLabels reached reference check phase}
    (entry : Transition profile ready (ComponentCall.hostWithComponent bindings callees)
      site.start (.give route .entered) entryLabels site.checked)
    (left : Steps profile ready (Dispatch.coreOnly ready bindings) site.checked checkLabels reached)
    (right : Steps profile ready (Dispatch.coreOnly ready bindings) (site.reference site.referenceReply) canonLabels reference)
    (stop : GiveStop site check phase canonLabels reached reference) (store : reached.store = reference.store)
    (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels) :
    NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) site.start
        (entryLabels ++ checkLabels) reached ∨
      Dispatch.LookupCut profile ready bindings callees site.checked checkLabels reached ∨
      Dispatch.LookupCut profile ready bindings callees (site.reference site.referenceReply) canonLabels reference :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedGiveStop
    site linked entry left right stop store seen

/-- Classify the actual finite callback of a public give, preserving active,
saved and absent occurrence marks. An absent mark is not evidence of return.
The canonical plan keeps the already executed classified edges without a
premise that the allocator makes further progress. -/
theorem linked_allocator_cut {route : GiveEffectRoute} {site : PayloadRoot.Site grow sig route}
    {callees : List (ComponentCall.Callee sig)} {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {beforeCheck beforeCanon left right reached reference : Config (core3 grow) (HostState sig)}
    {checkEntryLabels canonEntryLabels checkLabels canonLabels mark}
    (cut : AllocatorCut profile ready bindings older changes left right reached reference checkLabels canonLabels mark)
    (checkEntry : Dispatch.Compatible profile ready bindings callees site.checked checkEntryLabels beforeCheck)
    (canonEntry : Dispatch.Compatible profile ready bindings callees (site.reference site.referenceReply) canonEntryLabels beforeCanon)
    (seenEntry : PayloadPrefix.visible checkEntryLabels = PayloadPrefix.visible canonEntryLabels)
    (checkInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCheck [.tau, .tau, .tau] left)
    (canonInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCanon [.tau, .tau] right) :
    let checkTrace := checkEntryLabels ++ [.tau, .tau, .tau] ++ checkLabels
    let canonTrace := canonEntryLabels ++ [.tau, .tau] ++ canonLabels
    (Transition profile ready (ComponentCall.hostWithComponent bindings callees) site.checked
        (.give route (.allocatorPrefix mark)) checkTrace reached ∧
      NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees)
        (site.reference site.referenceReply) canonTrace reference ∧
      PayloadPrefix.visible checkTrace = PayloadPrefix.visible canonTrace) ∨
      CallbackOverlayCut bindings profile ready callees left checkLabels reached ∨
      CallbackOverlayCut bindings profile ready callees right canonLabels reference :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedAllocatorCut
    cut checkEntry canonEntry seenEntry checkInstall canonInstall

/-- A closed local segment replays to the end, even with a different host and
older paired continuations. It leaves both hosts' accepted observations and
claims unchanged: the reached foci exclude host updates as well as reads and
callouts. No corresponding frame is implied for a callback. -/
theorem local_segment_replay (run : PayloadPrefix.LocalSteps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ reached, Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming labels reached ∧
      HostFrame.Related.Paired older finish reached ∧ finish.host = start.host ∧ reached.host = incoming.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.replayLocal run paired

/-- Descend through compared nested bodies, then continue from the actual
caller rejoin with the reached host. Only the completed case has the full
checked observable trace as a guarantee. A cut records a reached configuration
and a matching observable prefix, not execution of the unvisited suffix. -/
theorem NestedPlan.runs (plan : NestedPlan bindings profile ready base start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ trace reached, Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming trace reached ∧
      PayloadPrefix.visible trace <+: PayloadPrefix.visible labels ∧
      ((PayloadPrefix.visible labels = PayloadPrefix.visible trace ∧ HostFrame.Related.Paired older finish reached) ∨
        NestedCut bindings profile ready base older reached) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.runs plan paired

/-- Join actual argument lowering and Core entry to a classified body,
worker completion and delivery under one linked dispatcher. The body may
contain nested gives; it is selected only at the reached Core entry. An
argument trap or suspension instead ends the finite plan before entry. -/
theorem stackful_worker_plan {reached first : Config (core3 grow) (HostState sig)} {site : OnStartSite start} {handoff : LowerStartAt site}
    {returned : LowerArgumentReturn handoff reached} {callees : List (ComponentCall.Callee sig)}
    (args : CalleeArguments returned) {Result : Type} (words : Result → List FlatValue)
    (lowered : StringPlanPair profile ready bindings callees first (fun result => args.enter (words result)))
    (asyncMode : args.record.opts.async_ = true) (callback : args.record.opts.callback = none)
    (body : ∀ (entry : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue),
      entry.ctl = ⟨cursor.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), cursor.frames⟩ :: cursor.rest →
      ∃ bodyLabels afterBody exitLabels afterExit deliveryLabels last,
        NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) entry bodyLabels afterBody ∧
        StackfulBodyEnd args.task afterBody exitLabels afterExit ∧
        (∀ (site : StackfulReturn afterBody), site.segments = []) ∧
        NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) afterExit deliveryLabels last) :
    ∃ leading entry trailing last,
      Steps profile ready (Dispatch.linked ready bindings callees) first leading entry ∧
      NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) first (leading ++ trailing) last ∧
      ((∃ (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue),
          entry.ctl = ⟨cursor.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), cursor.frames⟩ :: cursor.rest ∧
          NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) entry trailing last) ∨
        (StringPlanStopped profile ready bindings first leading entry ∧ trailing = [] ∧ last = entry)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.stackfulWorker
    args words lowered asyncMode callback body

/-- A placed public memory or flat give with a nonallocating data root has
its body comparison derived from the compiled field and linked width.
It rejoins the original Core caller on success; a canonical trap instead
keeps the common reached store and does not issue a completion reply. -/
theorem local_data_give_plan {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    (data : PayloadPrefix.LocalDataType (sig.payload site.tag)) (payload : Stored.Payload (sig.payload site.tag))
    (field : site.field = .data (sig.payload site.tag) payload) {entryLabels}
    (entryPath : Steps profile ready (specDispatch ready base) site.start entryLabels site.checked)
    (silent : PayloadPrefix.visible entryLabels = [])
    (placed : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok ())
    (prepared : Stored.OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ()) :
    ∃ bodyLabels reached, NestedPlan bindings profile ready base site.start (entryLabels ++ bodyLabels) reached ∧
      ((∃ value checkedLabels atReply,
        Steps profile ready (specDispatch ready base) site.checked checkedLabels atReply ∧
        atReply.ctl = site.cursor.control (site.reply (.ok value)) ∧ bodyLabels = checkedLabels ++ [.tau, .tau, .tau] ∧
        reached.host = atReply.host.record (route.reply site.destination site.start.host.nextTicket (.ok value)).1) ∨
      (reached.ctl = [] ∧ ∃ leading reason, PayloadPrefix.visible bodyLabels = leading ++ [.trap reason])) := by
  obtain ⟨labels, reached, plan, outcome, _⟩ := Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.localDataGive
    site linked data payload field entryPath silent placed prepared
  exact ⟨labels, reached, plan, outcome⟩

/-- Compare the actual checked and live canonical paths of a placed
nonallocating data give, through caller rejoin or a common canonical trap.
The closed body maintains accepted observations without requiring equal
host journals or discarding writes at a trap. -/
theorem paired_local_data_give {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    (data : PayloadPrefix.LocalDataType (sig.payload site.tag)) (payload : Stored.Payload (sig.payload site.tag))
    (field : site.field = .data (sig.payload site.tag) payload) {entryLabels}
    (entryPath : Steps profile ready (specDispatch ready base) site.start entryLabels site.checked)
    (silent : PayloadPrefix.visible entryLabels = [])
    (placed : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok ())
    (prepared : Stored.OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    (paired : HostFrame.Related.Paired older site.start incoming)
    (roots : site.start.host.writer.accepted = incoming.host.writer.accepted) :
    ∃ checkLabels canonLabels checked canonical,
      Steps profile ready (specDispatch ready base) site.start checkLabels checked ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonLabels canonical ∧
      HostFrame.Related.Paired older checked canonical ∧ PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧
      checked.host.writer.accepted = canonical.host.writer.accepted :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.pairedLocalDataGive
    site linked data payload field entryPath silent placed prepared paired roots

/-- A successfully selected Core request can compare its actual recursive
emitter under the live dispatcher. Only the reached handle lookup must
agree; the journal, claims, and allocator callbacks need not be identical. -/
theorem CoreGiveRequest.Selected.recursive_give {route : GiveEffectRoute} {request : CoreGiveRequest bindings start}
    (selection : request.Selected route) {callees : List (ComponentCall.Callee sig)}
    (family : RecursiveGiveDomain selection)
    (paired : HostFrame.Related.Paired older start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle = some selection.tree) :
    ReachedRecursiveGive profile ready callees selection older incoming :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.reachedRecursiveGive
    selection family paired selected

/-- Compare the actual closed prefix up to a nested Core give, then use
its reached root to derive the recursive body paths under the same live
dispatcher. An unequal reached lookup is a boundary, not a type error.
No equality of entire journals or allocator progress is required. -/
theorem ClosedCallbackPrefix.recursive_give_or_lookup {route : GiveEffectRoute} {request : CoreGiveRequest bindings finish}
    (selection : request.Selected route) {callees : List (ComponentCall.Callee sig)} {protectedReturn}
    (path : ClosedCallbackPrefix bindings profile ready (ComponentCall.hostWithComponent bindings callees)
      protectedReturn start labels finish)
    (covers : ∀ first second, older first second → protectedReturn first)
    (paired : HostFrame.Related.Paired older start incoming)
    (family : RecursiveGiveDomain selection) :
    ∃ checkedLabels canonLabels reached,
      Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start checkedLabels finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming canonLabels reached ∧
      PayloadPrefix.visible checkedLabels = labels ∧ PayloadPrefix.visible canonLabels = labels ∧
      HostFrame.Related.Paired older finish reached ∧
      (Stored.Endpoints.Core.childFromHistory start.host.writer.accepted selection.handle =
        Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle →
        ReachedRecursiveGive profile ready callees selection older reached) ∧
      (ReachedRecursiveGive profile ready callees selection older reached ∨
        Stored.Endpoints.Core.childFromHistory reached.host.writer.accepted selection.handle ≠ some selection.tree) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.recursiveGiveAfterCallback
    selection path covers paired family

/-- Closed commit, poll, wait, cancel, and tick segments lead to the actual
next give under the same dispatcher. The lookup is derived at that point
from the accepted observations at entry, not from an assumed retained event
or equality of the reached journals. -/
theorem CoreGiveRequest.Selected.recursive_give_after_interleaving {route : GiveEffectRoute}
    {request : CoreGiveRequest bindings finish} (selection : request.Selected route)
    {callees : List (ComponentCall.Callee sig)} {actions prior outgoing}
    (between : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      start prior actions labels finish outgoing)
    (roots : prior.writer.accepted = start.host.writer.accepted) (family : RecursiveGiveDomain selection) :
    Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish ∧
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
      (HostFrame.replace start prior) labels (HostFrame.replace finish outgoing) ∧
    ReachedRecursiveGive profile ready callees selection (fun _ _ => False) (HostFrame.replace finish outgoing) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.recursiveGiveAfterInterleaving
    selection between roots family

/-- Refine a reached give-installation cut from paired replay. The actual
linked selector determines the route, ABI refusal, or caller trap. Open
lookups and direct program calls remain explicit, not fabricated errors. -/
theorem GiveInstall.recursive_request_cut {callees : List (ComponentCall.Callee sig)} {label}
    (install : GiveInstall bindings (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start label finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    DirectGiveAt bindings start ∨ ∃ request : CoreGiveRequest bindings start, RecursiveRequestCut profile ready callees request older incoming :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.recursiveInstallCut install paired

/-- The next give after a common reply is classified from its reached
install, not from a preselected route or replay of its checked-only body. -/
theorem RejoinedWorkerTail.classify {callees : List (ComponentCall.Callee sig)}
    (tail : RejoinedWorkerTail profile ready bindings callees older start incoming)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish) :
    ClassifiedWorkerTail profile ready bindings callees older start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.classifyReplay (tail.replay run)

open ReturnFrame.Occurrence in
/-- Follow the actual saved allocator occurrence through the common worker
prefix. The next install is classified before its body, or the replay stops
at a reached read or substituted pop. A lost mark is not a return. -/
theorem AllocatorMark.classified_worker_tail {callees : List (ComponentCall.Callee sig)}
    {checkEntry canonEntry : Config (core3 grow) (HostState sig)} {checkTrace canonTrace : Trace grow sig}
    {mark : Option Location} {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (tracked : AllocatorMark profile ready (ComponentCall.hostWithComponent bindings callees) bindings older
      checkEntry canonEntry checkTrace canonTrace start incoming mark)
    (paired : HostFrame.Related.Paired (ReturnFrame.Extend older first second) start incoming)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish) :
    ClassifiedWorkerTail profile ready bindings callees (ReturnFrame.Extend older first second) start incoming labels finish
      (fun added left right => ∃ reached,
        AllocatorMark profile ready (ComponentCall.hostWithComponent bindings callees) bindings older checkEntry canonEntry
          (checkTrace ++ added) (canonTrace ++ added) left right reached) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.classifyAllocatorTail tracked paired run

open ReturnFrame.Occurrence in
/-- Resume the enclosing allocator only if its marked occurrence really
pops in the extracted residual after the nested give's common reply. -/
theorem RejoinedCallbackReplay.allocator_residual {callees : List (ComponentCall.Callee sig)}
    {request reference checkEntry canonEntry : Config (core3 grow) (HostState sig)}
    {checkTrace canonTrace checkPrefix canonPrefix : Trace grow sig} {mark : Option Location}
    {retained : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (replay : RejoinedCallbackReplay profile ready bindings callees older request reference start incoming
      checkPrefix canonPrefix labels finish)
    (tracked : AllocatorMark profile ready (ComponentCall.hostWithComponent bindings callees) bindings retained
      checkEntry canonEntry checkTrace canonTrace start incoming mark)
    (installed : segmentAt (segmentStorage canonEntry) (.active 0 0) = some (.prog second)) :
    RejoinedAllocatorResidual profile ready bindings callees retained checkEntry canonEntry start incoming
      checkTrace canonTrace labels finish first second :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.rejoinedAllocatorResidual replay tracked installed

open ReturnFrame.Occurrence in
/-- Accumulate the enclosing traversal's occurrences and the new allocator
mark through the same reached worker cut. A save, switch, or loss is traced
as such; the cut does not require either occurrence to return. -/
theorem ComparedAllocatorPaths.classified_worker_tail {callees : List (ComponentCall.Callee sig)}
    {checkEntry canonEntry leftStart rightStart : Config (core3 grow) (HostState sig)}
    {checkTrace canonTrace seen : Trace grow sig} {offset : Nat}
    {mark : Option Location} {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (tracked : AllocatorMark profile ready (ComponentCall.hostWithComponent bindings callees) bindings older
      checkEntry canonEntry checkTrace canonTrace start incoming mark)
    (enclosing : ComparedAllocatorPaths profile ready (ComponentCall.hostWithComponent bindings callees) bindings
      leftStart rightStart seen start incoming offset)
    (paired : HostFrame.Related.Paired (ReturnFrame.Extend older first second) start incoming)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish) :
    ClassifiedWorkerTail profile ready bindings callees (ReturnFrame.Extend older first second) start incoming labels finish
      (fun added left right => (∃ reached,
        AllocatorMark profile ready (ComponentCall.hostWithComponent bindings callees) bindings older checkEntry canonEntry
          (checkTrace ++ added) (canonTrace ++ added) left right reached) ∧
        ComparedAllocatorPaths profile ready (ComponentCall.hostWithComponent bindings callees) bindings
          leftStart rightStart (seen ++ PayloadPrefix.visible added) left right offset) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.classifyEnclosingAllocatorTail tracked enclosing paired run

/-- Execute the intervening delivery on the reached journals and classify
the next Core cut. The next selector runs against the updated journals; an
event may have been consumed or replaced before that selector is reached. -/
theorem RejoinedWorkerTail.classify_after_delivery {callees : List (ComponentCall.Callee sig)}
    (tail : RejoinedWorkerTail profile ready bindings callees older start incoming)
    (empty : ∀ first second, ¬ older first second) {actions reached outgoing queued done}
    (between : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      start incoming.host actions labels reached outgoing)
    (next : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) reached queued done) :
    Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels reached ∧
    Steps profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
      incoming labels (HostFrame.replace reached outgoing) ∧
    ClassifiedWorkerTail profile ready bindings callees (fun _ _ => False) reached (HostFrame.replace reached outgoing) queued done ∧
    (incoming.host.writer.accepted = start.host.writer.accepted → outgoing.writer.accepted = reached.host.writer.accepted) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.classifyAfterDelivery tail empty between next

/-- Align closed delivery with the actual checked residual. A common give
reply does not imply that delivery executes: a short prefix or scheduler
departure does not release the canonical delivery or a new worker tail. -/
theorem RejoinedWorkerTail.align_delivery {callees : List (ComponentCall.Callee sig)}
    {actions reached outgoing} {deliveryLabels : Trace grow sig}
    (tail : RejoinedWorkerTail profile ready bindings callees older start incoming)
    (empty : ∀ first second, ¬ older first second)
    (between : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      start incoming.host actions deliveryLabels reached outgoing)
    (actual : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish) :
    WorkerBodyAlignment profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
      start reached deliveryLabels labels finish ∧
    ∀ suffix, labels = deliveryLabels ++ suffix →
      Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) reached suffix finish ∧
      Steps profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming deliveryLabels (HostFrame.replace reached outgoing) ∧
      ClassifiedWorkerTail profile ready bindings callees (fun _ _ => False) reached (HostFrame.replace reached outgoing) suffix finish ∧
      (deliveryLabels ≠ [] → suffix.length < labels.length) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.alignDeliveryResidual tail empty between actual

open ReturnFrame.Occurrence in
/-- Both real public root entries follow the same push for every previously
installed occurrence, even though checked performs additional guard reads. -/
theorem PendingRecursiveRoot.coupled_entry {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {callees : List (ComponentCall.Callee sig)} {checkLabels : Trace grow sig}
    (checked : site.EntryPrefix profile ready (ComponentCall.hostWithComponent bindings callees) checkLabels site.checked)
    (pending : PendingRecursiveRoot profile ready bindings callees older site incoming) :
    ∃ canonLabels entered, PayloadPrefix.visible canonLabels = [] ∧
      CoupledOccurrencePaths profile ready (ComponentCall.hostWithComponent bindings callees) bindings
        site.start incoming checkLabels canonLabels site.checked entered :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.pendingCoupledEntry site checked pending

open ReturnFrame.Occurrence in
/-- Rebase the recursive allocator cut to the pre-callout public requests.
The body starts below the fresh public reply frame, so every previously
active slot uses the next depth in the traversal's derived certificate. -/
theorem ComparedAllocatorPaths.at_public_request {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {entered lhs rhs : Config (core3 grow) (HostState sig)} {checkedEntry canonEntry seen : Trace grow sig}
    (checked : site.EntryPrefix profile ready base checkedEntry site.checked)
    (canonical : ∀ place, Prefix profile ready (specDispatch ready (host bindings base))
      incoming place canonEntry entered (site.entryPlace place))
    (checkSilent : PayloadPrefix.visible checkedEntry = []) (canonSilent : PayloadPrefix.visible canonEntry = [])
    (suspended : ComparedAllocatorPaths profile ready base bindings site.checked entered seen lhs rhs) :
    ComparedAllocatorPaths profile ready base bindings site.start incoming seen lhs rhs :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.rebaseAllocatorAtRequest
    site checked canonical checkSilent canonSilent suspended

/-- The public request itself provides the initial all-location comparison;
the checked and canonical entry paths need not have the same raw length. -/
theorem PendingRecursiveRoot.compared_entry {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {callees : List (ComponentCall.Callee sig)} {checkLabels : Trace grow sig}
    (checked : site.EntryPrefix profile ready (ComponentCall.hostWithComponent bindings callees) checkLabels site.checked)
    (silent : PayloadPrefix.visible checkLabels = [])
    (pending : PendingRecursiveRoot profile ready bindings callees older site incoming) :
    ∃ entered, HostFrame.Related.Paired older (site.reference site.referenceReply) entered ∧ entered.host = incoming.host ∧
      ComparedOccurrencePaths profile ready (ComponentCall.hostWithComponent bindings callees) bindings
        site.start incoming [] site.checked entered :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.pendingComparedEntry site checked silent pending

/-- Rebase the reached allocator and range outcomes to the original
scheduled `givePayload` or `giveFlat`, including older saved occurrences.
The installed mark distinguishes a suspended or lost return from a pop. -/
theorem linked_public_collection_occurrences {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} {checkLabels : Trace grow sig}
    {type element : Stored.TypeOf} {entries : List Field}
    (field : site.field = .dynamic type element entries)
    (checked : site.EntryPrefix profile ready (ComponentCall.hostWithComponent bindings callees) checkLabels site.checked)
    (silent : PayloadPrefix.visible checkLabels = [])
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (prepared : Stored.OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ()) :
    PublicCollectionOccurrences profile ready bindings callees older site incoming type element entries :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.publicCollectionOccurrences
    site linked field checked silent paired selected prepared

/-- Classify a real delivery interleaving followed by worker execution at
the reached record. The cut may precede delivery completion if an open
boundary is reached; it does not assert retention of a consumed event. -/
theorem RequestWorkerTail.classify_after_delivery {callees : List (ComponentCall.Callee sig)}
    {request reference delivered queued : Config (core3 grow) (HostState sig)} {seen deliveryLabels workerLabels : Trace grow sig}
    {actions outgoing}
    (tail : RequestWorkerTail profile ready bindings callees older request reference seen start incoming)
    (delivery : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees) start incoming.host
      actions deliveryLabels delivered outgoing)
    (worker : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) delivered workerLabels queued) :
    ClassifiedWorkerTail profile ready bindings callees older start incoming (deliveryLabels ++ workerLabels) queued
      (fun added left right => RequestExitOccurrences profile ready (ComponentCall.hostWithComponent bindings callees)
        bindings request reference (seen ++ PayloadPrefix.visible added) left right) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.requestWorkerTailAfterDelivery tail delivery worker

/-- Consume repeated common ABI refusals in an actual finite checked run.
The remaining run begins at the first open or unhandled request, an early
prefix of a refusal, or a genuine scheduler boundary. -/
theorem RequestExitOccurrences.worker_refusals {callees : List (ComponentCall.Callee sig)}
    {request reference : Config (core3 grow) (HostState sig)} {seen : Trace grow sig}
    (arrived : RequestExitOccurrences profile ready (ComponentCall.hostWithComponent bindings callees) bindings
      request reference seen start incoming)
    (paired : HostFrame.Related.Paired older start incoming) :
    RequestWorkerRefusals profile ready bindings callees older request reference seen start incoming :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.requestWorkerRefusals arrived paired

/-- Trace actual checked delivery followed by a finite worker suffix,
without assuming that any original event survives delivery. -/
theorem RequestWorkerRefusals.after_delivery {callees : List (ComponentCall.Callee sig)}
    {request reference delivered done : Config (core3 grow) (HostState sig)} {seen deliveryLabels workerLabels : Trace grow sig}
    {actions outgoing}
    (tail : RequestWorkerRefusals profile ready bindings callees older request reference seen start incoming)
    (delivery : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees) start incoming.host
      actions deliveryLabels delivered outgoing)
    (worker : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) delivered workerLabels done) :
    WorkerRefusalRun profile ready bindings callees older request reference seen start incoming (deliveryLabels ++ workerLabels) done :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.requestWorkerRefusalsAfterDelivery tail delivery worker

/-- At the next actual selected request, a compiler refusal only returns
on the checked side. Rebase the canonical pending cursor and checked reply
from the prior worker cut, without replaying the checked-only suffix. -/
theorem CoreGiveRequest.Selected.compiler_stop_after_worker_prefix {callees : List (ComponentCall.Callee sig)} {route : GiveEffectRoute}
    {request : CoreGiveRequest bindings start} (selection : request.Selected route) {issue : Stored.Endpoints.RecordLower.Issue}
    {origin reference : Config (core3 grow) (HostState sig)} {seen : Trace grow sig}
    (refused : selection.preflight = .error issue)
    (paired : HostFrame.Related.Paired older start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle = some selection.tree)
    (arrived : RequestExitOccurrences profile ready (ComponentCall.hostWithComponent bindings callees) bindings
      origin reference seen start incoming)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish) :
    CompilerStopSuffix profile ready callees selection issue older origin reference incoming seen labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.compilerStopAfterWorkerPrefix
    selection refused paired selected arrived run

open ReturnFrame.Occurrence in
/-- Match a derived recursive body endpoint against the actual checked run.
Only a reached marked common pop couples older occurrences and extracts the
next actual callback prefix, including closed readiness reads. A typed reply
retains the stopped canonical body and never replays the checked suffix. -/
theorem PublicOccurrenceExit.align_worker {route : GiveEffectRoute} {site : PayloadRoot.Site grow sig route}
    {callees : List (ComponentCall.Callee sig)} {origin reference entered left right : Config (core3 grow) (HostState sig)}
    {checkLabels canonLabels prior seen : Trace grow sig} {verdict : Except Stored.Endpoints.RecordLower.Issue route.output.Result}
    (body : PublicOccurrenceExit profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site entered verdict seen left right)
    (checked : site.EntryPrefix profile ready (ComponentCall.hostWithComponent bindings callees) checkLabels site.checked)
    (canonical : ∀ place, Prefix profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
      incoming place canonLabels entered (site.entryPlace place))
    (checkQuiet : PayloadPrefix.visible checkLabels = []) (canonQuiet : PayloadPrefix.visible canonLabels = [])
    (arrived : RequestExitOccurrences profile ready (ComponentCall.hostWithComponent bindings callees) bindings
      origin reference prior site.start incoming)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) site.start labels finish) :
    PublicGiveWorkerAlignment profile ready bindings callees older site entered left right verdict
      origin reference incoming checkLabels canonLabels prior seen labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.alignPublicGiveWorker
    site checked canonical checkQuiet canonQuiet body arrived run

/-- The compiler's layout relation supplies the sum slot. Only the
selected compiled field needs a visitor shape. -/
theorem MemoryVisitShape.compiled_sum {type : Stored.TypeOf} {arms : List (Option Stored.TypeOf)} {tag : Nat} {selected : Option Field}
    (matched : Field.LayoutMatches (.sum type arms tag selected) type)
    (children : ∀ item, selected = some item → MemoryVisitShape item) : MemoryVisitShape (.sum type arms tag selected) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.compiledSumVisitShape matched children

/-- Run the flat visitor on an executed checked residual. Each sibling
starts at the actual returned focus and receives only the words that the
previous sibling produced. -/
theorem compiled_flat_visit {origin : CStore (core3 grow)} {root item : Field} {schema : Stored.TypeOf} {budget : Nat}
    (destination : RecordDestination) (inst : InstId) (shape : FlatVisitShape item)
    (rootLayout : root.LayoutMatches schema)
    (fits : Stored.Lower.fits Quirks.none destination.encoding destination.width schema root.value = true)
    (allocates : Field.AllocatorFor destination.realloc root) (path : root.Descendant item)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (compare : ShorterCallbackSlices profile ready base bindings budget) :
    FlatVisitField profile ready base bindings older origin destination inst budget item :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.driveCompiledFlat
    destination inst shape rootLayout fits allocates path embedder width compare

/-- Run a placed compiled visitor on the actual finite checked derivation.
Siblings and selected arms use the executed residual; a boundary or typed
refusal does not run a sibling or publish the enclosing value. -/
theorem compiled_memory_visit {origin : CStore (core3 grow)} {root item : Field} {schema : Stored.TypeOf} {budget bytes : Nat}
    (destination : RecordDestination) (inst : InstId) (address : Nat) (shape : MemoryVisitShape item)
    (rootLayout : root.LayoutMatches schema)
    (fits : Stored.Lower.fits Quirks.none destination.encoding destination.width schema root.value = true)
    (allocates : Field.AllocatorFor destination.realloc root) (path : root.Descendant item)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (placed : LinkedCallback.MemorySequence.SlotFits destination.width bytes item address)
    (compare : ShorterCallbackSlices profile ready base bindings budget) :
    MemoryVisitField profile ready base bindings older origin destination inst budget item address :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.driveCompiledMemory
    destination inst address shape rootLayout fits allocates path embedder width sized placed compare

/-- Consume the original direct program's checked field residual on either
public route. Compilation determines both visitor shape and canonical
field; only actual checked callback slices may advance the visitor. -/
theorem direct_give_placed_visit (request : GiveSelector bindings) (ticket : Nat)
    (selected : SelectionValue sig request.schema) (field : Field) (plan : List Object)
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (site : PairedComponentSite older start incoming check canon)
    (compiled : request.preflight (grow := grow) selected = .ok (field, plan))
    (linked : request.destination.check start.store = .ok ())
    (fit : request.selectedFits selected request.destination.width = true)
    (placed : request.selectedPlacement selected start.store = .ok ())
    (checkedAt : start.ctl = check.control (request.fieldContinuation ticket selected field))
    (canonAt : incoming.ctl = canon.control
      (referenceTail request.inst request.destination request.schema (.ok selected) >>= fun reply => pure (.flat reply)))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (run : Steps profile ready (specDispatch ready base) start labels finish) {budget : Nat}
    (bounded : labels.length ≤ budget) (compare : ShorterCallbackSlices profile ready base bindings budget) :
    DirectGiveVisitRun profile ready base bindings older request ticket start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.visitDirectGivePlaced
    request ticket selected field plan site compiled linked fit placed checkedAt canonAt embedder run bounded compare

/-- Consume the actual value-mode element residual after a validated
collection range. Run the descriptor write only after all elements return. -/
theorem compiled_memory_elements {origin : CStore (core3 grow)} {root : Field} {schema : Stored.TypeOf} {budget bytes : Nat}
    (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf) (entries : List Field) (index pointer address : Nat)
    (matching : Field.EntriesMatch entries element) (shapes : ∀ item ∈ entries, MemoryVisitShape item)
    (paths : ∀ item ∈ entries, root.Descendant item)
    (rootLayout : root.LayoutMatches schema)
    (fits : Stored.Lower.fits Quirks.none destination.encoding destination.width schema root.value = true)
    (allocates : Field.AllocatorFor destination.realloc root)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (width : (core3 grow).memAddrType? start.store.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? start.store.core destination.memory = some bytes)
    (aligned : pointer = alignTo pointer (layout destination.width element).alignment)
    (bounds : pointer + entries.length * (layout destination.width element).size ≤ bytes)
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon) (growth : Core3.Grows origin.core start.store.core)
    (checkAt : start.ctl = check.control (PayloadPrefix.checkedCollectionTail destination inst entries (layout destination.width element)
      index (.memory address) pointer (.ok ()) >>= checkNext))
    (canonAt : incoming.ctl = canon.control (PayloadPrefix.canonicalCollectionTail destination inst entries (layout destination.width element)
      (.memory address) pointer .value >>= canonNext))
    (actual : Steps profile ready (specDispatch ready base) start labels finish)
    (bounded : labels.length ≤ budget) (compare : ShorterCallbackSlices profile ready base bindings budget) :
    MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.driveCompiledMemoryElements
    destination inst element entries index pointer address matching shapes paths rootLayout fits allocates embedder width sized
    aligned bounds frame growth checkAt canonAt actual bounded compare

/-- Use the live public entry guards and the finite compiled memory visitor
to find the original marked reply in the actual checked residual. -/
theorem actual_memory_request {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (linked : site.Linked bindings) (shape : MemoryVisitShape site.field)
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (run : Steps profile ready (specDispatch ready base) site.start labels finish)
    (compare : ShorterCallbackSlices profile ready base bindings labels.length) :
    PayloadRoot.Cut site profile ready bindings (ActualMemoryRequestRun profile ready base bindings older site incoming labels finish) base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.actualMemoryRequest
    site linked shape paired selected embedder run compare

/-- Read the local callback cut from an actual placed request. This covers
unfinished entry, recursive body stops, and executed original caller replies. -/
theorem ActualMemoryRequestRun.callback {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (body : ActualMemoryRequestRun profile ready base bindings older site incoming labels finish)
    {label next} (install : GiveInstall bindings (specDispatch ready base) site.start label next) :
    CallbackSlice profile ready base bindings older site.start incoming labels finish := by
  obtain ⟨_, _, _, _, compare⟩ := body
  exact compare install

/-- Recover the recursive memory site from the successful compiler result
of the selected request at an actual give installation. -/
theorem GiveInstall.actual_selected_memory_request {pointer : FlatValue} {request : CoreGiveRequest bindings start}
    (selection : request.Selected (.memory pointer)) {field : Field} {plan label}
    {next : Config (core3 grow) (HostState sig)}
    (compiled : selection.preflight = .ok (field, plan))
    (install : GiveInstall bindings (specDispatch ready base) start label next)
    (tail : Steps profile ready (specDispatch ready base) next labels finish)
    (paired : HostFrame.Related.Paired older start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle = some selection.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (compare : ShorterCallbackSlices profile ready base bindings (label :: labels).length) :
    ∃ tag payload arity children, selection.tree = .tag ⟨tag, payload⟩ arity children ∧
      let site := selection.site tag payload arity children field
      site.Linked bindings ∧ PayloadRoot.Cut site profile ready bindings
        (ActualMemoryRequestRun profile ready base bindings older site incoming (label :: labels) finish) base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.actualSelectedMemoryRequest
    selection compiled install tail paired selected embedder compare

/-- Cross an actually installed memory give whose live selection agrees.
Compiler and root refusals keep the canonical emitter pending; the placed
case uses the recursive visitor and its genuinely shorter callback runs. -/
theorem GiveInstall.actual_selected_memory_callback {pointer : FlatValue} {request : CoreGiveRequest bindings start}
    (selection : request.Selected (.memory pointer)) {label next}
    (install : GiveInstall bindings (specDispatch ready base) start label next)
    (tail : Steps profile ready (specDispatch ready base) next labels finish)
    (paired : HostFrame.Related.Paired older start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle = some selection.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (compare : ShorterCallbackSlices profile ready base bindings (label :: labels).length) :
    CallbackSlice profile ready base bindings older start incoming (label :: labels) finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.actualSelectedMemoryCallback
    selection install tail paired selected embedder compare

/-- Classify finite callbacks under the fixed live dispatcher. The fold derives the installed
Core request, its actual selector and the visitor shape of the compiled field. Parked gives and
reached reads with agreeing continuations use shorter checked derivations. A differing read,
live lookup, or direct install remains a separate proof cut. -/
theorem classify_give_callbacks
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (run : Steps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    CallbackSlice profile ready base bindings older start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.classifyGiveCallbacks embedder run paired

/-- One finite checked-run fold under the fixed component dispatcher. Parked
gives, admitted component calls, and public polls, waits and cancels share the
shorter-run induction, including inside allocator and cancellation callbacks.
An unresolved cancel enters the hook after the actual request write and
installation. Its executed marked pop leads to the reached readiness decision,
or to the actual trapped or exhausted prefix of that decision.
When the original Core caller is active at that decision, compare its live
finish and executed reply, or follow its executed park through the mixed suffix.
A direct give follows the actual thread and store reads to the two live callout
bodies, with the marked program continuation; admission remains a proof cut.
A non-early wait enters the scheduler fold before any caller reply. Exhausted
and trapped deliveries retain their reached endpoints without rejoining. Other
component sites remain at their exact install cut with the reached outcome. -/
theorem classify_mixed_callbacks {callees : List (ComponentCall.Callee sig)}
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    MixedCallbackSlice profile ready bindings callees older start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.classifyMixedCallbacks run paired

open ReturnFrame.Occurrence in
/-- Follow the original Core wait install through the actual entry and
early/non-early decision. The reached prefix may still be pending or trapped.
A returned decision selects the next body; it is not a Core reply or a park. -/
theorem cut_public_wait_decision (mem : (core3 grow).MemAddr) (inst : InstId) (args : List FlatValue)
    {thread core resume frames rest label installed}
    (focused : start.ctl = ⟨thread, .core core resume, frames⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (waitableCalloutHost false mem inst) args)
    (step : Step profile ready (specDispatch ready base) start label installed)
    (run : Steps profile ready (specDispatch ready base) installed labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ peerFrames peerRest leading suffix reached peer,
      let caller : Seg (core3 grow) (HostState sig) := .core core resume
      let check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨thread, caller :: frames, rest⟩
      let canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨thread, caller :: peerFrames, peerRest⟩
      label :: labels = (.tau :: leading) ++ suffix ∧
      (∃ mark, OccurrenceTransport profile ready base bindings start incoming (.tau :: leading) (.tau :: leading) reached peer [mark]) ∧
      (reached.ctl ≠ [] → OccurrenceTransport profile ready base bindings start incoming (.tau :: leading) (.tau :: leading)
        reached peer [some (.active 0 0)]) ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon (fun result : WaitableCalloutEntry × Option ThreadId => waitableWaitAfterDecision mem result.1 result.2)
        (fun result => waitableWaitAfterDecision mem result.1 result.2) reached peer suffix True :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutPublicWaitDecision
    mem inst args focused calling step run paired

open ReturnFrame.Occurrence in
/-- Cut public cancellation at its executed Core install and reached entry.
Argument, live handle, duplicate and membership traps retain their actual
paired paths. Successful entry selects a body, not a cancellation reply. -/
theorem cut_public_cancel_entry (async : Bool) (inst : InstId) (args : List FlatValue)
    {thread core resume frames rest label installed}
    (focused : start.ctl = ⟨thread, .core core resume, frames⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.builtin (.subtaskCancel async) inst) args)
    (step : Step profile ready (specDispatch ready base) start label installed)
    (run : Steps profile ready (specDispatch ready base) installed labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ peerFrames peerRest leading suffix reached peer,
      let caller : Seg (core3 grow) (HostState sig) := .core core resume
      let check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨thread, caller :: frames, rest⟩
      let canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨thread, caller :: peerFrames, peerRest⟩
      label :: labels = (.tau :: leading) ++ suffix ∧
      (∃ mark, OccurrenceTransport profile ready base bindings start incoming (.tau :: leading) (.tau :: leading) reached peer [mark]) ∧
      (reached.ctl ≠ [] → OccurrenceTransport profile ready base bindings start incoming (.tau :: leading) (.tau :: leading)
        reached peer [some (.active 0 0)]) ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon (cancelCalloutBody async) (cancelCalloutBody async) reached peer suffix True :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutPublicCancelEntry
    async inst args focused calling step run paired

/-- Spend the actual current-thread read and cancellation-request update on
the unresolved branch up to the late-bound hook focus. This does not execute
or assume a return from the hook and does not consume an event. -/
theorem cut_cancel_request_write (async : Bool) (subtask : SubtaskId) (hook : CancelRef)
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (cancelCalloutBody async (subtask, some hook)))
    (rightFocus : incoming.ctl = canon.control (cancelCalloutBody async (subtask, some hook)))
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon (fun _ : Unit => cancelAfterRequestWrite async subtask hook)
        (fun _ => cancelAfterRequestWrite async subtask hook) reached peer suffix True :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutCancelRequestWrite
    async subtask hook leftFocus rightFocus paired run

/-- Starting at the actual post-hook continuation, compare the return shape,
live resolution read and synchronous readiness choice. A chosen wait is not
yet an executed block, and neither branch is a public cancellation reply. -/
theorem cut_cancel_hook_decision (async : Bool) (subtask : SubtaskId) (result : Ret (core3 grow))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (cancelHookReturn async subtask result))
    (rightFocus : incoming.ctl = canon.control (cancelHookReturn async subtask result))
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon (cancelAfterHookDecision subtask) (cancelAfterHookDecision subtask)
        reached peer suffix True :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutCancelHookDecision
    async subtask result leftFocus rightFocus paired run

open ReturnFrame.Occurrence in
/-- Compare the actual synchronous cancel block and save the original Core
caller at its reached slot. An exhausted block focus has not parked. -/
theorem cut_cancel_sync_park (subtask : SubtaskId)
    {thread core resume frames rest peerFrames peerRest}
    (leftFocus : start.ctl = ⟨some thread, .prog (cancelAfterHookDecision subtask (some thread)), .core core resume :: frames⟩ :: rest)
    (rightFocus : incoming.ctl = ⟨some thread, .prog (cancelAfterHookDecision subtask (some thread)),
      .core core resume :: peerFrames⟩ :: peerRest)
    (paired : PairedComponentSite older start incoming ⟨some thread, .core core resume :: frames, rest⟩
      ⟨some thread, .core core resume :: peerFrames, peerRest⟩)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    (labels = [] ∧ finish = start) ∨
      ∃ suffix,
        let reached := { (start.setCont thread (some ⟨some thread, .prog (cancelFinish subtask), .core core resume :: frames⟩)) with
          store := StepDefs.threadStatusSt thread .blocked start.store, ctl := rest }
        let peer := { (incoming.setCont thread (some ⟨some thread, .prog (cancelFinish subtask), .core core resume :: peerFrames⟩)) with
          store := StepDefs.threadStatusSt thread .blocked incoming.store, ctl := peerRest }
        labels = .tau :: suffix ∧ Steps profile ready (specDispatch ready base) reached suffix finish ∧
        HostFrame.Related.Paired older reached peer ∧
        OccurrenceTransport profile ready base bindings start incoming [.tau] [.tau] reached peer ∧
        Trail profile ready (specDispatch ready base) start (some (.active 0 0)) [.tau] reached (some (.saved thread.idx 0)) ∧
        Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming (some (.active 0 0))
          [.tau] peer (some (.saved thread.idx 0)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutCoreCalloutPark
    (cancelFinish subtask) leftFocus rightFocus paired run

open ReturnFrame.Occurrence in
/-- Spend the actual late-bound cancellation-hook install, if reached. Both
dispatchers install the same hook body and original continuation; this does
not certify the behavior of an open hook or force it to return. -/
theorem cut_cancel_hook_install (async : Bool) (subtask : SubtaskId) (hook : CancelRef)
    {thread frames rest peerFrames peerRest}
    (leftFocus : start.ctl = ⟨thread, .prog (cancelAfterRequestWrite async subtask hook), frames⟩ :: rest)
    (rightFocus : incoming.ctl = ⟨thread, .prog (cancelAfterRequestWrite async subtask hook), peerFrames⟩ :: peerRest)
    (paired : PairedComponentSite older start incoming ⟨thread, frames, rest⟩ ⟨thread, peerFrames, peerRest⟩)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    (labels = [] ∧ finish = start) ∨
    ∃ suffix,
      let resume := cancelHookReturn (grow := grow) (sig := sig) async subtask
      let body := specDispatch ready base (.onCancel hook)
      let reached := { start with ctl := ⟨thread, .prog body, .prog resume :: frames⟩ :: rest }
      let peer := { incoming with ctl := ⟨thread, .prog body, .prog resume :: peerFrames⟩ :: peerRest }
      labels = .tau :: suffix ∧ Steps profile ready (specDispatch ready base) reached suffix finish ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older resume resume) reached peer ∧
      OccurrenceTransport profile ready base bindings start incoming [.tau] [.tau] reached peer [some (.active 0 0)] :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutCancelHookInstall
    async subtask hook leftFocus rightFocus paired run

open ReturnFrame.Occurrence in
/-- At the reached cancel delivery body, match consumption of the live event
and the subsequent record read. Only an executed Core pop exposes the caller
residual; a late trap retains the effects of the preceding take. -/
theorem cut_cancel_delivery (async : Bool) (subtask : SubtaskId)
    {thread core resume frames rest peerFrames peerRest}
    (leftFocus : start.ctl = ⟨thread, .prog (cancelCalloutBody async (subtask, none)), .core core resume :: frames⟩ :: rest)
    (rightFocus : incoming.ctl = ⟨thread, .prog (cancelCalloutBody async (subtask, none)), .core core resume :: peerFrames⟩ :: peerRest)
    (paired : PairedComponentSite older start incoming ⟨thread, .core core resume :: frames, rest⟩
      ⟨thread, .core core resume :: peerFrames, peerRest⟩)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older ⟨thread, .core core resume :: frames, rest⟩
        ⟨thread, .core core resume :: peerFrames, peerRest⟩ waitableFlatReply waitableFlatReply reached peer suffix True ∧
      WaitableCalloutExit profile ready base bindings older reached peer suffix finish ∧
      (reached.ctl ≠ [] → ∀ place,
        Prefix profile ready (specDispatch ready base) start place leading reached place ∧
        Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place leading peer place) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutCancelDelivery
    async subtask leftFocus rightFocus paired run

open ReturnFrame.Occurrence in
/-- Compare the live cancellation finish. `[BLOCKED]` is a flat reply with
no delivery observation; a resolved branch consumes its current event. -/
theorem cut_cancel_finish (subtask : SubtaskId)
    {thread core resume frames rest peerFrames peerRest}
    (leftFocus : start.ctl = ⟨thread, .prog (cancelFinish subtask), .core core resume :: frames⟩ :: rest)
    (rightFocus : incoming.ctl = ⟨thread, .prog (cancelFinish subtask), .core core resume :: peerFrames⟩ :: peerRest)
    (paired : PairedComponentSite older start incoming ⟨thread, .core core resume :: frames, rest⟩
      ⟨thread, .core core resume :: peerFrames, peerRest⟩)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      CancelFinishExit profile ready base bindings older reached peer suffix finish ∧
      (reached.ctl ≠ [] → ∀ place,
        Prefix profile ready (specDispatch ready base) start place leading reached place ∧
        Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place leading peer place) ∧
      reached.host = start.host ∧ peer.host = incoming.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutCancelFinish
    subtask leftFocus rightFocus paired run

open ReturnFrame.Occurrence in
/-- Drive the finish from an executed resume of the currently selected slot.
This identifies the reached saved occurrence, not an earlier overwritten one. -/
theorem cut_resumed_cancel_finish (subtask : SubtaskId)
    {waiter resumer afterResume frames rest core resume savedFrames label next}
    (scheduled : start.ctl = ⟨resumer, .prog (.op (.resumeThread waiter) afterResume), frames⟩ :: rest)
    (found : start.cont? waiter = some ⟨some waiter, .prog (cancelFinish subtask), .core core resume :: savedFrames⟩)
    (step : Step profile ready (specDispatch ready base) start label next)
    (run : Steps profile ready (specDispatch ready base) next labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ leading suffix reached peer,
      label :: labels = (.tau :: leading) ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming (.tau :: leading) (.tau :: leading) reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      CancelFinishExit profile ready base bindings older reached peer suffix finish ∧
      (reached.ctl ≠ [] →
        Trail profile ready (specDispatch ready base) start (some (.saved waiter.idx 0))
          (.tau :: leading) reached (some (.active 0 0)) ∧
        Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming (some (.saved waiter.idx 0))
          (.tau :: leading) peer (some (.active 0 0))) ∧
      reached.host = start.host ∧ peer.host = incoming.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.cutResumedCancelFinish
    subtask scheduled found step run paired

/-- Classify the actually executed hook prefix under the mixed live
dispatcher. At a reply focus, consume only the installed occurrence's pop. -/
theorem classify_cancel_hook_callbacks {callees : List (ComponentCall.Callee sig)}
    (async : Bool) (subtask : SubtaskId) (hook : CancelRef)
    {thread frames rest peerFrames peerRest}
    (leftFocus : start.ctl = ⟨thread, .prog (cancelAfterRequestWrite async subtask hook), frames⟩ :: rest)
    (rightFocus : incoming.ctl = ⟨thread, .prog (cancelAfterRequestWrite async subtask hook), peerFrames⟩ :: peerRest)
    (paired : PairedComponentSite older start incoming ⟨thread, frames, rest⟩ ⟨thread, peerFrames, peerRest⟩)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish) :
    CancelHookCallbackSlice profile ready (ComponentCall.hostWithComponent bindings callees) bindings older
      (cancelHookReturn async subtask) start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.classifyCancelHookCallbacks
    async subtask hook leftFocus rightFocus paired run

/-- Compare an executed wait park and its actual mixed suffix, transporting
the original Core caller across intervening work and any reached resumption.
Loss, including overwrite by an equal continuation, is not a return. -/
theorem classify_parked_wait_callbacks {callees : List (ComponentCall.Callee sig)}
    (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry)
    {thread core resume frames rest peerFrames peerRest}
    (leftFocus : start.ctl = ⟨some thread, .prog (waitableWaitAfterDecision mem entry (some thread)), .core core resume :: frames⟩ :: rest)
    (rightFocus : incoming.ctl = ⟨some thread, .prog (waitableWaitAfterDecision mem entry (some thread)),
      .core core resume :: peerFrames⟩ :: peerRest)
    (paired : PairedComponentSite older start incoming ⟨some thread, .core core resume :: frames, rest⟩
      ⟨some thread, .core core resume :: peerFrames, peerRest⟩)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish) :
    ParkedWaitCallbackSlice profile ready (ComponentCall.hostWithComponent bindings callees) bindings older start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.classifyParkedWaitCallbacks
    mem entry leftFocus rightFocus paired run

/-- Follow the original cancellation caller from its executed block through
the mixed fold, including reached resumes and actual Core returns. -/
theorem classify_parked_cancel_callbacks {callees : List (ComponentCall.Callee sig)}
    (subtask : SubtaskId)
    {thread core resume frames rest peerFrames peerRest}
    (leftFocus : start.ctl = ⟨some thread, .prog (cancelAfterHookDecision subtask (some thread)), .core core resume :: frames⟩ :: rest)
    (rightFocus : incoming.ctl = ⟨some thread, .prog (cancelAfterHookDecision subtask (some thread)),
      .core core resume :: peerFrames⟩ :: peerRest)
    (paired : PairedComponentSite older start incoming ⟨some thread, .core core resume :: frames, rest⟩
      ⟨some thread, .core core resume :: peerFrames, peerRest⟩)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish) :
    ParkedCoreCalloutSlice profile ready (ComponentCall.hostWithComponent bindings callees) bindings older start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.classifyParkedCancelCallbacks
    subtask leftFocus rightFocus paired run

/-- Enter the live worker fold only on the actually executed marked pop.
The fold consumes the extracted shorter suffix under the same dispatcher;
a different resumed program remains a boundary after the paired pop. -/
theorem compare_component_marked_worker {callees : List (ComponentCall.Callee sig)}
    {reached peer : Config (core3 grow) (HostState sig)} {leading suffix : Trace grow sig}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (moved : OccurrenceTransport profile ready (ComponentCall.hostWithComponent bindings callees) bindings
      start incoming leading leading reached peer)
    (reply : ComponentMarkedReplyTail profile ready (ComponentCall.hostWithComponent bindings callees) bindings older
      start incoming reached peer leading check first second suffix finish) :
    ComponentMarkedWorkerTail profile ready (ComponentCall.hostWithComponent bindings callees) bindings older
      start incoming reached peer leading check first second suffix finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.compareComponentMarkedWorker moved reply

theorem classify_memory_callbacks
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (run : Steps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    CallbackSlice profile ready base bindings older start incoming labels finish :=
  classify_give_callbacks embedder run paired

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch
