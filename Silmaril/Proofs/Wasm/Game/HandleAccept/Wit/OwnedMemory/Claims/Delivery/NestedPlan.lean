module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.StringPlan.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.StringPlan.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Public.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Traversal.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Allocation.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
import Silmaril.Wasm.Component.Reference.ABI.Layout.Thms
import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
import Silmaril.Wasm.Component.Reference.Canon.Lower.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.RecursiveTrails

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open LiveDispatch ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind} {ready : HostReady (HostState sig)}
  {bindings : List (Binding sig)} {base : HostImpl (core3 grow) (HostState sig)}
  {start finish incoming : Config (core3 grow) (HostState sig)} {labels : Trace grow sig}
  {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}

private theorem append {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {before middle after : Config (core3 grow) (HostState sig)} {leading trailing}
    (front : Steps profile ready dispatch before leading middle) (back : Steps profile ready dispatch middle trailing after) :
    Steps profile ready dispatch before (leading ++ trailing) after := by
  induction front with
  | refl => exact back
  | cons step _ ih => exact .cons step (ih back)

private theorem progOpEq {S : Sig} {Result : Type} {first second : S.Op}
    {left : S.Resp first → Prog S Result} {right : S.Resp second → Prog S Result} :
    Prog.op first left = Prog.op second right → first = second ∧ HEq left right := by
  intro same
  injection same with operation continuation
  exact ⟨operation, continuation⟩

set_option maxHeartbeats 1000000 in
private theorem silentStepUnique {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {before left right : Config (core3 grow) (HostState sig)} {label}
    (quiet : Step profile ready dispatch before .tau left) (actual : Step profile ready dispatch before label right) :
    label = .tau ∧ left = right := by
  cases quiet <;> cases actual
  all_goals try (cases (show Fault before _ from by assumption))
  all_goals simp_all [StepDefs.HostReadyCfg]
  all_goals
    have heads := (show (_ ∧ Prog.op (S := Eff (core3 grow) (HostState sig)) (α := Ret (core3 grow)) _ _ = Prog.op _ _ ∧ _) ∧ _
      from by assumption)
    obtain ⟨⟨_, programs, _⟩, _⟩ := heads
    obtain ⟨operation, continuation⟩ := progOpEq programs
    simp_all
  all_goals (injection operation; subst_vars; simp_all)

private theorem splitSilent {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {before replied finish : Config (core3 grow) (HostState sig)} {count : Nat} {labels : Trace grow sig}
    (quiet : Steps profile ready dispatch before (List.replicate count .tau) replied)
    (actual : Steps profile ready dispatch before labels finish) :
    (∃ rest, labels = List.replicate count .tau ++ rest ∧ Steps profile ready dispatch replied rest finish) ∨ labels.length < count := by
  induction count generalizing before labels with
  | zero => cases quiet; exact .inl ⟨labels, rfl, actual⟩
  | succ count ih =>
    rw [List.replicate_succ] at quiet
    cases quiet with
    | cons first quiet =>
      cases actual with
      | refl => exact .inr (Nat.zero_lt_succ _)
      | cons second actual =>
        obtain ⟨rfl, rfl⟩ := silentStepUnique first second
        rcases ih quiet actual with ⟨rest, rfl, tail⟩ | short
        · exact .inl ⟨rest, by rw [List.replicate_succ]; rfl, tail⟩
        · exact .inr (Nat.succ_lt_succ short)

set_option maxHeartbeats 2000000 in
theorem cutComponentLowerEntry (callee : ComponentCall.Callee sig) (caller : CallerId)
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
      Steps profile ready (specDispatch ready base) (entered start cursor) suffix finish) ∨ labels.length < 3 := by
  dsimp only
  obtain ⟨peerFrames, peerRest, peerFocus, aligned⟩ := paired.retarget focused (.prog (.pure (.cancel .none)))
    (start.host.enter callee.name callee.coreType args) (incoming.host.enter callee.name callee.coreType args)
  have peerRecord := paired.data.1 ▸ record
  have left := ComponentCall.invoke_lower_entry (prof := profile) (ready := ready) (dispatch := specDispatch ready base)
    callee caller record focused
  have right := ComponentCall.invoke_lower_entry (prof := profile) (ready := ready)
    (dispatch := specDispatch ready (LiveDispatch.host bindings base)) callee caller peerRecord peerFocus
  rcases splitSilent (count := 3) (left (.active 0 0)).toTrail.steps run with ⟨suffix, split, residual⟩ | short
  · exact .inl ⟨⟨cursor.thread, peerFrames, peerRest⟩, suffix, split,
      CallbackPrefix.stationaryTransport left right, aligned, residual⟩
  · exact .inr short

set_option maxHeartbeats 2000000 in
theorem cutComponentAdmitted (callee : ComponentCall.Callee sig) (caller : CallerId)
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
      Steps profile ready (specDispatch ready base) (reached start frames rest) suffix finish) ∨ labels.length < 7 := by
  dsimp only
  obtain ⟨peerFrames, peerRest, peerFocus, aligned⟩ := paired.retarget focused (.prog (.pure (.cancel .none)))
    (start.host.enter callee.name callee.coreType args) (incoming.host.enter callee.name callee.coreType args)
  have sameStore := paired.data.1
  have plan : callee.childPreflight start.host.writer.accepted start.store cx args =
      callee.childPreflight incoming.host.writer.accepted incoming.store cx args :=
    (ComponentCall.child_preflight_agrees callee observed).trans
      (congrArg (fun store => callee.childPreflight incoming.host.writer.accepted store cx args) sameStore)
  have leftEntry := ComponentCall.invoke_lower_entry (prof := profile) (ready := ready) (dispatch := specDispatch ready base)
    callee caller record focused
  have rightEntry := ComponentCall.invoke_lower_entry (prof := profile) (ready := ready)
    (dispatch := specDispatch ready (LiveDispatch.host bindings base)) callee caller (sameStore ▸ record) peerFocus
  let entered (state : Config (core3 grow) (HostState sig)) atFrames atRest :=
    { state with
      host := state.host.enter callee.name callee.coreType args
      ctl := ⟨some active, .prog (ComponentCall.invokeLower callee caller state.host subtask cx args pos ft limits results),
        atFrames⟩ :: atRest }
  have left := fun place => (leftEntry place).append (ComponentCall.invoke_lower_admitted
    (config := entered start frames rest) callee caller start.host liveThread liveTask context admitted rfl place)
  have right := fun place => (rightEntry place).append (ComponentCall.invoke_lower_admitted
    (config := entered incoming peerFrames peerRest) callee caller incoming.host
    (sameStore ▸ liveThread) (sameStore ▸ liveTask) context (sameStore ▸ admitted) rfl place)
  change ∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
    incoming place (List.replicate 7 .tau)
    { incoming with
      host := incoming.host.enter callee.name callee.coreType args
      ctl := ⟨some active, .prog (ComponentCall.acceptPlanned callee caller incoming.host.nextTicket
        (callee.childPreflight incoming.host.writer.accepted incoming.store cx args)), peerFrames⟩ :: peerRest } place at right
  rw [← plan] at right
  rcases splitSilent (count := 7) (left (.active 0 0)).toTrail.steps run with ⟨suffix, split, residual⟩ | short
  · exact .inl ⟨peerFrames, peerRest, suffix, split, CallbackPrefix.stationaryTransport left right, aligned, residual⟩
  · exact .inr short

theorem cutComponentLiftStart (callee : ComponentCall.Callee sig) (caller : CallerId)
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
      Steps profile ready (specDispatch ready base) (reached start check leftTicket) suffix finish) ∨ labels.length < count := by
  dsimp only
  have same : start.store = incoming.store := (HostFrame.Related.Paired.data paired).1
  have left := ComponentCall.observe_lower_start_tracks (prof := profile) (ready := ready) (dispatch := specDispatch ready base)
    caller record (ComponentCall.acceptPayload callee caller leftTicket planned) callerRecord live leftFocus
  have right := ComponentCall.observe_lower_start_tracks (prof := profile) (ready := ready)
    (dispatch := specDispatch ready (LiveDispatch.host bindings base)) caller record
    (ComponentCall.acceptPayload callee caller rightTicket planned) (same ▸ callerRecord) (same ▸ live) rightFocus
  dsimp only at left right
  have steps : ([.tau, .tau] ++ (if record.index.isSome then [.tau] else []) ++ [.tau] : Trace grow sig) =
      List.replicate (if record.index.isSome then 4 else 3) .tau := by cases record.index <;> rfl
  rw [steps] at left right
  rcases splitSilent (left (.active 0 0)).toTrail.steps run with ⟨suffix, split, residual⟩ | short
  · refine .inl ⟨suffix, split, CallbackPrefix.stationaryTransport left right, ?_, residual⟩
    unfold PairedComponentSite HostFrame.Related.Paired at paired ⊢
    dsimp only
    rw [← same]
    exact paired.set_store _
  · exact .inr short

private theorem componentTrapUnique {reason : TrapReason} {cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {resume : (Eff (core3 grow) (HostState sig)).Resp (.trap reason) → Session grow sig (Ret (core3 grow))}
    (focus : start.ctl = cursor.control (.op (.trap reason) resume))
    {label} {reached : Config (core3 grow) (HostState sig)}
    (step : Step profile ready (specDispatch ready base) start label reached) :
    label = .trap reason ∧ reached = StepDefs.trapCfg start := by
  cases cursor
  cases step
  all_goals try (cases (show Fault start _ from by assumption))
  all_goals simp_all [PayloadPrefix.Cursor.control, StepDefs.HostReadyCfg]
  all_goals
    have heads := (show (_ ∧ Prog.op (S := Eff (core3 grow) (HostState sig)) (α := Ret (core3 grow)) _ _ = Prog.op _ _ ∧ _) ∧ _
      from by assumption)
    obtain ⟨⟨_, programs, _⟩, _⟩ := heads
    obtain ⟨operation, continuation⟩ := progOpEq programs
    simp_all
  exact Op.trap.inj operation

private theorem componentChoiceActual {choice : ChoiceKind} {cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {resume : choice.Resp → Session grow sig (Ret (core3 grow))} {label reached}
    (focus : start.ctl = cursor.control (.op (.choose choice) resume))
    (step : Step profile ready (specDispatch ready base) start label reached) :
    ∃ result, label = .choice choice result ∧ reached = { start with ctl := cursor.control (resume result) } ∧
      Allowed profile choice result := by
  cases cursor
  cases step
  case choose result found allowed =>
    rw [focus] at found
    cases found
    exact ⟨_, rfl, rfl, allowed⟩
  all_goals try (cases (show Fault start _ from by assumption))
  all_goals simp_all [PayloadPrefix.Cursor.control, StepDefs.HostReadyCfg]
  all_goals obtain ⟨operation, _⟩ := progOpEq focus.1.2.1; cases operation

private def storePreserves (invariant : CStore (core3 grow) → Prop) : (Eff (core3 grow) (HostState sig)).Op → Prop
  | .modify update => ∀ store, invariant store → invariant (update store)
  | _ => True

open PayloadPrefix ReturnFrame.Occurrence in
set_option maxHeartbeats 3000000 in
private theorem cutComponentStoreBodyFramed {Result : Type} {closed : Prop} (body : Session grow sig Result)
    (checkNext canonNext : Result → Session grow sig (Ret (core3 grow)))
    (certified : closed → Prog.Every (fun op => componentStoreOp op = true) body)
    {invariant : CStore (core3 grow) → Prop}
    (preserves : Prog.Every (storePreserves invariant) body) (initial : invariant start.store)
    {check canon : Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (body >>= checkNext))
    (rightFocus : incoming.ctl = canon.control (body >>= canonNext))
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon checkNext canonNext reached peer suffix closed ∧
      reached.host = start.host ∧ peer.host = incoming.host ∧
      (reached.ctl ≠ [] → invariant reached.store ∧ ∀ place,
        Prefix profile ready (specDispatch ready base) start place leading reached place ∧
        Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place leading peer place) := by
  induction labels generalizing start incoming body with
  | nil =>
    cases run
    refine ⟨[], [], finish, incoming, rfl, CallbackPrefix.stationaryTransport (fun _ => .done _ _) (fun _ => .done _ _), .refl _, ?_, rfl, rfl,
      fun _ => ⟨initial, fun place => ⟨.done _ place, .done _ place⟩⟩⟩
    cases body with
    | pure result => exact .returned result leftFocus rightFocus paired
    | op op next => exact .pending op next leftFocus rightFocus paired (.inl rfl)
  | cons label suffix ih =>
    cases body with
    | pure result =>
      exact ⟨[], label :: suffix, start, incoming, rfl, CallbackPrefix.stationaryTransport (fun _ => .done _ _) (fun _ => .done _ _),
        run, .returned result leftFocus rightFocus paired, rfl, rfl, fun _ => ⟨initial, fun place => ⟨.done _ place, .done _ place⟩⟩⟩
    | op op next =>
      have leftOp : start.ctl = check.control (.op op (fun response => next response >>= checkNext)) := leftFocus
      have rightOp : incoming.ctl = canon.control (.op op (fun response => next response >>= canonNext)) := rightFocus
      by_cases localOp : componentStoreOp op = false
      · have notClosed : ¬ closed := by
          intro proven
          cases certified proven with
          | op allowed _ => rw [localOp] at allowed; contradiction
        exact ⟨[], label :: suffix, start, incoming, rfl, CallbackPrefix.stationaryTransport (fun _ => .done _ _) (fun _ => .done _ _),
          run, .pending op next leftOp rightOp paired (.inr ⟨notClosed, localOp⟩), rfl, rfl,
          fun _ => ⟨initial, fun place => ⟨.done _ place, .done _ place⟩⟩⟩
      cases run with
      | @cons _ middle _ _ _ first tail =>
        have same : start.store = incoming.store := (HostFrame.Related.Paired.data paired).1
        have sameThread : check.thread = canon.thread := by
          obtain ⟨frames, rest, focus, _⟩ := HostFrame.Related.Paired.retarget paired rfl (.prog (.pure (.cancel .none))) start.host incoming.host
          exact (congrArg (fun ctl : List (Activation (core3 grow) (HostState sig)) => ctl.head?.map (·.thread)) focus |> Option.some.inj).symm
        have localStep {action : Label (core3 grow) (HostState sig)}
            (response : (Eff (core3 grow) (HostState sig)).Resp op) (updated : CStore (core3 grow))
            (updatedInv : invariant updated)
            (leftStep : Step profile ready (specDispatch ready base) start action
              { start with store := updated, ctl := check.control (next response >>= checkNext) })
            (rightStep : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming action
              { incoming with store := updated, ctl := canon.control (next response >>= canonNext) })
            (leftEdit : transitionEdit start action = .same) (rightEdit : transitionEdit incoming action = .same)
            (executed : action = .tau ∨ (label = action ∧
              middle = { start with store := updated, ctl := check.control (next response >>= checkNext) })) :
            ∃ leading trailing reached peer, label :: suffix = leading ++ trailing ∧
              OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
              Steps profile ready (specDispatch ready base) reached trailing finish ∧
              ComponentStoreFrontier older check canon checkNext canonNext reached peer trailing closed ∧
              reached.host = start.host ∧ peer.host = incoming.host ∧
              (reached.ctl ≠ [] → invariant reached.store ∧ ∀ place,
                Prefix profile ready (specDispatch ready base) start place leading reached place ∧
                Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place leading peer place) := by
          have actually : label = action ∧ middle = { start with store := updated, ctl := check.control (next response >>= checkNext) } := by
            rcases executed with rfl | alignment
            · obtain ⟨silent, endpoint⟩ := silentStepUnique leftStep first
              exact ⟨silent, endpoint.symm⟩
            · exact alignment
          obtain ⟨sameLabel, sameEndpoint⟩ := actually
          subst label
          subst middle
          let nextPeer := { incoming with store := updated, ctl := canon.control (next response >>= canonNext) }
          have aligned : PairedComponentSite older
              { start with store := updated, ctl := check.control (next response >>= checkNext) } nextPeer check canon :=
            HostFrame.Related.Paired.set_store paired updated
          have followingCertified : closed → Prog.Every (fun op => componentStoreOp op = true) (next response) := by
            intro proven
            cases certified proven with
            | op _ continuations => exact continuations response
          have followingPreserves : Prog.Every (storePreserves invariant) (next response) := by
            cases preserves with
            | op _ continuations => exact continuations response
          obtain ⟨leading, trailing, reached, peer, split, moved, residual, frontier, leftHost, rightHost, retained⟩ :=
            ih (next response) followingCertified followingPreserves updatedInv rfl (show nextPeer.ctl = _ from rfl) aligned tail
          have leftAt place : Prefix profile ready (specDispatch ready base) start place [action] _ place :=
            .step leftStep (by rw [leftEdit]; rfl) (.done _ place)
          have rightAt place : Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place [action] nextPeer place :=
            .step rightStep (by rw [rightEdit]; rfl) (.done _ place)
          have movement := CallbackPrefix.stationaryTransport (bindings := bindings) leftAt rightAt
          refine ⟨action :: leading, trailing, reached, peer, congrArg (action :: ·) split, ?_, residual, frontier, leftHost, rightHost, ?_⟩
          · simpa only [List.map_nil, List.append_nil, List.singleton_append] using
              (CallbackPrefix.transportAppend movement moved).choose_spec.1
          · intro live
            obtain ⟨keeps, paths⟩ := retained live
            exact ⟨keeps, fun place => ⟨(leftAt place).append (paths place).1, (rightAt place).append (paths place).2⟩⟩
        cases op with
        | get =>
          exact localStep start.store start.store initial (.get leftOp) (same ▸ .get rightOp)
            (by rw [transitionEdit, leftOp]; rfl) (by rw [transitionEdit, rightOp]; rfl) (.inl rfl)
        | modify update =>
          have updatedInv : invariant (update start.store) := by
            cases preserves with
            | op allowed _ => exact allowed _ initial
          exact localStep () (update start.store) updatedInv (.modify leftOp)
            (by rw [same]; exact .modify rightOp)
            (by rw [transitionEdit, leftOp]; rfl) (by rw [transitionEdit, rightOp]; rfl) (.inl rfl)
        | currentThread =>
          exact localStep check.thread start.store initial (.currentThread leftOp)
            (by rw [same, sameThread]; exact .currentThread rightOp)
            (by rw [transitionEdit, leftOp]; rfl) (by rw [transitionEdit, rightOp]; rfl) (.inl rfl)
        | choose choice =>
          obtain ⟨answer, actualLabel, actualNext, allowed⟩ := componentChoiceActual leftOp first
          exact localStep answer start.store initial (.choose answer leftOp allowed)
            (by rw [same]; exact .choose answer rightOp allowed) rfl rfl (.inr ⟨actualLabel, actualNext⟩)
        | trap reason =>
          obtain ⟨rfl, rfl⟩ := componentTrapUnique leftOp first
          refine ⟨[.trap reason], suffix, StepDefs.trapCfg start, StepDefs.trapCfg incoming, rfl, ?_, tail,
            .trapped rfl rfl ?_, rfl, rfl, fun live => False.elim (live rfl)⟩
          · have tracking := CallbackPrefix.localLeafTransport (check := check) (canon := canon) (checkNext := checkNext)
              (left := start) (right := incoming) (store := start.store) (leftHost := start.host) (rightHost := incoming.host)
              (checked := [.trap reason]) (canonical := [.trap reason]) (canonNext := canonNext) (result := .error reason)
              (fun mark => by
                simp only [localLeafEnd, same]
                have leftTrap : Step profile ready (specDispatch ready base) start (.trap reason) (StepDefs.trapCfg start) := .trap leftOp
                have rightTrap : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming
                    (.trap reason) (StepDefs.trapCfg incoming) := .trap rightOp
                have leftLock : StepDefs.trapCfg { start with store := incoming.store } = StepDefs.trapCfg start := by rw [← same]
                rw [leftLock]
                refine ⟨.step leftTrap ?_, .step rightTrap ?_⟩ <;>
                  rcases mark with _ | ⟨place⟩ <;> try exact .done _ _
                all_goals cases place <;> exact .done _ _) (profile := profile) (ready := ready) (base := base) (bindings := bindings)
            simpa only [localLeafEnd, StepDefs.trapCfg, same] using tracking
          · simpa only [StepDefs.trapCfg, same] using
              (HostFrame.Related.Paired.set_store paired (StepDefs.lockdownSt incoming.store)).clear_control
        | _ => exact False.elim (localOp rfl)

private theorem trivialPreserves {Result : Type} (program : Session grow sig Result) :
    Prog.Every (storePreserves (fun _ => True)) program := by
  induction program with
  | pure result => exact .pure result
  | op op next ih => exact .op (by cases op <;> simp [storePreserves]) ih

open PayloadPrefix in
theorem cutComponentStoreBody {Result : Type} {closed : Prop} (body : Session grow sig Result)
    (checkNext canonNext : Result → Session grow sig (Ret (core3 grow)))
    (certified : closed → Prog.Every (fun op => componentStoreOp op = true) body)
    {check canon : Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (body >>= checkNext))
    (rightFocus : incoming.ctl = canon.control (body >>= canonNext))
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon checkNext canonNext reached peer suffix closed ∧
      reached.host = start.host ∧ peer.host = incoming.host := by
  obtain ⟨leading, trailing, reached, peer, split, moved, residual, frontier, left, right, _⟩ :=
    cutComponentStoreBodyFramed (bindings := bindings) body checkNext canonNext certified (trivialPreserves body) trivial
      leftFocus rightFocus paired run
  exact ⟨leading, trailing, reached, peer, split, moved, residual, frontier, left, right⟩

private abbrev ComponentStoreEdit (grow : SingleThreaded.GrowOracle) := CStore (core3 grow) → CStore (core3 grow)

open ReturnFrame.Occurrence in
private inductive ComponentQuietPath (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) :
    Config (core3 grow) (HostState sig) → List (ComponentStoreEdit grow) → Config (core3 grow) (HostState sig) → Prop where
  | done (state : Config (core3 grow) (HostState sig)) : ComponentQuietPath profile ready dispatch cursor state [] state
  | step {before after : Config (core3 grow) (HostState sig)} {update updates host program}
      (actual : Step profile ready dispatch before .tau
        { before with store := update before.store, host, ctl := cursor.control program })
      (stationary : transitionEdit before .tau = .same)
      (tail : ComponentQuietPath profile ready dispatch cursor
        { before with store := update before.store, host, ctl := cursor.control program } updates after) :
      ComponentQuietPath profile ready dispatch cursor before (update :: updates) after

open ReturnFrame.Occurrence in
private theorem ComponentQuietPath.track {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {updates : List (ComponentStoreEdit grow)}
    (path : ComponentQuietPath profile ready dispatch cursor start updates finish) (place : Location) :
    Prefix profile ready dispatch start place (List.replicate updates.length .tau) finish place := by
  induction path with
  | done => exact .done _ _
  | step actual stationary _ ih => exact .step actual (by rw [stationary]; cases place <;> rfl) ih

private theorem pairQuietHost {left right : Config (core3 grow) (HostState sig)}
    (paired : ReturnFrame.Related.Paired older left right) (host : HostState sig) :
    ReturnFrame.Related.Paired older { left with host } { right with host } := by
  cases paired with
  | mk control blocked => exact .mk control blocked

open ReturnFrame.Occurrence in
private theorem compareQuietShort {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {updates : List (ComponentStoreEdit grow)} {target peerTarget : Config (core3 grow) (HostState sig)}
    (left : ComponentQuietPath profile ready (specDispatch ready base) check start updates target)
    (right : ComponentQuietPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) canon incoming updates peerTarget)
    (paired : PairedComponentSite older start incoming check canon)
    (leftFocus : ∃ program, start.ctl = check.control program) (rightFocus : ∃ program, incoming.ctl = canon.control program)
    (run : Steps profile ready (specDispatch ready base) start labels finish) (short : labels.length < updates.length) :
    ComponentEarlyPrefix profile ready base bindings older check canon start incoming labels finish updates.length := by
  induction updates generalizing start incoming target peerTarget labels with
  | nil => simp at short
  | cons update updates ih =>
    cases run with
    | refl =>
      exact ⟨short, incoming, CallbackPrefix.stationaryTransport (fun _ => .done _ _) (fun _ => .done _ _),
        paired, leftFocus, rightFocus⟩
    | cons first tail =>
      cases left with
      | step leftStep leftEdit leftTail =>
        cases right with
        | step rightStep rightEdit rightTail =>
          rename_i leftHost leftProgram rightHost rightProgram
          obtain ⟨rfl, rfl⟩ := silentStepUnique leftStep first
          have same : start.store = incoming.store := (HostFrame.Related.Paired.data paired).1
          have nextPaired : PairedComponentSite older
              { start with store := update start.store, host := leftHost, ctl := check.control leftProgram }
              { incoming with store := update incoming.store, host := rightHost, ctl := canon.control rightProgram } check canon := by
            unfold PairedComponentSite
            rw [← same]
            exact pairQuietHost (paired.set_store (update start.store)) rightHost
          obtain ⟨_, peer, moved, endpoint, leftReached, rightReached⟩ :=
            ih leftTail rightTail nextPaired ⟨_, rfl⟩ ⟨_, rfl⟩ tail (by simpa using short)
          have firstMove := CallbackPrefix.stationaryTransport (bindings := bindings)
            (fun place => .step leftStep (by rw [leftEdit]; cases place <;> rfl) (.done _ place))
            (fun place => .step rightStep (by rw [rightEdit]; cases place <;> rfl) (.done _ place))
          refine ⟨short, peer, ?_, endpoint, leftReached, rightReached⟩
          simpa only [List.map_nil, List.append_nil, List.singleton_append] using
            (CallbackPrefix.transportAppend firstMove moved).choose_spec.1

open AsyncRef ReturnFrame.Occurrence in
private theorem refusalResolvePath (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (ticket : Nat) (caller : CallerId) (issue : Scheduled.Issue)
    {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat}
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (ComponentCall.resolveRefused ticket caller issue))
    (record : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (resultType : ft.result = some ComponentCall.resultType) (indirect : results ≤ 1) :
    ComponentQuietPath profile ready dispatch cursor start [id, id, id]
      { start with host := start.host.record (.refused ticket issue), ctl := cursor.control (do
        maybeOnProgress subtask
        let flat ← lowerFlatValues Limits.spec Quirks.none cx results [.variant 1 none]
          [ComponentCall.resultType] (some ⟨args, pos⟩)
        Subtask.resolve subtask .returned flat
        return .cancel .none) } := by
  cases cursor with
  | mk thread frames rest =>
    refine .step (.hostGet focused) (by rw [transitionEdit, focused]; rfl) ?_
    refine .step (.hostSet rfl) rfl ?_
    have read := Step.get (prof := profile) (hr := ready) (dispatch := dispatch)
      (m := { start with host := start.host.record (.refused ticket issue), ctl :=
        ⟨thread, .prog (ComponentCall.resolveError ticket caller), frames⟩ :: rest }) rfl
    simp only [Prog.bind, record, Prog.pure_eq, resultType, bne_self_eq_false, Bool.false_eq_true,
      ite_false, Nat.not_lt.mpr indirect] at read
    exact .step read rfl (.done _)

open ReturnFrame.Occurrence in
private theorem componentPreflightPath (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (callee : ComponentCall.Callee sig) (caller : CallerId)
    {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat}
    {active : ThreadId} {frames rest} {entry : Runtime.Thread} {task : Runtime.Task (core3 grow)}
    (focus : start.ctl = ⟨some active, .prog (ComponentCall.invoke callee caller), frames⟩ :: rest)
    (record : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (liveThread : ArenaField.threads.get? start.store active = some entry)
    (liveTask : ArenaField.tasks.get? start.store entry.task = some task)
    (context : task.inst = callee.inst)
    (admitted : callee.check start.store subtask cx args pos ft (limits, results) = .ok ()) :
    ComponentQuietPath profile ready dispatch ⟨some active, frames, rest⟩ start [id, id, id, id, id, id, id]
      (componentPreflightAt callee caller cx args start ⟨some active, frames, rest⟩) := by
  have read := Step.get (prof := profile) (hr := ready) (dispatch := dispatch) focus
  simp only [Prog.bind, record] at read
  refine .step read (by rw [transitionEdit, focus]; rfl) ?_
  refine .step (.hostGet rfl) rfl (.step (.hostSet rfl) rfl ?_)
  refine .step (.get rfl) rfl (.step (.currentThread rfl) rfl (.step (.get rfl) rfl ?_))
  simp only [id, Prog.bind, liveThread]
  refine .step (.get rfl) rfl ?_
  simp only [Prog.bind, liveTask, pure, context, bne_self_eq_false, Bool.false_eq_true, ite_false, admitted]
  exact .done _

open ReturnFrame.Occurrence in
theorem cutComponentPreflight (callee : ComponentCall.Callee sig) (caller : CallerId)
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
      ∃ canon, ComponentEarlyPrefix profile ready base bindings older ⟨some active, frames, rest⟩ canon start incoming labels finish 7 := by
  obtain ⟨peerFrames, peerRest, peerFocus, aligned⟩ := paired.retarget focused (.prog (.pure (.cancel .none)))
    (start.host.enter callee.name callee.coreType args) (incoming.host.enter callee.name callee.coreType args)
  have same := paired.data.1
  have left := componentPreflightPath (profile := profile) (ready := ready) (specDispatch ready base)
    callee caller focused record liveThread liveTask context admitted
  have right := componentPreflightPath (profile := profile) (ready := ready) (specDispatch ready (LiveDispatch.host bindings base))
    callee caller peerFocus (same ▸ record) (same ▸ liveThread) (same ▸ liveTask) context (same ▸ admitted)
  rcases splitSilent (count := 7) (left.track (.active 0 0)).toTrail.steps run with ⟨suffix, split, residual⟩ | short
  · exact .inl ⟨peerFrames, peerRest, suffix, peerFocus, split, CallbackPrefix.stationaryTransport left.track right.track, aligned, residual⟩
  · have site : PairedComponentSite older start incoming ⟨some active, frames, rest⟩ ⟨some active, peerFrames, peerRest⟩ := by
      obtain ⟨_, _, atPeer, normal⟩ := paired.retarget focused (.prog (.pure (.cancel .none))) start.host incoming.host
      rw [peerFocus] at atPeer
      simp only [List.cons.injEq, Activation.mk.injEq, true_and] at atPeer
      obtain ⟨rfl, rfl⟩ := atPeer
      exact normal
    exact .inr ⟨_, compareQuietShort left right site ⟨_, focused⟩ ⟨_, peerFocus⟩ run short⟩

open AsyncRef in
theorem cutComponentResolveRefused (caller : CallerId) (issue : Scheduled.Issue)
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
    ComponentEarlyPrefix profile ready base bindings older check canon start incoming labels finish 3 := by
  dsimp only
  have same : start.store = incoming.store := (HostFrame.Related.Paired.data paired).1
  have left := refusalResolvePath (profile := profile) (ready := ready) (specDispatch ready base)
    leftTicket caller issue check leftFocus record resultType indirect
  have right := refusalResolvePath (profile := profile) (ready := ready) (specDispatch ready (LiveDispatch.host bindings base))
    rightTicket caller issue canon rightFocus (same ▸ record) resultType indirect
  rcases splitSilent (count := 3) (left.track (.active 0 0)).toTrail.steps run with ⟨suffix, split, residual⟩ | short
  · refine .inl ⟨suffix, split, CallbackPrefix.stationaryTransport left.track right.track, ?_, residual⟩
    unfold PairedComponentSite at paired
    obtain ⟨frames, rest, focus, aligned⟩ := HostFrame.Related.Paired.retarget paired rfl (.prog _)
      (start.host.record (.refused leftTicket issue)) (incoming.host.record (.refused rightTicket issue))
    simp only [PayloadPrefix.Cursor.control, List.cons.injEq, Activation.mk.injEq, true_and] at focus
    obtain ⟨⟨sameThread, sameFrames⟩, sameRest⟩ := focus
    simpa only [PayloadPrefix.Cursor.control, ← sameThread, ← sameFrames, ← sameRest] using aligned
  · exact .inr (compareQuietShort left right paired ⟨_, leftFocus⟩ ⟨_, rightFocus⟩ run short)

open ReturnFrame.Occurrence in
private def refusalSkipEdits (record : Subtask) (subtask : SubtaskId) (caller : CallerId) (pos : Nat) :
    List (ComponentStoreEdit grow) :=
  [id, id] ++ (if record.index.isSome then [fun store => store.setPendingSt (.subtask subtask) (.subtask subtask)] else []) ++
    [LowerSt.startSt subtask, LowerSt.setCallerPosSt caller pos]

open ReturnFrame.Occurrence in
private theorem refusalSkipPath (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (callee : ComponentCall.Callee sig) (caller : CallerId) (ticket : Nat) (issue : Scheduled.Issue)
    {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat} (record : Subtask)
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (ComponentCall.acceptPlanned callee caller ticket (.error issue)))
    (callerRecord : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (live : start.store.subtask? subtask = some record) :
    let queued := if record.index.isSome then start.store.setPendingSt (.subtask subtask) (.subtask subtask) else start.store
    ComponentQuietPath profile ready dispatch cursor start (refusalSkipEdits record subtask caller (args.length - 1))
      { start with
        store := LowerSt.setCallerPosSt caller (args.length - 1) (LowerSt.startSt subtask queued)
        ctl := cursor.control (ComponentCall.resolveRefused ticket caller issue) } := by
  dsimp only [refusalSkipEdits]
  cases cursor with
  | mk thread frames rest =>
    have read := Step.get (prof := profile) (hr := ready) (dispatch := dispatch) focused
    simp only [Prog.bind, callerRecord, Prog.pure_eq] at read
    rw [CStore.subtask?] at live
    cases indexed : record.index with
    | none =>
      refine .step read (by rw [transitionEdit, focused]; rfl) ?_
      refine .step (.get rfl) rfl ?_
      simp [Prog.bind, live, indexed, pure, Prog.bind_assoc]
      exact .step (.modify rfl) rfl (.step (.modify rfl) rfl (.done _))
    | some _ =>
      refine .step read (by rw [transitionEdit, focused]; rfl) ?_
      refine .step (.get rfl) rfl ?_
      simp [Prog.bind, live, indexed, pure, Prog.bind_assoc, Waitable.setPendingEvent]
      refine .step (.modify rfl) rfl ?_
      exact .step (.modify rfl) rfl (.step (.modify rfl) rfl (.done _))

private theorem admittedRefusalGuards (callee : ComponentCall.Callee sig) {subtask : SubtaskId}
    {cx : LiftLowerContext (core3 grow)} {args : List FlatValue} {pos : Nat}
    {ft : WIT.FuncType Empty RtId} {limits results : Nat} {index : Option Nat}
    (admitted : callee.check start.store subtask cx args pos ft (limits, results) index = .ok ()) :
    ft.result = some ComponentCall.resultType ∧ results ≤ 1 := by
  have sameType : ft = callee.funcType := by
    by_contra different
    simp [ComponentCall.Callee.check, different, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at admitted
  have modes : (limits, results) = lowerLimits callee.async_ := by
    by_contra different
    by_cases context : cx.inst = callee.inst ∧ cx.scope = .subtask subtask
    · simp [ComponentCall.Callee.check, sameType, context.1, context.2, different, bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw] at admitted
    · have wrong : ¬cx.inst = callee.inst ∨ ¬cx.scope = .subtask subtask := by
        by_cases sameInst : cx.inst = callee.inst
        · exact .inr (fun sameScope => context ⟨sameInst, sameScope⟩)
        · exact .inl sameInst
      simp [ComponentCall.Callee.check, sameType, wrong, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at admitted
  refine ⟨congrArg WIT.FuncType.result sameType, ?_⟩
  rw [show results = (lowerLimits callee.async_).2 from congrArg Prod.snd modes]
  cases callee.async_ <;> decide

open AsyncRef in
theorem cutAdmittedRefusal (callee : ComponentCall.Callee sig) (caller : CallerId) (issue : Scheduled.Issue)
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
    ComponentEarlyPrefix profile ready base bindings older check canon start incoming labels finish count := by
  dsimp only
  let skipCount := if record.index.isSome then 5 else 4
  let skipped := fun (state : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (ticket : Nat) =>
    let queued := if record.index.isSome then state.store.setPendingSt (.subtask subtask) (.subtask subtask) else state.store
    { state with
      store := LowerSt.setCallerPosSt caller (args.length - 1) (LowerSt.startSt subtask queued)
      ctl := cursor.control (ComponentCall.resolveRefused ticket caller issue) }
  have same : start.store = incoming.store := (HostFrame.Related.Paired.data paired).1
  have leftPath := refusalSkipPath (profile := profile) (ready := ready) (specDispatch ready base)
    callee caller leftTicket issue record check leftFocus callerRecord live
  have rightPath := refusalSkipPath (profile := profile) (ready := ready) (specDispatch ready (LiveDispatch.host bindings base))
    callee caller rightTicket issue record canon rightFocus (same ▸ callerRecord) (same ▸ live)
  have edits : (refusalSkipEdits (grow := grow) record subtask caller (args.length - 1)).length = skipCount := by
    unfold refusalSkipEdits skipCount
    cases indexed : record.index <;> rfl
  have left := leftPath.track
  have right := rightPath.track
  rw [edits] at left right
  have count : skipCount + 3 = (if record.index.isSome then 8 else 7) := by
    unfold skipCount
    cases record.index <;> rfl
  rcases splitSilent (count := skipCount) (left (.active 0 0)).toTrail.steps run with ⟨tail, split, residual⟩ | short
  · have skipSite : PairedComponentSite older (skipped start check leftTicket) (skipped incoming canon rightTicket) check canon := by
      unfold PairedComponentSite at paired ⊢
      dsimp only [skipped]
      rw [← same]
      exact paired.set_store _
    have reachedRecord : ArenaField.callers.get? (skipped start check leftTicket).store caller =
        some (.lower subtask cx args (args.length - 1) ft limits results) := by
      dsimp only [skipped]
      rw [LowerSt.setCallerPosSt, ArenaField.get?_modify_self]
      cases indexed : record.index <;> simp only [Option.isSome, Bool.false_eq_true, ite_false, ite_true]
      all_goals change (ArenaField.callers.get? start.store caller).map _ = _
      all_goals rw [callerRecord]; rfl
    obtain ⟨resultType, indirect⟩ := admittedRefusalGuards callee admitted
    rcases cutComponentResolveRefused (bindings := bindings) caller issue rfl rfl reachedRecord resultType indirect skipSite residual with
      ⟨suffix, more, moved, paired, remaining⟩ | short
    · refine .inl ⟨suffix, _, _, ?_, ?_, rfl, rfl, paired, remaining⟩
      · rw [← count, split, more, ← List.append_assoc, List.replicate_add]; rfl
      · have movement := CallbackPrefix.stationaryTransport (bindings := bindings) left right
        rw [← count, List.replicate_add]
        simpa only [skipCount, List.map_nil, List.append_nil, List.replicate_succ, List.replicate_zero] using
          (CallbackPrefix.transportAppend movement moved).choose_spec.1
    · obtain ⟨shorter, peer, moved, endpoint, leftProgram, rightProgram⟩ := short
      refine .inr ⟨?_, peer, ?_, endpoint, leftProgram, rightProgram⟩
      · rw [← count, split, List.length_append, List.length_replicate]
        omega
      · rw [split]
        simpa only [List.map_nil, List.append_nil] using
          (CallbackPrefix.transportAppend (CallbackPrefix.stationaryTransport left right) moved).choose_spec.1
  · apply Or.inr
    have early := compareQuietShort (bindings := bindings) leftPath rightPath paired ⟨_, leftFocus⟩ ⟨_, rightFocus⟩ run
      (edits.symm ▸ short)
    exact ⟨by rw [← count]; omega, early.2⟩

private abbrev StoreEffects {Result : Type} (body : Session grow sig Result) : Prop :=
  Prog.Every (fun op => componentStoreOp op = true) body

private theorem storeEffects_of_map {Result Projected : Type} (project : Result → Projected)
    (body : Session grow sig Result) {allow : (Eff (core3 grow) (HostState sig)).Op → Prop}
    (mapped : Prog.Every allow (project <$> body)) : Prog.Every allow body := by
  induction body with
  | pure result => exact .pure result
  | op op tail ih =>
    change Prog.Every allow (.op op (fun response => project <$> tail response)) at mapped
    cases mapped with
    | op allowed rest => exact .op allowed fun response => ih response (rest response)

theorem observedArgumentsEffects (caller : CallerId) :
    Prog.Every (fun op => componentStoreOp op = true)
      (Stored.OwnedMemory.observeLowerOnStart Limits.spec Quirks.none caller :
      Session grow sig (List Stored.OwnedMemory.Observed)) := by
  apply storeEffects_of_map (List.map Stored.OwnedMemory.Observed.value)
  rw [Stored.OwnedMemory.projectLowerOnStart]
  exact lowerOnStart_every _ _ _ rfl (fun _ => rfl) (fun _ => rfl)

open ReturnFrame.Occurrence in
theorem cutObservedArguments (callee : ComponentCall.Callee sig) (caller : CallerId)
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
          Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place leading peer place) := by
  let body := (Stored.OwnedMemory.observeLowerOnStart Limits.spec Quirks.none caller : Session grow sig _)
  have lifted : Prog.Every LowerSt.argumentLiftOp body := by
    apply storeEffects_of_map (List.map Stored.OwnedMemory.Observed.value)
    rw [Stored.OwnedMemory.projectLowerOnStart]
    exact lowerOnStart_caller_shape _ _ _
  have framed {Result : Type} {program : Session grow sig Result} (cert : Prog.Every LowerSt.argumentLiftOp program) :
      Prog.Every (storePreserves (fun store => ∀ id, LowerSt.callerShape store id = LowerSt.callerShape start.store id)) program := by
    induction cert with
    | pure result => exact .pure result
    | @op op _ allowed _ ih =>
      refine .op ?_ ih
      cases op <;> try trivial
      exact fun store keeps id => (allowed store id).trans (keeps id)
  exact cutComponentStoreBodyFramed body _ _ (fun _ => observedArgumentsEffects caller) (framed lifted)
    (fun _ => rfl) leftFocus rightFocus paired run

private theorem storeEffectGet : StoreEffects (getStore : Session grow sig (CStore (core3 grow))) :=
  .op rfl fun snapshot => .pure snapshot

private theorem storeEffectModify (update : CStore (core3 grow) → CStore (core3 grow)) :
    StoreEffects (modifyStore update : Session grow sig Unit) :=
  .op rfl fun _ => .pure ()

private theorem storeEffectTrap {Result : Type} (reason : TrapReason) : StoreEffects (trap reason : Session grow sig Result) :=
  .op rfl fun response => nomatch response

private theorem storeEffectOrTrap {Result : Type} (reason : TrapReason) (value : Option Result) :
    StoreEffects (orTrap reason value : Session grow sig Result) := by
  cases value with
  | none => exact storeEffectTrap reason
  | some result => exact .pure result

private theorem storeEffectTrapIf (condition : Bool) (reason : TrapReason) :
    StoreEffects (trapIf condition reason : Session grow sig Unit) := by
  cases condition
  · exact .pure ()
  · exact storeEffectTrap reason

private theorem storeEffectPtrType (cx : LiftLowerContext (core3 grow)) :
    StoreEffects (ptrType cx : Session grow sig AddrType) :=
  storeEffectGet.bind fun _ => .pure _

private theorem storeEffectBounds (cx : LiftLowerContext (core3 grow)) (ptr size : Nat) :
    StoreEffects (checkInBounds cx ptr size : Session grow sig Unit) := by
  unfold checkInBounds memLen memAddr
  exact (Prog.Every.bind (storeEffectOrTrap _ _) fun _ =>
    storeEffectGet.bind fun _ => storeEffectOrTrap _ _).bind fun _ => storeEffectTrapIf _ _

private theorem storeEffectWrite (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (bytes : ByteArray) :
    StoreEffects (writeMem cx ptr bytes : Session grow sig Unit) := by
  unfold writeMem memAddr
  refine (storeEffectOrTrap _ _).bind fun _ => storeEffectGet.bind fun _ => ?_
  split
  · exact storeEffectTrap _
  · exact storeEffectModify _

theorem waitableCalloutDispatch (poll : Bool) (mem : (core3 grow).MemAddr) (inst : InstId) (args : List FlatValue) :
    specDispatch ready base (.hostCallout (waitableCalloutHost poll mem inst) args) =
      (waitableCalloutEntry poll mem inst args >>= waitableCalloutBody poll mem : Session grow sig (Ret (core3 grow))) := by
  change Prog.op (S := Eff (core3 grow) (HostState sig)) Op.currentThread (fun _ => Prog.op Op.get (fun _ => _)) =
    Prog.op (S := Eff (core3 grow) (HostState sig)) Op.currentThread (fun _ => Prog.op Op.get (fun _ => _))
  congr 1
  funext thread
  congr 1
  funext store
  simp only [Prog.bind]
  cases calloutEntry store thread (waitableCalloutHost poll mem inst) with
  | some reason =>
    simp only [trap, Prog.bind]
    congr 1
    funext impossible
    cases impossible
  | none =>
    cases poll <;> rcases args with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩ <;>
      simp [waitableCalloutHost, calloutBody, builtinProg, withArgs2, Builtins.waitableSetPoll,
        Builtins.waitableSetWait, waitableCalloutBody, Prog.bind_assoc]
    all_goals
      simp only [internal, trap, Prog.bind]
      congr 1
      funext impossible
      cases impossible

private theorem storeEffectGetObject {Id Result} (field : ArenaField (core3 grow) Id Result) (idx : Id) :
    StoreEffects (getObj field idx : Session grow sig Result) := by
  unfold getObj
  refine storeEffectGet.bind fun _ => ?_
  split
  · exact .pure _
  · exact storeEffectTrap _

private theorem storeEffectEnterWaitable : StoreEffects (Builtins.enterWaitableBuiltin : Session grow sig InstId) := by
  have current : StoreEffects (currentInst : Session grow sig InstId) := by
    unfold currentInst currentInst? currentTask? getThread getTask
    refine Prog.Every.bind (Prog.Every.bind (Prog.Every.bind (.op rfl fun _ => .pure _) fun thread => ?_)
      fun task => ?_) fun instId => ?_
    · cases thread
      · exact .pure _
      · exact (storeEffectGetObject _ _).bind fun _ => .pure _
    · cases task
      · exact .pure _
      · exact (storeEffectGetObject _ _).bind fun _ => .pure _
    · cases instId
      · exact storeEffectTrap _
      · exact .pure _
  unfold Builtins.enterWaitableBuiltin getInst
  exact current.bind fun _ => (storeEffectGetObject _ _).bind fun _ => (storeEffectTrapIf _ _).bind fun _ => .pure _

private theorem storeEffectHandlesGet (inst : InstId) (index : Nat) :
    StoreEffects (handlesGet inst index : Session grow sig HandleEntry) := by
  unfold handlesGet getInst
  exact (storeEffectGetObject _ _).bind fun _ => storeEffectOrTrap _ _

private theorem waitableCalloutEntryEffects (poll : Bool) (mem : (core3 grow).MemAddr) (inst : InstId)
    (args : List FlatValue) : StoreEffects (waitableCalloutEntry poll mem inst args : Session grow sig WaitableCalloutEntry) := by
  unfold waitableCalloutEntry
  refine Prog.Every.bind (.op rfl fun _ => .pure _) fun _ => storeEffectGet.bind fun _ => ?_
  split
  · exact storeEffectTrap _
  · unfold withArgs2
    split
    · rename_i first second
      refine storeEffectEnterWaitable.bind fun currentId => (storeEffectHandlesGet currentId (flatNat first)).bind fun entry => ?_
      have set : StoreEffects (Builtins.expectWset entry : Session grow sig WsetId) := by
        cases entry <;> first | exact .pure _ | exact storeEffectTrap _
      exact set.bind fun _ => .pure _
    · exact storeEffectTrap _

theorem cutWaitableCalloutEntry (poll : Bool) (mem : (core3 grow).MemAddr) (inst : InstId) (args : List FlatValue)
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
        reached peer suffix True ∧ reached.host = start.host ∧ peer.host = incoming.host := by
  simp only [waitableCalloutDispatch] at leftFocus rightFocus
  exact cutComponentStoreBody _ _ _ (fun _ => waitableCalloutEntryEffects poll mem inst args) leftFocus rightFocus paired run

private theorem waitableWaitSplit (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry) :
    (waitableCalloutBody false mem entry : Session grow sig (Ret (core3 grow))) =
      (waitableWaitDecision entry >>= waitableWaitAfterDecision mem entry) := by
  unfold waitableCalloutBody waitableWaitDecision wsetWait Thread.waitUntilGuest Thread.waitUntil
  simp only [Bool.false_eq_true, ite_false, Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext _
  congr 1
  funext thread
  congr 1
  funext now
  congr 1
  funext early
  cases early <;> simp [waitableWaitAfterDecision, waitableWaitContinue, Prog.bind_assoc]

private theorem storeEffectCurrentThread : StoreEffects (currentThreadId : Session grow sig ThreadId) := by
  unfold currentThreadId
  refine Prog.Every.bind (.op rfl fun _ => .pure _) fun current => ?_
  cases current
  · exact storeEffectTrap _
  · exact .pure _

private theorem cancelCalloutDispatch (async : Bool) (inst : InstId) (args : List FlatValue) :
    specDispatch ready base (.hostCallout (.builtin (.subtaskCancel async) inst) args) =
      (cancelCalloutEntry async inst args >>= cancelCalloutBody async : Session grow sig (Ret (core3 grow))) := by
  change Prog.op (S := Eff (core3 grow) (HostState sig)) Op.currentThread (fun _ => Prog.op Op.get (fun _ => _)) =
    Prog.op (S := Eff (core3 grow) (HostState sig)) Op.currentThread (fun _ => Prog.op Op.get (fun _ => _))
  congr 1
  funext thread
  congr 1
  funext store
  simp only [Prog.bind]
  cases calloutEntry store thread (.builtin (.subtaskCancel async) inst) with
  | some reason =>
    simp only [trap, Prog.bind]
    congr 1
    funext impossible
    cases impossible
  | none =>
    rcases args with _ | ⟨value, _ | ⟨second, rest⟩⟩ <;>
      simp only [calloutBody, builtinProg, withArgs1, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']
    all_goals try
      simp only [internal, trap, Prog.bind]
      congr 1
      funext impossible
      cases impossible
    unfold Builtins.subtaskCancel
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq]
    congr 1
    funext current
    congr 1
    funext entry
    congr 1
    funext subtask
    congr 1
    funext _
    congr 1
    funext _
    congr 1
    funext record
    congr 1
    funext _
    congr 1
    funext _
    congr 1
    funext _
    cases record.state.resolved <;> simp [cancelCalloutBody, Prog.bind_assoc]
    congr 1
    funext resolved
    cases resolved <;> rfl

private theorem cancelCalloutEntryEffects (async : Bool) (inst : InstId) (args : List FlatValue) :
    StoreEffects (cancelCalloutEntry async inst args : Session grow sig (SubtaskId × Option CancelRef)) := by
  unfold cancelCalloutEntry
  refine Prog.Every.bind (.op rfl fun _ => .pure _) fun _ => storeEffectGet.bind fun _ => ?_
  split
  · exact storeEffectTrap _
  · unfold withArgs1
    split
    · rename_i value
      refine storeEffectEnterWaitable.bind fun current => (storeEffectHandlesGet current (flatNat value)).bind fun entry => ?_
      have subtask : StoreEffects (Builtins.expectSubtask entry : Session grow sig SubtaskId) := by
        cases entry <;> first | exact storeEffectTrap _ | (rename_i waitable; cases waitable <;> first | exact .pure _ | exact storeEffectTrap _)
      refine subtask.bind fun subtask => ?_
      have delivered : StoreEffects (Subtask.resolveDelivered subtask : Session grow sig Bool) := storeEffectGet.bind fun _ => .pure _
      refine delivered.bind fun flag => (storeEffectTrapIf flag _).bind fun _ => ?_
      refine (storeEffectGetObject _ _).bind fun record => (storeEffectTrapIf record.cancellationRequested _).bind fun _ => ?_
      have inSet : StoreEffects (Runtime.Waitable.inWaitableSet (.subtask subtask) : Session grow sig Bool) :=
        storeEffectGet.bind fun _ => .pure _
      exact inSet.bind fun flag => (storeEffectTrapIf flag _).bind fun _ => .pure _
    · exact storeEffectTrap _

open ReturnFrame.Occurrence in
private theorem cutCancelCalloutEntry (async : Bool) (inst : InstId) (args : List FlatValue)
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (specDispatch ready base (.hostCallout (.builtin (.subtaskCancel async) inst) args)))
    (rightFocus : incoming.ctl = canon.control (specDispatch ready (LiveDispatch.host bindings base)
      (.hostCallout (.builtin (.subtaskCancel async) inst) args)))
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon (cancelCalloutBody async) (cancelCalloutBody async)
        reached peer suffix True ∧
      (reached.ctl ≠ [] → ∀ place,
        Prefix profile ready (specDispatch ready base) start place leading reached place ∧
        Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place leading peer place) := by
  simp only [cancelCalloutDispatch] at leftFocus rightFocus
  obtain ⟨leading, suffix, reached, peer, split, moved, residual, frontier, _, _, paths⟩ :=
    cutComponentStoreBodyFramed (closed := True) _ _ _ (fun _ => cancelCalloutEntryEffects async inst args)
      (trivialPreserves _) trivial leftFocus rightFocus paired run
  exact ⟨leading, suffix, reached, peer, split, moved, residual, frontier, fun live => (paths live).2⟩

private theorem cancelRequestSplit (async : Bool) (subtask : SubtaskId) (hook : CancelRef) :
    (cancelCalloutBody async (subtask, some hook) : Session grow sig (Ret (core3 grow))) =
      (cancelRequestWrite subtask >>= fun _ => cancelAfterRequestWrite async subtask hook) := by
  calc
    _ = (do
      let thread ← currentThreadId
      modifyStore (Builtins.WaitableSt.requestCancel subtask thread)
      let result ← callRet (.onCancel hook)
      cancelHookReturn async subtask result) := by
        simp only [cancelCalloutBody, Builtins.subtaskCancelRequest, cancelHookReturn, callUnit, bind_assoc]
        congr 1
        funext thread
        congr 1
        funext _
        congr 1
        funext result
        cases result <;> rfl
    _ = _ := by
      simp only [cancelRequestWrite, bind_assoc]
      rfl

theorem cutCancelRequestWrite (async : Bool) (subtask : SubtaskId) (hook : CancelRef)
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
        (fun _ => cancelAfterRequestWrite async subtask hook) reached peer suffix True := by
  simp only [cancelRequestSplit] at leftFocus rightFocus
  have closed : StoreEffects (cancelRequestWrite subtask : Session grow sig Unit) :=
    storeEffectCurrentThread.bind fun _ => storeEffectModify _
  obtain ⟨leading, suffix, reached, peer, split, paths, tail, frontier, _, _⟩ :=
    cutComponentStoreBody (closed := True) _ _ _ (fun _ => closed) leftFocus rightFocus paired run
  exact ⟨leading, suffix, reached, peer, split, paths, tail, frontier⟩

private theorem cancelSyncWaitSplit (async : Bool) (subtask : SubtaskId) :
    (Builtins.subtaskCancelSyncWait async subtask >>= fun _ => cancelFinish subtask : Session grow sig (Ret (core3 grow))) =
      cancelSyncDecision async subtask >>= cancelAfterHookDecision subtask := by
  unfold Builtins.subtaskCancelSyncWait cancelSyncDecision
  simp only [bind_assoc]
  congr 1
  funext resolved
  split
  · unfold Thread.waitUntilGuest Thread.waitUntil
    simp only [bind_assoc]
    congr 1
    funext thread
    congr 1
    funext now
    congr 1
    funext early
    cases early <;> simp [cancelAfterHookDecision, Prog.bind_assoc]
  · rfl

private theorem cancelHookSplit (async : Bool) (subtask : SubtaskId) (result : Ret (core3 grow)) :
    (cancelHookReturn async subtask result : Session grow sig (Ret (core3 grow))) =
      cancelHookDecision async subtask result >>= cancelAfterHookDecision subtask := by
  cases result <;> first
  | exact cancelSyncWaitSplit async subtask
  | simp only [cancelHookReturn, cancelHookDecision, internal, trap, Prog.bind_eq, Prog.bind]
    congr 1
    funext impossible
    cases impossible

private theorem cancelHookDecisionEffects (async : Bool) (subtask : SubtaskId) (result : Ret (core3 grow)) :
    StoreEffects (cancelHookDecision async subtask result : Session grow sig (Option ThreadId)) := by
  cases result <;> try exact storeEffectTrap _
  unfold cancelHookDecision cancelSyncDecision Builtins.subtaskResolvedNow gets
  refine (storeEffectGet.bind fun _ => .pure _).bind fun resolved => ?_
  split
  · refine storeEffectCurrentThread.bind fun _ => (storeEffectGet.bind fun _ => .pure _).bind fun now => ?_
    have chooseEarly : StoreEffects ((if now then choose (.earlyReturn .syncSubtaskCancel) else pure false) : Session grow sig Bool) := by
      cases now
      · exact .pure _
      · exact .op rfl fun _ => .pure _
    refine chooseEarly.bind fun early => ?_
    cases early
    · exact (storeEffectModify _).bind fun _ => .pure _
    · exact .pure _
  · exact .pure _

theorem cutCancelHookDecision (async : Bool) (subtask : SubtaskId) (result : Ret (core3 grow))
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
        reached peer suffix True := by
  simp only [cancelHookSplit] at leftFocus rightFocus
  obtain ⟨leading, suffix, reached, peer, split, paths, residual, frontier, _, _⟩ :=
    cutComponentStoreBody (closed := True) _ _ _ (fun _ => cancelHookDecisionEffects async subtask result)
      leftFocus rightFocus paired run
  exact ⟨leading, suffix, reached, peer, split, paths, residual, frontier⟩

private theorem waitableWaitDecisionEffects (entry : WaitableCalloutEntry) :
    StoreEffects (waitableWaitDecision entry : Session grow sig (Option ThreadId)) := by
  unfold waitableWaitDecision
  refine (storeEffectModify _).bind fun _ => storeEffectCurrentThread.bind fun _ => ?_
  refine ((storeEffectGet.bind fun _ => .pure _)).bind fun now => ?_
  have decision : StoreEffects ((if now then choose (.earlyReturn .waitableSetWait) else pure false) : Session grow sig Bool) := by
    cases now
    · exact .pure _
    · exact .op rfl fun _ => .pure _
  refine decision.bind fun early => ?_
  cases early
  · exact (storeEffectModify _).bind fun _ => .pure _
  · exact .pure _

theorem cutWaitableWaitDecision (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry)
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
        reached peer suffix True ∧ reached.host = start.host ∧ peer.host = incoming.host := by
  simp only [waitableWaitSplit] at leftFocus rightFocus
  exact cutComponentStoreBody _ _ _ (fun _ => waitableWaitDecisionEffects entry) leftFocus rightFocus paired run

open ReturnFrame.Occurrence in
theorem cutCoreCalloutPark (savedProgram : Session grow sig (Ret (core3 grow)))
    {thread core resume frames rest peerFrames peerRest}
    (leftFocus : start.ctl = ⟨some thread, .prog (.op (.block none) (fun _ => savedProgram)), .core core resume :: frames⟩ :: rest)
    (rightFocus : incoming.ctl = ⟨some thread, .prog (.op (.block none) (fun _ => savedProgram)),
      .core core resume :: peerFrames⟩ :: peerRest)
    (paired : PairedComponentSite older start incoming ⟨some thread, .core core resume :: frames, rest⟩
      ⟨some thread, .core core resume :: peerFrames, peerRest⟩)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    (labels = [] ∧ finish = start) ∨
      ∃ suffix,
        let reached := { (start.setCont thread (some ⟨some thread, .prog savedProgram, .core core resume :: frames⟩)) with
          store := StepDefs.threadStatusSt thread .blocked start.store, ctl := rest }
        let peer := { (incoming.setCont thread (some ⟨some thread, .prog savedProgram, .core core resume :: peerFrames⟩)) with
          store := StepDefs.threadStatusSt thread .blocked incoming.store, ctl := peerRest }
        labels = .tau :: suffix ∧ Steps profile ready (specDispatch ready base) reached suffix finish ∧
        HostFrame.Related.Paired older reached peer ∧
        OccurrenceTransport profile ready base bindings start incoming [.tau] [.tau] reached peer ∧
        Trail profile ready (specDispatch ready base) start (some (.active 0 0)) [.tau] reached (some (.saved thread.idx 0)) ∧
        Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming (some (.active 0 0))
          [.tau] peer (some (.saved thread.idx 0)) := by
  cases run with
  | refl => exact .inl ⟨rfl, rfl⟩
  | cons first tail =>
    let saved : Focus (core3 grow) (HostState sig) := .prog savedProgram
    let reached := { (start.setCont thread (some ⟨some thread, saved, .core core resume :: frames⟩)) with
      store := StepDefs.threadStatusSt thread .blocked start.store, ctl := rest }
    let peer := { (incoming.setCont thread (some ⟨some thread, saved, .core core resume :: peerFrames⟩)) with
      store := StepDefs.threadStatusSt thread .blocked incoming.store, ctl := peerRest }
    have checked : Step profile ready (specDispatch ready base) start .tau reached := .block leftFocus
    have canonical : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau peer := .block rightFocus
    obtain ⟨rfl, rfl⟩ := silentStepUnique checked first
    have aligned : HostFrame.Related.Paired older reached peer := by
      obtain ⟨otherFrames, otherRest, shape, parked⟩ := ReturnFrame.Related.Paired.park_under_core paired rfl saved
      simp only [PayloadPrefix.Cursor.control, List.cons.injEq, Activation.mk.injEq, true_and] at shape
      obtain ⟨rfl, rfl⟩ := shape
      have updated := congrArg (StepDefs.threadStatusSt thread .blocked) (HostFrame.Related.Paired.data paired).1
      simpa only [reached, peer, updated, HostFrame.Related.Paired, HostFrame.replace, Config.setCont] using
        ReturnFrame.Related.Paired.set_store parked (StepDefs.threadStatusSt thread .blocked start.store)
    let edit : Edit (core3 grow) (HostState sig) := .block thread.idx
    have leftEdit : transitionEdit start .tau = edit := by rw [transitionEdit, leftFocus]; rfl
    have rightEdit : transitionEdit incoming .tau = edit := by rw [transitionEdit, rightFocus]; rfl
    have trail (place : Option Location) :
        Trail profile ready (specDispatch ready base) start place [.tau] reached (place.bind edit.follow) ∧
        Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place [.tau] peer (place.bind edit.follow) :=
      ⟨.step checked (by rw [leftEdit]; exact .done _ _), .step canonical (by rw [rightEdit]; exact .done _ _)⟩
    refine .inr ⟨_, rfl, tail, aligned, ⟨(·.bind edit.follow), trail, ?_⟩, trail (some (.active 0 0))⟩
    intro previous marks outside
    change OutsideMarks previous (segmentStorage reached) (segmentStorage peer) (marks.map (·.bind edit.follow))
    rw [step_edit checked, step_edit canonical, leftEdit, rightEdit]
    exact outside.edit edit

open ReturnFrame.Occurrence in
theorem cutWaitableWaitPark (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry)
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
  cutCoreCalloutPark (waitableWaitContinue mem entry) leftFocus rightFocus paired run

open ReturnFrame.Occurrence in
private theorem cutCoreCalloutResume (savedProgram : Session grow sig (Ret (core3 grow)))
    {waiter resumer afterResume frames rest core resume savedFrames label next}
    (scheduled : start.ctl = ⟨resumer, .prog (.op (.resumeThread waiter) afterResume), frames⟩ :: rest)
    (found : start.cont? waiter = some ⟨some waiter, .prog savedProgram, .core core resume :: savedFrames⟩)
    (step : Step profile ready (specDispatch ready base) start label next)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ peerFrames peerRest peerSaved,
      let check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨some waiter, .core core resume :: savedFrames,
        ⟨resumer, .prog (afterResume ()), frames⟩ :: rest⟩
      let canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨some waiter, .core core resume :: peerSaved,
        ⟨resumer, .prog (afterResume ()), peerFrames⟩ :: peerRest⟩
      let reached := { (start.setCont waiter none) with
        store := StepDefs.threadStatusSt waiter .running start.store
        ctl := check.control savedProgram }
      let peer := { (incoming.setCont waiter none) with
        store := StepDefs.threadStatusSt waiter .running incoming.store
        ctl := canon.control savedProgram }
      label = .tau ∧ next = reached ∧ PairedComponentSite older reached peer check canon ∧
      OccurrenceTransport profile ready base bindings start incoming [.tau] [.tau] reached peer ∧
      Trail profile ready (specDispatch ready base) start (some (.saved waiter.idx 0)) [.tau] reached (some (.active 0 0)) ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming (some (.saved waiter.idx 0))
        [.tau] peer (some (.active 0 0)) := by
  obtain ⟨peerFrames, peerRest, peerSaved, peerFocus, peerFound, framed⟩ :=
    ReturnFrame.Related.Paired.resume_core paired scheduled found (.prog (afterResume ())) (.prog (.pure (.cancel .none)))
  let check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨some waiter, .core core resume :: savedFrames,
    ⟨resumer, .prog (afterResume ()), frames⟩ :: rest⟩
  let canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨some waiter, .core core resume :: peerSaved,
    ⟨resumer, .prog (afterResume ()), peerFrames⟩ :: peerRest⟩
  let reached := { (start.setCont waiter none) with
    store := StepDefs.threadStatusSt waiter .running start.store
    ctl := check.control savedProgram }
  let peer := { (incoming.setCont waiter none) with
    store := StepDefs.threadStatusSt waiter .running incoming.store
    ctl := canon.control savedProgram }
  have checked : Step profile ready (specDispatch ready base) start .tau reached := .resumeThread scheduled found
  have canonical : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau peer :=
    .resumeThread peerFocus peerFound
  obtain ⟨rfl, rfl⟩ := silentStepUnique checked step
  have updated := congrArg (StepDefs.threadStatusSt waiter .running) (HostFrame.Related.Paired.data paired).1
  have aligned : PairedComponentSite older reached peer check canon := by
    simpa only [PairedComponentSite, reached, peer, check, canon, updated, PayloadPrefix.Cursor.control,
      HostFrame.Related.Paired, HostFrame.replace, Config.setCont] using
      ReturnFrame.Related.Paired.set_store framed (StepDefs.threadStatusSt waiter .running start.store)
  let edit : Edit (core3 grow) (HostState sig) := .resume waiter.idx
  have leftEdit : transitionEdit start .tau = edit := by rw [transitionEdit, scheduled]
  have rightEdit : transitionEdit incoming .tau = edit := by rw [transitionEdit, peerFocus]
  have trail (place : Option Location) :
      Trail profile ready (specDispatch ready base) start place [.tau] reached (place.bind edit.follow) ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place [.tau] peer (place.bind edit.follow) :=
    ⟨.step checked (by rw [leftEdit]; exact .done _ _), .step canonical (by rw [rightEdit]; exact .done _ _)⟩
  refine ⟨peerFrames, peerRest, peerSaved, rfl, rfl, aligned, ⟨(·.bind edit.follow), trail, ?_⟩, ?_⟩
  · intro previous marks outside
    change OutsideMarks previous (segmentStorage reached) (segmentStorage peer) (marks.map (·.bind edit.follow))
    rw [step_edit checked, step_edit canonical, leftEdit, rightEdit]
    exact outside.edit edit
  · change Trail profile ready (specDispatch ready base) start (some (.saved waiter.idx 0)) [.tau] reached (some (.active 0 0)) ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming (some (.saved waiter.idx 0))
        [.tau] peer (some (.active 0 0))
    simpa [edit, Edit.follow, Location.resume] using trail (some (.saved waiter.idx 0))

open ReturnFrame.Occurrence in
theorem cutWaitableWaitResume (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry)
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
  cutCoreCalloutResume (waitableWaitContinue mem entry) scheduled found step paired

open ReturnFrame.Occurrence in
private theorem sharedPushTransport {left right : Config (core3 grow) (HostState sig)}
    {frame : Seg (core3 grow) (HostState sig)}
    (checked : Step profile ready (specDispatch ready base) start .tau left)
    (canonical : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau right)
    (leftEdit : transitionEdit start .tau = .push frame)
    (rightEdit : transitionEdit incoming .tau = .push frame) :
    OccurrenceTransport profile ready base bindings start incoming [.tau] [.tau] left right [some (.active 0 0)] := by
  have shifted (place : Option Location) : place.bind (Edit.push frame).follow = place.map Location.pushed := by
    cases place with
    | none => rfl
    | some place => cases place with
      | active activation _ => cases activation <;> rfl
      | saved => rfl
  refine ⟨(·.map Location.pushed), ?_, ?_⟩
  · intro place
    exact ⟨.step checked (by rw [leftEdit, shifted]; exact .done _ _), .step canonical (by rw [rightEdit, shifted]; exact .done _ _)⟩
  · intro previous marks outside
    rw [step_edit checked, step_edit canonical, leftEdit, rightEdit]
    exact outside.push _ _

open ReturnFrame.Occurrence in
private theorem cutSharedCalloutInstall (target : CanonHost (core3 grow)) (args : List FlatValue)
    {thread core resume frames rest label next}
    (focused : start.ctl = ⟨thread, .core core resume, frames⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout target args)
    (taken : Step profile ready (specDispatch ready base) start label next)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ peerFrames peerRest,
      let caller : Seg (core3 grow) (HostState sig) := .core core resume
      let check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨thread, caller :: frames, rest⟩
      let canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨thread, caller :: peerFrames, peerRest⟩
      let request := Call.hostCallout target args
      let reached := { start with ctl := check.control (specDispatch ready base request) }
      let peer := { incoming with ctl := canon.control (specDispatch ready (LiveDispatch.host bindings base) request) }
      label = .tau ∧ next = reached ∧ PairedComponentSite older reached peer check canon ∧
      OccurrenceTransport profile ready base bindings start incoming [.tau] [.tau] reached peer [some (.active 0 0)] ∧
      segmentAt (segmentStorage reached) (.active 0 0) = some caller ∧
      segmentAt (segmentStorage peer) (.active 0 0) = some caller := by
  let caller : Seg (core3 grow) (HostState sig) := .core core resume
  obtain ⟨peerFrames, peerRest, peerFocus, entered⟩ :=
    ReturnFrame.Related.Paired.push_shared paired focused (.prog (.pure (.cancel .none))) caller
  have peerCalling : (core3 grow).status incoming.store.core core = .callout target args := by
    rw [← (HostFrame.Related.Paired.data paired).1]
    exact calling
  let request := Call.hostCallout target args
  let reached := { start with ctl := ⟨thread, .prog (specDispatch ready base request), caller :: frames⟩ :: rest }
  let peer := { incoming with ctl := ⟨thread, .prog (specDispatch ready (LiveDispatch.host bindings base) request),
    caller :: peerFrames⟩ :: peerRest }
  have checked : Step profile ready (specDispatch ready base) start .tau reached := .coreCallout focused calling
  have canonical : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau peer :=
    .coreCallout peerFocus peerCalling
  have leftEdit : transitionEdit start .tau = .push caller := by simp [transitionEdit, focused, calling, caller]
  have rightEdit : transitionEdit incoming .tau = .push caller := by simp [transitionEdit, peerFocus, peerCalling, caller]
  obtain ⟨labelEq, nextEq⟩ := silentStepUnique checked taken
  exact ⟨peerFrames, peerRest, labelEq, nextEq.symm, entered, sharedPushTransport checked canonical leftEdit rightEdit, rfl, rfl⟩

open ReturnFrame.Occurrence in
theorem cutWaitableCalloutInstall (poll : Bool) (mem : (core3 grow).MemAddr) (inst : InstId) (args : List FlatValue)
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
  cutSharedCalloutInstall _ args focused calling taken paired

open ReturnFrame.Occurrence in
private theorem cutWaitableCorePop {thread core resume frames rest peerFrames peerRest values}
    (leftFocus : start.ctl = ⟨thread, .prog (.pure (.flat values)), .core core resume :: frames⟩ :: rest)
    (rightFocus : incoming.ctl = ⟨thread, .prog (.pure (.flat values)), .core core resume :: peerFrames⟩ :: peerRest)
    (paired : PairedComponentSite older start incoming ⟨thread, .core core resume :: frames, rest⟩
      ⟨thread, .core core resume :: peerFrames, peerRest⟩)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    (labels = [] ∧ finish = start) ∨
      ∃ suffix,
        let reached := { start with ctl := ⟨thread, .core ((core3 grow).resume start.store.core core (.values values)) resume,
          frames⟩ :: rest }
        let peer := { incoming with ctl := ⟨thread, .core ((core3 grow).resume incoming.store.core core (.values values)) resume,
          peerFrames⟩ :: peerRest }
        labels = .tau :: suffix ∧ Steps profile ready (specDispatch ready base) reached suffix finish ∧
        HostFrame.Related.Paired older reached peer ∧
        OccurrenceTransport profile ready base bindings start incoming [.tau] [.tau] reached peer ∧
        Trail profile ready (specDispatch ready base) start (some (.active 0 0)) [.tau] reached none := by
  cases run with
  | refl => exact .inl ⟨rfl, rfl⟩
  | cons first tail =>
    let reached := { start with ctl := ⟨thread, .core ((core3 grow).resume start.store.core core (.values values)) resume, frames⟩ :: rest }
    let peer := { incoming with ctl := ⟨thread, .core ((core3 grow).resume incoming.store.core core (.values values)) resume, peerFrames⟩ :: peerRest }
    have taken : Step profile ready (specDispatch ready base) start .tau reached := .popCore leftFocus
    have canonical : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau peer := .popCore rightFocus
    obtain ⟨rfl, rfl⟩ := silentStepUnique taken first
    have resumed := congrArg (fun store => (core3 grow).resume store.core core (.values values))
      (HostFrame.Related.Paired.data paired).1
    have aligned : HostFrame.Related.Paired older reached peer := by
      obtain ⟨otherFrames, otherRest, shape, popped⟩ :=
        HostFrame.Related.Paired.retarget_core_frame paired rfl
          (.core ((core3 grow).resume start.store.core core (.values values)) resume) start.host incoming.host
      simp only [PayloadPrefix.Cursor.control, List.cons.injEq, Activation.mk.injEq, true_and] at shape
      obtain ⟨rfl, rfl⟩ := shape
      simpa only [reached, peer, resumed, PayloadPrefix.Cursor.control] using popped
    let drop := fun mark : Option Location => mark.bind (Edit.pop : Edit (core3 grow) (HostState sig)).follow
    have leftEdit : transitionEdit start .tau = .pop := by rw [transitionEdit, leftFocus]; rfl
    have rightEdit : transitionEdit incoming .tau = .pop := by rw [transitionEdit, rightFocus]; rfl
    refine .inr ⟨_, rfl, tail, aligned, ⟨drop, ?_, ?_⟩, Trail.pop_core (.active 0 0) leftFocus⟩
    · intro place
      exact ⟨.step taken (by rw [leftEdit]; exact .done _ _), .step canonical (by rw [rightEdit]; exact .done _ _)⟩
    · intro previous marks outside
      change OutsideMarks previous (segmentStorage reached) (segmentStorage peer) (marks.map drop)
      rw [step_edit taken, step_edit canonical, leftEdit, rightEdit]
      exact outside.edit _

private theorem cutFlatCalloutBodyExit {Observation : Type} (code : Observation → Nat)
    {thread core resume frames rest peerFrames peerRest}
    (frontier : ComponentStoreFrontier older ⟨thread, .core core resume :: frames, rest⟩
      ⟨thread, .core core resume :: peerFrames, peerRest⟩ (fun value => .pure (.flat [i32Flat (code value)]))
      (fun value => .pure (.flat [i32Flat (code value)])) start incoming labels True)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    FlatCalloutExit code profile ready base bindings older start incoming labels finish := by
  cases frontier with
  | returned observation checked canonical paired =>
    rcases cutWaitableCorePop (bindings := bindings) checked canonical paired run with done | popped
    · exact .exhausted done.1 done.2
    · obtain ⟨_, split, tail, paired, transport, _⟩ := popped
      exact .rejoined observation checked canonical split tail paired transport
  | pending _ _ _ _ _ boundary =>
    rcases boundary with rfl | ⟨notClosed, _⟩
    · cases run
      exact .exhausted rfl rfl
    · exact (notClosed trivial).elim
  | trapped checked canonical paired => exact .trapped checked canonical paired

private theorem cutWaitableBodyExit {thread core resume frames rest peerFrames peerRest}
    (frontier : ComponentStoreFrontier older ⟨thread, .core core resume :: frames, rest⟩
      ⟨thread, .core core resume :: peerFrames, peerRest⟩ waitableFlatReply waitableFlatReply start incoming labels True)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    WaitableCalloutExit profile ready base bindings older start incoming labels finish :=
  cutFlatCalloutBodyExit Prod.snd frontier run

private theorem takeWaitableEffects (waitable : Waitable) :
    StoreEffects (Waitable.getPendingEvent waitable : Session grow sig AsyncRef.EventTuple) := by
  unfold Waitable.getPendingEvent
  refine storeEffectGet.bind fun _ => ?_
  split
  · exact storeEffectTrap _
  · exact (storeEffectModify _).bind fun _ => .pure _

private theorem cancelDeliveryObservationEffects (subtask : SubtaskId) :
    StoreEffects (cancelDeliveryObservation subtask : Session grow sig (AsyncRef.EventTuple × Nat)) :=
  (takeWaitableEffects _).bind fun _ => (storeEffectGetObject _ _).bind fun _ => .pure _

private theorem selectWaitableEffects (ws : WsetId) :
    StoreEffects (wsetGetPendingEvent ws : Session grow sig AsyncRef.EventTuple) := by
  unfold wsetGetPendingEvent getObj
  refine Prog.Every.bind (storeEffectGet.bind fun _ => ?_) fun record => ?_
  · split
    · exact .pure _
    · exact storeEffectTrap _
  have shuffled : StoreEffects (Canon.shuffle record.elems : Session grow sig (List Waitable)) :=
    .op rfl fun _ => .pure _
  refine shuffled.bind fun _ => (storeEffectModify _).bind fun _ => storeEffectGet.bind fun _ => ?_
  split
  · exact takeWaitableEffects _
  · exact storeEffectTrap _

open ReturnFrame.Occurrence in
theorem cutCancelDelivery (async : Bool) (subtask : SubtaskId)
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
        Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place leading peer place) := by
  have program : (cancelCalloutBody async (subtask, none) : Session grow sig (Ret (core3 grow))) =
      cancelDeliveryObservation subtask >>= waitableFlatReply := by
    simp only [cancelCalloutBody, Builtins.subtaskCancelDeliver, cancelDeliveryObservation, bind_assoc]
    congr 1
  simp only [program] at leftFocus rightFocus
  obtain ⟨leading, suffix, reached, peer, split, moved, residual, frontier, _, _, paths⟩ :=
    cutComponentStoreBodyFramed (closed := True) _ _ _ (fun _ => cancelDeliveryObservationEffects subtask) (trivialPreserves _) trivial
      leftFocus rightFocus paired run
  exact ⟨leading, suffix, reached, peer, split, moved, residual, frontier,
    cutWaitableBodyExit (bindings := bindings) frontier residual, fun live => (paths live).2⟩

private theorem cancelFinishSplit (subtask : SubtaskId) :
    (cancelFinish subtask : Session grow sig (Ret (core3 grow))) =
      cancelFinishObservation subtask >>= fun observation => .pure (.flat [i32Flat observation.2]) := by
  simp only [cancelFinish, cancelFinishObservation, bind_assoc]
  congr 1
  funext _
  congr 1
  funext resolved
  cases resolved
  · rfl
  · simp only [ite_true, Builtins.subtaskCancelDeliver, cancelDeliveryObservation, bind_assoc]
    congr 1

private theorem cancelFinishObservationEffects (subtask : SubtaskId) :
    StoreEffects (cancelFinishObservation subtask : Session grow sig (Option AsyncRef.EventTuple × Nat)) := by
  unfold cancelFinishObservation Builtins.subtaskResolvedNow gets
  refine (storeEffectModify _).bind fun _ => (storeEffectGet.bind fun _ => .pure _).bind fun resolved => ?_
  split
  · refine (cancelDeliveryObservationEffects subtask).bind fun observation => ?_
    cases observation
    exact .pure _
  · exact .pure _

open ReturnFrame.Occurrence in
theorem cutCancelFinish (subtask : SubtaskId)
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
        Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place leading peer place) := by
  simp only [cancelFinishSplit] at leftFocus rightFocus
  obtain ⟨leading, suffix, reached, peer, split, moved, residual, frontier, _, _, paths⟩ :=
    cutComponentStoreBodyFramed (closed := True) _ _ _ (fun _ => cancelFinishObservationEffects subtask)
      (trivialPreserves _) trivial leftFocus rightFocus paired run
  exact ⟨leading, suffix, reached, peer, split, moved, residual,
    cutFlatCalloutBodyExit Prod.snd frontier residual, fun live => (paths live).2⟩

open ReturnFrame.Occurrence in
theorem cutResumedCancelFinish (subtask : SubtaskId)
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
          (.tau :: leading) peer (some (.active 0 0))) := by
  obtain ⟨_, _, _, rfl, rfl, site, resumed, leftMark, rightMark⟩ :=
    cutCoreCalloutResume (bindings := bindings) (cancelFinish subtask) scheduled found step paired
  obtain ⟨leading, suffix, reached, peer, split, body, residual, exit, retained⟩ :=
    cutCancelFinish (bindings := bindings) subtask rfl rfl site run
  have joined := (CallbackPrefix.transportAppend resumed body).choose_spec.1
  refine ⟨leading, suffix, reached, peer, by rw [split]; rfl, ?_, residual, exit, ?_⟩
  · simpa only [List.singleton_append, List.map_nil, List.append_nil] using joined
  · intro live
    obtain ⟨left, right⟩ := retained live (.active 0 0)
    exact ⟨leftMark.append left.toTrail, rightMark.append right.toTrail⟩

theorem waitableSelectionEffects (poll : Bool) (ws : WsetId) :
    Prog.Every (fun op => componentStoreOp op = true)
      ((if poll then wsetPoll ws else wsetGetPendingEvent ws) : Session grow sig AsyncRef.EventTuple) := by
  cases poll with
  | false => exact selectWaitableEffects ws
  | true =>
    change StoreEffects (wsetPoll ws : Session grow sig AsyncRef.EventTuple)
    unfold wsetPoll wsetHasPendingEvent gets
    refine (storeEffectGet.bind fun _ => .pure _).bind fun _ => ?_
    split
    · exact selectWaitableEffects ws
    · exact .pure _

private theorem waitableBufferEffects (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (event : AsyncRef.EventTuple) :
    StoreEffects (unpackEvent cx ptr event : Session grow sig Nat) := by
  unfold unpackEvent checkAligned
  exact (storeEffectTrapIf _ _).bind fun _ => (storeEffectBounds _ _ _).bind fun _ =>
    (storeEffectWrite _ _ _).bind fun _ => (storeEffectWrite _ _ _).bind fun _ => .pure _

open ReturnFrame.Occurrence in
theorem cutWaitableWaitDelivery (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry)
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
        Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place leading peer place) := by
  let body : Session grow sig (AsyncRef.EventTuple × Nat) := do
    modifyStore (CStore.wsetDecWaitingSt entry.set)
    let event ← wsetGetPendingEvent entry.set
    let code ← unpackEvent (Builtins.eventCx mem entry.inst) entry.ptr event
    pure (event, code)
  have program : (waitableWaitContinue mem entry : Session grow sig (Ret (core3 grow))) = body >>= waitableFlatReply := by
    simp [body, waitableWaitContinue, waitableFlatReply, Prog.bind_assoc]
  have certified : StoreEffects body :=
    (storeEffectModify _).bind fun _ => (selectWaitableEffects entry.set).bind fun event =>
      (waitableBufferEffects (Builtins.eventCx mem entry.inst) entry.ptr event).bind fun _ => .pure _
  rw [program] at leftFocus rightFocus
  obtain ⟨leading, suffix, reached, peer, split, moved, residual, frontier, _, _, retained⟩ :=
    cutComponentStoreBodyFramed (bindings := bindings) body _ _ (closed := True) (fun _ => certified)
      (trivialPreserves body) trivial leftFocus rightFocus paired run
  exact ⟨leading, suffix, reached, peer, split, moved, residual, frontier, cutWaitableBodyExit frontier residual,
    fun live => (retained live).2⟩

open ReturnFrame.Occurrence in
theorem cutResumedWaitDelivery (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry)
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
          (.tau :: leading) peer (some (.active 0 0))) := by
  obtain ⟨_, _, _, rfl, rfl, site, resumed, leftMark, rightMark⟩ :=
    cutWaitableWaitResume (bindings := bindings) mem entry scheduled found step paired
  obtain ⟨leading, suffix, reached, peer, split, body, residual, frontier, exit, retained⟩ :=
    cutWaitableWaitDelivery (bindings := bindings) mem entry rfl rfl site run
  have joined := (CallbackPrefix.transportAppend resumed body).choose_spec.1
  refine ⟨leading, suffix, reached, peer, _, _, by rw [split]; rfl, ?_, residual, frontier, exit, ?_⟩
  · simpa only [List.singleton_append, List.map_nil, List.append_nil] using joined
  · intro live
    obtain ⟨left, right⟩ := retained live (.active 0 0)
    exact ⟨leftMark.append left.toTrail, rightMark.append right.toTrail⟩

private theorem pollCalloutDispatch (mem : (core3 grow).MemAddr) (inst : InstId) (args : List FlatValue) :
    specDispatch ready base (.hostCallout (waitableCalloutHost true mem inst) args) =
      (pollCalloutObservation mem inst args >>= waitableFlatReply : Session grow sig (Ret (core3 grow))) := by
  rw [waitableCalloutDispatch]
  change (waitableCalloutEntry true mem inst args >>= fun entry => waitableCalloutBody true mem entry) = _
  simp [pollCalloutObservation, waitableCalloutBody, waitableFlatReply, Prog.bind_assoc]

open ReturnFrame.Occurrence in
private theorem cutPollCalloutBody (mem : (core3 grow).MemAddr) (inst : InstId) (args : List FlatValue)
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (specDispatch ready base (.hostCallout (waitableCalloutHost true mem inst) args)))
    (rightFocus : incoming.ctl = canon.control (specDispatch ready (LiveDispatch.host bindings base)
      (.hostCallout (waitableCalloutHost true mem inst) args)))
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon waitableFlatReply waitableFlatReply reached peer suffix True ∧
      reached.host = start.host ∧ peer.host = incoming.host ∧
      (reached.ctl ≠ [] → ∀ place,
        Prefix profile ready (specDispatch ready base) start place leading reached place ∧
        Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place leading peer place) := by
  simp only [pollCalloutDispatch] at leftFocus rightFocus
  let body : Session grow sig (AsyncRef.EventTuple × Nat) := pollCalloutObservation mem inst args
  have certified : StoreEffects body := by
    exact (waitableCalloutEntryEffects true mem inst args).bind fun entry =>
      (waitableSelectionEffects true entry.set).bind fun event =>
        (waitableBufferEffects (Builtins.eventCx mem entry.inst) entry.ptr event).bind fun _ => .pure _
  obtain ⟨leading, suffix, reached, peer, split, moved, residual, frontier, leftHost, rightHost, paths⟩ :=
    cutComponentStoreBodyFramed body waitableFlatReply waitableFlatReply (closed := True) (fun _ => certified)
      (trivialPreserves body) trivial leftFocus rightFocus paired run
  exact ⟨leading, suffix, reached, peer, split, moved, residual, frontier, leftHost, rightHost, fun live => (paths live).2⟩

open ReturnFrame.Occurrence in
private theorem cutWaitCalloutDecision (mem : (core3 grow).MemAddr) (inst : InstId) (args : List FlatValue)
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (specDispatch ready base (.hostCallout (waitableCalloutHost false mem inst) args)))
    (rightFocus : incoming.ctl = canon.control (specDispatch ready (LiveDispatch.host bindings base)
      (.hostCallout (waitableCalloutHost false mem inst) args)))
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer,
      labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ComponentStoreFrontier older check canon (fun result : WaitableCalloutEntry × Option ThreadId => waitableWaitAfterDecision mem result.1 result.2)
        (fun result => waitableWaitAfterDecision mem result.1 result.2) reached peer suffix True ∧
      (reached.ctl ≠ [] → ∀ place,
        Prefix profile ready (specDispatch ready base) start place leading reached place ∧
        Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place leading peer place) := by
  let body : Session grow sig (WaitableCalloutEntry × Option ThreadId) := do
    let entry ← waitableCalloutEntry false mem inst args
    let decision ← waitableWaitDecision entry
    pure (entry, decision)
  let next := fun result : WaitableCalloutEntry × Option ThreadId => waitableWaitAfterDecision (sig := sig) mem result.1 result.2
  have program : specDispatch ready base (.hostCallout (waitableCalloutHost false mem inst) args) = body >>= next := by
    rw [waitableCalloutDispatch]
    simp only [body, next, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']
    congr 1
    funext entry
    exact waitableWaitSplit mem entry
  rw [program] at leftFocus
  rw [waitableCalloutDispatch] at rightFocus
  rw [waitableCalloutDispatch] at program
  rw [program] at rightFocus
  have certified : StoreEffects body :=
    (waitableCalloutEntryEffects false mem inst args).bind fun entry => (waitableWaitDecisionEffects entry).bind fun _ => .pure _
  obtain ⟨leading, suffix, reached, peer, split, moved, residual, frontier, _, _, paths⟩ :=
    cutComponentStoreBodyFramed body next next (closed := True) (fun _ => certified)
      (trivialPreserves body) trivial leftFocus rightFocus paired run
  exact ⟨leading, suffix, reached, peer, split, moved, residual, frontier, fun live => (paths live).2⟩

open ReturnFrame.Occurrence in
private theorem retainComparedOccurrences {left right reached peer} {checked canonical leading canonLeading : Trace grow sig} {introduced}
    (install : OccurrenceTransport profile ready base bindings start incoming checked canonical left right introduced)
    (retained : ∀ place,
      Prefix profile ready (specDispatch ready base) left place leading reached place ∧
      Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) right place canonLeading peer place) :
    OccurrenceTransport profile ready base bindings start incoming (checked ++ leading) (canonical ++ canonLeading) reached peer introduced := by
  obtain ⟨shift, trails, framed⟩ := install
  refine ⟨shift, ?_, ?_⟩
  · intro mark
    obtain ⟨lhs, rhs⟩ := trails mark
    cases location : shift mark with
    | none =>
      rw [location] at lhs rhs
      obtain ⟨left, right⟩ := retained (.active 0 0)
      exact ⟨lhs.append (.absent (prefix_survives left).1), rhs.append (.absent (prefix_survives right).1)⟩
    | some place =>
      rw [location] at lhs rhs
      obtain ⟨left, right⟩ := retained place
      exact ⟨lhs.append left.toTrail, rhs.append right.toTrail⟩
  · intro previous marks before place unmarked first second leftAt rightAt
    obtain ⟨left, right⟩ := retained place
    exact framed previous marks before place unmarked first second
      ((prefix_survives left).2.symm.trans leftAt) ((prefix_survives right).2.symm.trans rightAt)

open ReturnFrame.Occurrence in
private theorem retainInstalledWaitable {left right reached peer} {leading : Trace grow sig}
    (install : OccurrenceTransport profile ready base bindings start incoming [.tau] [.tau] left right [some (.active 0 0)])
    (retained : ∀ place,
      Prefix profile ready (specDispatch ready base) left place leading reached place ∧
      Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) right place leading peer place) :
    OccurrenceTransport profile ready base bindings start incoming (.tau :: leading) (.tau :: leading) reached peer [some (.active 0 0)] :=
  retainComparedOccurrences install retained

open ReturnFrame.Occurrence in
theorem cutPublicPoll (mem : (core3 grow).MemAddr) (inst : InstId) (args : List FlatValue)
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
      WaitableCalloutExit profile ready base bindings older reached peer suffix finish := by
  obtain ⟨peerFrames, peerRest, rfl, rfl, site, install, _, _⟩ :=
    cutWaitableCalloutInstall (bindings := bindings) true mem inst args focused calling step paired
  obtain ⟨leading, suffix, reached, peer, split, moved, residual, frontier, _, _, retained⟩ :=
    cutPollCalloutBody (bindings := bindings) mem inst args rfl rfl site run
  obtain ⟨move, whole, _⟩ := CallbackPrefix.transportAppend install moved
  refine ⟨peerFrames, peerRest, leading, suffix, reached, peer, by rw [split]; rfl,
    ⟨move (some (.active 0 0)), whole⟩, ?_, residual, frontier, ?_⟩
  · exact fun live => retainInstalledWaitable install (retained live)
  · exact cutWaitableBodyExit frontier residual

open ReturnFrame.Occurrence in
theorem cutPublicWaitDecision (mem : (core3 grow).MemAddr) (inst : InstId) (args : List FlatValue)
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
        (fun result => waitableWaitAfterDecision mem result.1 result.2) reached peer suffix True := by
  obtain ⟨peerFrames, peerRest, rfl, rfl, installedSite, install, _, _⟩ :=
    cutWaitableCalloutInstall (bindings := bindings) false mem inst args focused calling step paired
  obtain ⟨leading, suffix, reached, peer, split, moved, actual, frontier, retained⟩ :=
    cutWaitCalloutDecision (bindings := bindings) mem inst args rfl rfl installedSite run
  obtain ⟨move, whole, _⟩ := CallbackPrefix.transportAppend install moved
  exact ⟨peerFrames, peerRest, leading, suffix, reached, peer, by rw [split]; rfl,
    ⟨move (some (.active 0 0)), whole⟩, fun live => retainInstalledWaitable install (retained live), actual, frontier⟩

open ReturnFrame.Occurrence in
theorem cutPublicCancelEntry (async : Bool) (inst : InstId) (args : List FlatValue)
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
      ComponentStoreFrontier older check canon (cancelCalloutBody async) (cancelCalloutBody async) reached peer suffix True := by
  obtain ⟨peerFrames, peerRest, rfl, rfl, site, install, _, _⟩ :=
    cutSharedCalloutInstall (bindings := bindings) _ args focused calling step paired
  obtain ⟨leading, suffix, reached, peer, split, moved, actual, frontier, retained⟩ :=
    cutCancelCalloutEntry (bindings := bindings) async inst args rfl rfl site run
  obtain ⟨move, whole, _⟩ := CallbackPrefix.transportAppend install moved
  exact ⟨peerFrames, peerRest, leading, suffix, reached, peer, by rw [split]; rfl,
    ⟨move (some (.active 0 0)), whole⟩, fun live => retainInstalledWaitable install (retained live), actual, frontier⟩

theorem cutWaitableDelivery (poll : Bool) (ws : WsetId) (cx : LiftLowerContext (core3 grow)) (ptr : Nat)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
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
      reached.host = start.host ∧ peer.host = incoming.host := by
  let body : Session grow sig (AsyncRef.EventTuple × Nat) :=
    (if poll then wsetPoll ws else wsetGetPendingEvent ws) >>= fun event =>
      unpackEvent cx ptr event >>= fun code => .pure (event, code)
  have certified : StoreEffects body :=
    (waitableSelectionEffects poll ws).bind fun event => (waitableBufferEffects cx ptr event).bind fun code => .pure (event, code)
  have rearrange (next : Nat → Session grow sig (Ret (core3 grow))) :
      (body >>= next ∘ Prod.snd) = (if poll then wsetPoll ws else wsetGetPendingEvent ws) >>= fun event =>
        unpackEvent cx ptr event >>= next := by
    simp only [body, Prog.bind_eq, Prog.bind_assoc, Prog.pure_bind', Function.comp_apply]
  exact cutComponentStoreBody body (checkNext ∘ Prod.snd) (canonNext ∘ Prod.snd) (fun _ => certified)
    (by simpa only [rearrange] using leftFocus) (by simpa only [rearrange] using rightFocus) paired run

private theorem resultLowerEffects (cx : LiftLowerContext (core3 grow)) (cursor : FlatCursor)
    (results : Nat) (indirect : results ≤ 1) (handle : Option Nat) :
    StoreEffects (lowerFlatValues Limits.spec Quirks.none cx results
      [handle.elim (.variant 1 none) (fun value => .variant 0 (some (Value.Val.u32 value)))]
      [ComponentCall.resultType] (some cursor) : Session grow sig (List FlatValue)) := by
  unfold lowerFlatValues
  refine (storeEffectPtrType _).bind fun width => ?_
  have widthCount : (ABI.flattenTypes width [ComponentCall.resultType]).length = 2 := by
    simp [ComponentCall.resultType, ABI.flattenTypes, ABI.flatten, ABI.flattenOption, ABI.flattenPrimitive]
  simp only [widthCount, show results < 2 by omega, ite_true]
  have spill : StoreEffects (spillPointer cx width (ABI.layout width (.tuple [ComponentCall.resultType]))
      (some cursor) : Session grow sig (Nat × List FlatValue)) := by
    unfold spillPointer FlatCursor.next
    refine Prog.Every.bind ?_ fun _ => .pure _
    split
    · exact .pure _
    · exact storeEffectTrap _
  refine spill.bind fun (ptr, _) => (storeEffectTrapIf _ _).bind fun _ =>
    (storeEffectBounds _ _ _).bind fun _ => Prog.Every.bind ?_ fun _ => .pure _
  cases handle with
  | none =>
    simp only [Option.elim, store, storeTuple, ComponentCall.resultType, storeOpt]
    refine (storeEffectPtrType _).bind fun _ => Prog.Every.bind ?_ fun _ => .pure _
    refine (storeEffectPtrType _).bind fun _ => ?_
    exact ((storeEffectWrite _ _ _).bind fun _ => .pure _).bind fun _ => .pure _
  | some handle =>
    simp only [Option.elim, store, storeTuple, ComponentCall.resultType, storeOpt]
    refine (storeEffectPtrType _).bind fun _ => Prog.Every.bind ?_ fun _ => .pure _
    refine (storeEffectPtrType _).bind fun _ => ?_
    unfold storeVariantHead
    refine ((storeEffectWrite _ _ _).bind fun _ => .pure _).bind fun _ => ?_
    exact storeEffectWrite _ _ _

private theorem progressEffects (subtask : SubtaskId) :
    StoreEffects (maybeOnProgress subtask : Session grow sig Unit) := by
  unfold maybeOnProgress getObj
  simp only [Prog.bind_eq, Prog.bind_assoc]
  refine storeEffectGet.bind fun _ => ?_
  split
  · simp only [Prog.pure_eq, Prog.pure_bind']
    split
    · exact storeEffectModify _
    · exact .pure ()
  · exact .op rfl fun response => nomatch response

open AsyncRef in
private theorem resultEffects (subtask : SubtaskId) (cx : LiftLowerContext (core3 grow))
    (cursor : FlatCursor) (results : Nat) (indirect : results ≤ 1) (handle : Option Nat) :
    StoreEffects ((do
      maybeOnProgress subtask
      let flat ← lowerFlatValues Limits.spec Quirks.none cx results
        [handle.elim (.variant 1 none) (fun value => .variant 0 (some (Value.Val.u32 value)))]
        [ComponentCall.resultType] (some cursor)
      Subtask.resolve subtask .returned flat) : Session grow sig Unit) :=
  (progressEffects subtask).bind fun _ =>
    (resultLowerEffects cx cursor results indirect handle).bind fun _ => storeEffectModify _

open AsyncRef in
theorem cutAdmittedRefusalResult (callee : ComponentCall.Callee sig) (caller : CallerId) (issue : Scheduled.Issue)
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
    ComponentEarlyPrefix profile ready base bindings older check canon start incoming labels finish (if record.index.isSome then 8 else 7) := by
  rcases cutAdmittedRefusal (bindings := bindings) callee caller issue record leftFocus rightFocus callerRecord live admitted paired run with
    ⟨tail, observed, observedPeer, split, moved, left, right, aligned, residual⟩ | short
  · obtain ⟨_, indirect⟩ := admittedRefusalGuards callee admitted
    let body : Session grow sig Unit := do
      maybeOnProgress subtask
      let flat ← lowerFlatValues Limits.spec Quirks.none cx results [.variant 1 none]
        [ComponentCall.resultType] (some ⟨args, args.length - 1⟩)
      Subtask.resolve subtask .returned flat
    have leftBody : observed.ctl = check.control (body >>= fun _ => .pure (.cancel .none)) := by
      simpa only [body, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq] using left
    have rightBody : observedPeer.ctl = canon.control (body >>= fun _ => .pure (.cancel .none)) := by
      simpa only [body, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq] using right
    have site : PairedComponentSite older observed observedPeer check canon := by
      unfold PairedComponentSite
      obtain ⟨_, _, focus, normalized⟩ := aligned.retarget left (.prog (.pure (.cancel .none))) observed.host observedPeer.host
      rw [right] at focus
      simp only [PayloadPrefix.Cursor.control, List.cons.injEq, Activation.mk.injEq, true_and] at focus
      obtain ⟨⟨threadEq, framesEq⟩, restEq⟩ := focus
      simpa only [PayloadPrefix.Cursor.control, ← threadEq, ← framesEq, ← restEq] using normalized
    obtain ⟨leading, suffix, reached, peer, tailSplit, finishMove, remaining, frontier, _, _⟩ :=
      cutComponentStoreBody (bindings := bindings) (closed := True) body _ _ (fun _ => resultEffects subtask cx _ results indirect none)
        leftBody rightBody site residual
    refine .inl ⟨List.replicate (if record.index.isSome then 8 else 7) .tau ++ leading,
      suffix, reached, peer, ?_, ?_, ?_, remaining, frontier⟩
    · rw [split, tailSplit, List.append_assoc]
    · rw [split, tailSplit, List.length_append, List.length_append, List.length_replicate]
      split <;> omega
    · simpa only [List.map_nil, List.append_nil] using (CallbackPrefix.transportAppend moved finishMove).choose_spec.1
  · exact .inr short

open AsyncRef in
private def acceptedResultBody (subtask : SubtaskId) (cx : LiftLowerContext (core3 grow))
    (args : FlatCursor) (results handle : Nat) : Session grow sig Unit := do
  maybeOnProgress subtask
  let flat ← lowerFlatValues Limits.spec Quirks.none cx results [.variant 0 (some (Value.Val.u32 handle))]
    [ComponentCall.resultType] (some args)
  Subtask.resolve subtask .returned flat

open AsyncRef ReturnFrame.Occurrence in
private theorem acceptedResolvePath (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (ticket : Nat) (caller : CallerId) (tree : Stored.OwnedMemory.Tree sig)
    {handle : Nat} {writer : Stored.OwnedMemory.Claims.State sig}
    {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat}
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (ComponentCall.resolveTree ticket caller tree))
    (registered : start.host.writer.register tree = .ok writer) (expected : handle = writer.accepted.length)
    (room : handle < 2 ^ 32)
    (record : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (resultType : ft.result = some ComponentCall.resultType) :
    ComponentQuietPath profile ready dispatch cursor start [id, id]
      { start with ctl := cursor.control (acceptedResultBody subtask cx ⟨args, pos⟩ results handle >>=
          fun _ => ComponentCall.completeResolvedTree ticket tree handle) } := by
  cases cursor with
  | mk thread frames rest =>
    let lower := lowerOnResolve Limits.spec Quirks.none caller (some [.variant 0 (some (Value.Val.u32 handle))]) >>=
      fun _ => ComponentCall.completeResolvedTree (grow := grow) ticket tree handle
    have enter : Step profile ready dispatch start .tau { start with ctl := ⟨thread, .prog lower, frames⟩ :: rest } := by
      have read := Step.hostGet (prof := profile) (hr := ready) (dispatch := dispatch) focused
      simpa only [ComponentCall.resolveTree, Prog.bind, registered, ← expected, Nat.not_le.mpr room, ite_false] using read
    refine .step enter (by rw [transitionEdit, focused]; rfl) ?_
    have read := Step.get (prof := profile) (hr := ready) (dispatch := dispatch)
      (m := { start with ctl := ⟨thread, .prog lower, frames⟩ :: rest }) rfl
    simp only [lower, Prog.bind, record, resultType, Option.toList, Quirks.none, Bool.false_eq_true,
      ite_false, Prog.pure_eq] at read
    exact .step read rfl (.done _)

theorem cutSuccessfulPayload (callee : ComponentCall.Callee sig) (caller : CallerId)
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
    ComponentEarlyPrefix profile ready base bindings older check canon start incoming labels finish 2 := by
  dsimp only
  simp only [ComponentCall.acceptPayload, validated] at leftFocus rightFocus
  have same : start.store = incoming.store := (HostFrame.Related.Paired.data paired).1
  have left := acceptedResolvePath (profile := profile) (ready := ready) (specDispatch ready base)
    leftTicket caller _ check leftFocus leftLive leftHandle room record resultType
  have right := acceptedResolvePath (profile := profile) (ready := ready) (specDispatch ready (LiveDispatch.host bindings base))
    rightTicket caller _ canon rightFocus rightLive rightHandle room (same ▸ record) resultType
  rcases splitSilent (count := 2) (left.track (.active 0 0)).toTrail.steps run with ⟨suffix, split, residual⟩ | short
  · have transport := CallbackPrefix.stationaryTransport (bindings := bindings) left.track right.track
    let body : Session grow sig Unit := acceptedResultBody subtask cx ⟨args, pos⟩ results handle
    let next (ticket : Nat) (_ : Unit) := ComponentCall.completeResolvedTree (grow := grow) ticket
      (.node callee.tag valid children) handle
    let leftBody := { start with ctl := check.control (body >>= next leftTicket) }
    let rightBody := { incoming with ctl := canon.control (body >>= next rightTicket) }
    obtain ⟨leading, trailing, reached, peer, bodySplit, moved, remaining, frontier, leftHost, rightHost⟩ :=
      cutComponentStoreBody (bindings := bindings) (closed := True)
        (start := leftBody) (incoming := rightBody) body (next leftTicket) (next rightTicket)
        (fun _ => resultEffects subtask cx _ results indirect (some handle))
        rfl rfl paired residual
    refine .inl ⟨List.replicate 2 .tau ++ leading, trailing, reached, peer, ?_, ?_, ?_, remaining, frontier, leftHost, rightHost⟩
    · rw [split, bodySplit, List.append_assoc]
    · rw [split, bodySplit, List.length_append, List.length_append, List.length_replicate]
      omega
    · simpa only [List.map_nil, List.append_nil, List.length_cons, List.length_nil] using
        (CallbackPrefix.transportAppend transport moved).choose_spec.1
  · exact .inr (compareQuietShort left right paired ⟨_, leftFocus⟩ ⟨_, rightFocus⟩ run short)

private theorem publishedHandleLookup {tree : Stored.OwnedMemory.Tree sig} {handle : Nat}
    {before writer : Stored.OwnedMemory.Claims.State sig} (registered : before.register tree = .ok writer)
    (expected : handle = writer.accepted.length) (room : handle < 2 ^ 32) :
    Stored.Endpoints.Core.childFromHistory writer.accepted (BitVec.ofNat 32 handle) = some tree := by
  rw [(Stored.OwnedMemory.Claims.register_claims registered).1] at expected ⊢
  unfold Stored.Endpoints.Core.childFromHistory
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt room, expected]
  simp [guard]

open ReturnFrame.Occurrence in
private theorem publicationPath (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (ticket handle : Nat) (tree : Stored.OwnedMemory.Tree sig) (writer : Stored.OwnedMemory.Claims.State sig)
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (ComponentCall.completeResolvedTree ticket tree handle))
    (registered : start.host.writer.register tree = .ok writer)
    (expected : handle = writer.accepted.length) (room : handle < 2 ^ 32) :
    ComponentQuietPath profile ready dispatch cursor start [id, id, id, id]
      { start with
        host := (({ start.host with writer } : HostState sig).record (.published ticket handle)).record
          (.returned ticket handle)
        ctl := cursor.control (.pure (.cancel .none)) } := by
  subst handle
  cases cursor with
  | mk thread frames rest =>
    have read := Step.hostGet (prof := profile) (hr := ready) (dispatch := dispatch) focused
    simp only [Prog.bind, registered, Option.any, bne_self_eq_false, Bool.false_eq_true, ite_false, Nat.not_le.mpr room] at read
    refine .step read (by rw [transitionEdit, focused]; rfl) ?_
    exact .step (.hostSet rfl) rfl (.step (.hostGet rfl) rfl (.step (.hostSet rfl) rfl (.done _)))

theorem cutComponentPublication {tree : Stored.OwnedMemory.Tree sig} {handle leftTicket rightTicket : Nat}
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
    ComponentEarlyPrefix profile ready base bindings older leftCursor rightCursor start incoming labels finish 4 := by
  dsimp only
  have left := publicationPath (profile := profile) (ready := ready) (specDispatch ready base)
    leftTicket handle tree leftWriter leftCursor leftFocus leftLive leftHandle room
  have right := publicationPath (profile := profile) (ready := ready) (specDispatch ready (LiveDispatch.host bindings base))
    rightTicket handle tree rightWriter rightCursor rightFocus rightLive rightHandle room
  rcases splitSilent (count := 4) (left.track (.active 0 0)).toTrail.steps run with ⟨suffix, split, residual⟩ | short
  · refine .inl ⟨suffix, split, CallbackPrefix.stationaryTransport left.track right.track, ?_,
      publishedHandleLookup leftLive leftHandle room, publishedHandleLookup rightLive rightHandle room, residual⟩
    have replaceHost {first second : Config (core3 grow) (HostState sig)}
        (paired : ReturnFrame.Related.Paired older first second) (host : HostState sig) :
        ReturnFrame.Related.Paired older (HostFrame.replace first host) (HostFrame.replace second host) := by
      cases paired with
      | mk control blocked => exact .mk control blocked
    exact replaceHost site _
  · exact .inr (compareQuietShort left right site ⟨_, leftFocus⟩ ⟨_, rightFocus⟩ run short)

theorem cutSuccessfulPublication (callee : ComponentCall.Callee sig) (caller : CallerId)
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
      ComponentAcceptedFrontier older check canon (.node callee.tag valid children) handle reached peer suffix := by
  rcases cutSuccessfulPayload (bindings := bindings) callee caller first payload children validated
      leftFocus rightFocus paired record resultType indirect leftLive rightLive leftHandle rightHandle room run with
    ⟨leading, suffix, reached, peer, split, _, initialTransport, residual, frontier, leftHost, rightHost⟩ | early
  · cases frontier with
    | pending _ _ _ _ site boundary =>
      rcases boundary with exhausted | impossible
      · exact ⟨leading, suffix, reached, peer, split, initialTransport, residual, .pending site exhausted⟩
      · exact False.elim (impossible.1 trivial)
    | trapped checked canonical site =>
      exact ⟨leading, suffix, reached, peer, split, initialTransport, residual, .trapped checked canonical site⟩
    | returned _ checked canonical site =>
      rcases cutComponentPublication (bindings := bindings) checked canonical site
          (leftHost ▸ leftLive) (rightHost ▸ rightLive) leftHandle rightHandle room residual with
        ⟨trailing, used, publication, pair, leftLookup, rightLookup, remaining⟩ | early
      · refine ⟨leading ++ [.tau, .tau, .tau, .tau], trailing, _, _, ?_, ?_, remaining,
          .published rfl rfl pair leftLookup rightLookup⟩
        · rw [split, used, List.append_assoc]
        · simpa only [List.map_nil, List.append_nil] using (CallbackPrefix.transportAppend initialTransport publication).choose_spec.1
      · obtain ⟨_, finalPeer, moved, endpoint, _, _⟩ := early
        refine ⟨leading ++ suffix, [], finish, finalPeer, ?_, ?_, .refl _, .pending endpoint rfl⟩
        · simpa only [List.append_nil] using split
        · simpa only [List.map_nil, List.append_nil] using (CallbackPrefix.transportAppend initialTransport moved).choose_spec.1
  · obtain ⟨_, peer, moved, endpoint, _, _⟩ := early
    exact ⟨labels, [], finish, peer, (List.append_nil _).symm, moved, .refl _, .pending endpoint rfl⟩

set_option maxHeartbeats 2000000 in
private theorem labelledStepUnique {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {before left right : Config (core3 grow) (HostState sig)} {label}
    (first : Step profile ready dispatch before label left) (second : Step profile ready dispatch before label right) :
    left = right := by
  cases first <;> cases second
  all_goals try (cases (show Fault before _ from by assumption))
  all_goals simp_all
  case coreInternal.coreInternal => grind only [Core3.core3_internal_iff]
  all_goals
    have heads := (show (_ ∧ Prog.op (S := Eff (core3 grow) (HostState sig)) (α := Ret (core3 grow)) _ _ = Prog.op _ _ ∧ _) ∧ _
      from by assumption)
    obtain ⟨⟨_, programs, _⟩, _⟩ := heads
    obtain ⟨operation, continuation⟩ := progOpEq programs
    simp_all
  all_goals (injection operation; subst_vars; simp_all)

private theorem stripExactPrefix {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {before middle after : Config (core3 grow) (HostState sig)} {leading trailing : Trace grow sig}
    (front : Steps profile ready dispatch before leading middle)
    (whole : Steps profile ready dispatch before (leading ++ trailing) after) :
    Steps profile ready dispatch middle trailing after := by
  induction front with
  | refl => exact whole
  | cons first _ ih =>
    cases whole with
    | cons actual rest =>
      cases labelledStepUnique first actual
      exact ih rest

private theorem classifyReachedGrowth {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (run : Steps profile ready dispatch start labels finish) :
    CoreGrowthSteps profile ready dispatch start labels finish ∨ ReachedNonGrowingUpdate profile ready dispatch start labels finish := by
  classical
  induction run with
  | refl => exact .inl (.refl _)
  | @cons before next after label trailing first rest ih =>
    by_cases grows : CoreUpdateGrows before
    · rcases ih with certified | ⟨leading, action, remaining, reached, next, split, certified, openUpdate, actual, tail⟩
      · exact .inl (.cons grows first certified)
      · exact .inr ⟨label :: leading, action, remaining, reached, next, congrArg (label :: ·) split,
          .cons grows first certified, openUpdate, actual, tail⟩
    · exact .inr ⟨[], label, trailing, before, next, rfl, .refl _, grows, first, rest⟩

theorem cutExecutedCallback
    (run : Steps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) (includeComponentCalls : Bool := false) (includePoll : Bool := false)
    (includeWait : Bool := false) (includeCancelResume : Bool := false) (includeCancel : Bool := false) :
    ExecutedCallbackCut profile ready base bindings older start incoming labels finish := by
  let protectedReturn := fun resume => ∃ rhs, older resume rhs
  have covers : ∀ lhs rhs, older lhs rhs → protectedReturn lhs := fun _ rhs edge => ⟨rhs, edge⟩
  cases CallbackPrefix.classifyActual (bindings := bindings) (protectedReturn := protectedReturn) run
      includeComponentCalls includePoll includeWait includeCancelResume includeCancel with
  | complete _ replay growing =>
    obtain ⟨_, prefixRun⟩ := CallbackPrefix.executeClassifiedPrefix growing replay covers paired
    exact .complete prefixRun
  | @boundary leading label trailing reached next split _ growing replay kind step tail =>
    obtain ⟨_, compared⟩ := CallbackPrefix.executeClassifiedPrefix growing replay covers paired
    have smaller : trailing.length < labels.length := by simp [split, List.length_append]; omega
    exact .boundary split compared kind step tail smaller

private def CallbackCrossingAt (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig)) (label : Label (core3 grow) (HostState sig))
    (trailing : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  (∃ consumed canonLabels residual replied peer,
    trailing = consumed ++ residual ∧
    ExecutedCallbackSegment profile ready base bindings changes checked canonical (label :: consumed) canonLabels replied peer ∧
    Steps profile ready (specDispatch ready base) replied residual finish) ∨
  CallbackSlice profile ready base bindings changes checked canonical (label :: trailing) finish

private def CallbackComponentCrossing (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) : Prop :=
  ∀ {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {checked canonical next finish label trailing}
    {active hostId caller resume frames rest},
    checked.ctl = ⟨some active, .prog (.op (.call (.hostFunc hostId caller)) resume), frames⟩ :: rest →
    Step profile ready (specDispatch ready base) checked label next →
    Steps profile ready (specDispatch ready base) next trailing finish →
    HostFrame.Related.Paired changes checked canonical →
    CallbackCrossingAt profile ready base bindings changes checked canonical label trailing finish

private def CallbackWaitableCrossing (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) (poll : Bool) : Prop :=
  ∀ {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {checked canonical next finish label trailing}
    {thread core resume frames rest mem inst args},
    checked.ctl = ⟨thread, .core core resume, frames⟩ :: rest →
    (core3 grow).status checked.store.core core = .callout (waitableCalloutHost poll mem inst) args →
    Step profile ready (specDispatch ready base) checked label next →
    Steps profile ready (specDispatch ready base) next trailing finish →
    HostFrame.Related.Paired changes checked canonical →
    CallbackCrossingAt profile ready base bindings changes checked canonical label trailing finish

private def CallbackWaitResumeCrossing (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) : Prop :=
  ∀ {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {checked canonical next finish label trailing}
    {waiter resumer afterResume frames rest core resume savedFrames mem entry},
    checked.ctl = ⟨resumer, .prog (.op (.resumeThread waiter) afterResume), frames⟩ :: rest →
    checked.cont? waiter = some ⟨some waiter, .prog (waitableWaitContinue mem entry), .core core resume :: savedFrames⟩ →
    Step profile ready (specDispatch ready base) checked label next →
    Steps profile ready (specDispatch ready base) next trailing finish →
    HostFrame.Related.Paired changes checked canonical →
    CallbackCrossingAt profile ready base bindings changes checked canonical label trailing finish

private def CallbackCancelResumeCrossing (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) : Prop :=
  ∀ {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {checked canonical next finish label trailing}
    {waiter resumer afterResume frames rest core resume savedFrames subtask},
    checked.ctl = ⟨resumer, .prog (.op (.resumeThread waiter) afterResume), frames⟩ :: rest →
    checked.cont? waiter = some ⟨some waiter, .prog (cancelFinish subtask), .core core resume :: savedFrames⟩ →
    Step profile ready (specDispatch ready base) checked label next →
    Steps profile ready (specDispatch ready base) next trailing finish →
    HostFrame.Related.Paired changes checked canonical →
    CallbackCrossingAt profile ready base bindings changes checked canonical label trailing finish

private def CallbackCancelCrossing (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) : Prop :=
  ∀ {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {checked canonical next finish label trailing}
    {thread core resume frames rest async inst args},
    checked.ctl = ⟨thread, .core core resume, frames⟩ :: rest →
    (core3 grow).status checked.store.core core = .callout (.builtin (.subtaskCancel async) inst) args →
    Step profile ready (specDispatch ready base) checked label next →
    Steps profile ready (specDispatch ready base) next trailing finish →
    HostFrame.Related.Paired changes checked canonical →
    ShorterCallbackSlices profile ready base bindings (label :: trailing).length →
    CallbackCrossingAt profile ready base bindings changes checked canonical label trailing finish

private theorem foldCallbackSlicesWith (cross : CallbackGiveCrossing profile ready base bindings)
    (component : Option (PLift (CallbackComponentCrossing profile ready base bindings)))
    (poll : Option (PLift (CallbackWaitableCrossing profile ready base bindings true)))
    (wait : Option (PLift (CallbackWaitableCrossing profile ready base bindings false)))
    (waitResume : Option (PLift (CallbackWaitResumeCrossing profile ready base bindings)))
    (cancelResume : Option (PLift (CallbackCancelResumeCrossing profile ready base bindings)))
    (cancel : Option (PLift (CallbackCancelCrossing profile ready base bindings)))
    (run : Steps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    CallbackSlice profile ready base bindings older start incoming labels finish := by
  induction size : labels.length using Nat.strong_induction_on generalizing start incoming labels finish older with
  | ind budget ih =>
    cases cutExecutedCallback run paired component.isSome poll.isSome (wait.isSome || waitResume.isSome) cancelResume.isSome
        cancel.isSome with
    | complete segment => exact ⟨labels, labels, [], finish, _, (List.append_nil _).symm, segment, .exhausted⟩
    | @boundary leading label trailing reached peer next split front kind step tail smaller =>
      have stop (ending : CallbackSliceEnd profile ready base bindings older reached peer (label :: trailing) finish) :
          CallbackSlice profile ready base bindings older start incoming labels finish :=
        ⟨leading, leading, label :: trailing, reached, peer, split, front, ending⟩
      have advance (crossed : CallbackCrossingAt profile ready base bindings older reached peer label trailing finish) :
          CallbackSlice profile ready base bindings older start incoming labels finish := by
        rcases crossed with
          ⟨consumed, canonLabels, residual, replied, peerReply, used, reply, rest⟩ | ending
        · have remaining : residual.length < budget := by
            have lengths := congrArg List.length used
            simp only [List.length_append] at lengths
            omega
          obtain ⟨checked, canonical, trailing, reached, peer, suffix, continued, ending⟩ :=
            ih residual.length remaining rest reply.paired rfl
          exact ⟨leading ++ (label :: consumed) ++ checked, leading ++ canonLabels ++ canonical, trailing, reached, peer,
            by rw [split, used, suffix]; simp only [List.append_assoc, List.cons_append],
            CallbackPrefix.appendExecutedCallbacks (CallbackPrefix.appendExecutedCallbacks front reply) continued, ending⟩
        · obtain ⟨checked, canonical, trailing, reached, peer, tailSplit, nested, ending⟩ := ending
          exact ⟨leading ++ checked, leading ++ canonical, trailing, reached, peer,
            by rw [split, tailSplit, List.append_assoc], CallbackPrefix.appendExecutedCallbacks front nested, ending⟩
      have available : ShorterCallbackSlices profile ready base bindings (label :: trailing).length := by
        intro _ _ _ _ actual shorter actualRun actualPair
        have cutLength : (label :: trailing).length ≤ budget := by
          rw [← size, split, List.length_append]
          omega
        exact ih actual.length (Nat.lt_of_lt_of_le shorter cutLength) actualRun actualPair rfl
      cases kind with
      | give install => exact advance (cross install tail front.paired available)
      | @read thread resume frames rest focus _ =>
        by_cases agrees : resume reached.host = resume peer.host
        · obtain ⟨afterRead, read⟩ := CallbackPrefix.compareReachedHostRead focus step front.paired agrees
          obtain ⟨checked, canonical, trailing, lhs, rhs, used, continued, ending⟩ :=
            ih trailing.length (size ▸ smaller) tail read.paired rfl
          exact ⟨leading ++ [label] ++ checked, leading ++ [label] ++ canonical, trailing, lhs, rhs,
            by rw [split, used]; simp only [List.append_assoc, List.cons_append, List.nil_append],
            CallbackPrefix.appendExecutedCallbacks (CallbackPrefix.appendExecutedCallbacks front read) continued, ending⟩
        · by_cases journal : ∃ left right next,
              resume reached.host = .op (.hostSet left) (fun _ => next) ∧
                resume peer.host = .op (.hostSet right) (fun _ => next)
          · obtain ⟨left, right, nextProgram, checkedWrite, canonicalWrite⟩ := journal
            obtain ⟨afterWrite, compared⟩ := CallbackPrefix.compareReachedJournalUpdate focus front.paired checkedWrite canonicalWrite
            rcases splitSilent (count := 2) compared.checkedRun.steps (.cons step tail) with ⟨remaining, consumed, actual⟩ | _
            · have decreases : remaining.length < budget := by
                rw [← size, split, consumed, List.length_append, List.length_append, List.length_replicate]
                omega
              obtain ⟨checked, canonical, trailing, lhs, rhs, used, continued, ending⟩ :=
                ih remaining.length decreases actual compared.paired rfl
              exact ⟨leading ++ [.tau, .tau] ++ checked, leading ++ [.tau, .tau] ++ canonical, trailing, lhs, rhs,
                by rw [split, consumed, used]; simp only [List.replicate_succ, List.replicate_zero, List.append_assoc],
                CallbackPrefix.appendExecutedCallbacks (CallbackPrefix.appendExecutedCallbacks front compared) continued, ending⟩
            · exact stop (CallbackPrefix.compareDivergentHostRead focus step tail front.paired agrees)
          · exact stop (CallbackPrefix.compareDivergentHostRead focus step tail front.paired agrees)
      | protectedPop retained focus => exact stop (.boundary (.protectedPop retained focus) step tail)
      | componentInstall focus =>
        cases component with
        | none => exact stop (.boundary (.componentInstall focus) step tail)
        | some rule => exact advance (rule.down focus step tail front.paired)
      | pollInstall focus calling =>
        cases poll with
        | none => exact stop (.boundary (.pollInstall focus calling) step tail)
        | some rule => exact advance (rule.down focus calling step tail front.paired)
      | waitInstall focus calling =>
        cases wait with
        | none => exact stop (.boundary (.waitInstall focus calling) step tail)
        | some rule => exact advance (rule.down focus calling step tail front.paired)
      | waitResume focus found =>
        cases waitResume with
        | none => exact stop (.boundary (.waitResume focus found) step tail)
        | some rule => exact advance (rule.down focus found step tail front.paired)
      | cancelResume focus found =>
        cases cancelResume with
        | none => exact stop (.boundary (.cancelResume focus found) step tail)
        | some rule => exact advance (rule.down focus found step tail front.paired)
      | cancelInstall focus calling =>
        cases cancel with
        | none => exact stop (.boundary (.cancelInstall focus calling) step tail)
        | some rule => exact advance (rule.down focus calling step tail front.paired available)
      | write focus =>
        obtain ⟨rfl, rfl⟩ := silentStepUnique (.hostSet focus) step
        obtain ⟨afterWrite, compared⟩ := CallbackPrefix.compareReachedHostWrite focus front.paired
        obtain ⟨checked, canonical, trailing, lhs, rhs, used, continued, ending⟩ :=
          ih trailing.length (size ▸ smaller) tail compared.paired rfl
        exact ⟨leading ++ [.tau] ++ checked, leading ++ [.tau] ++ canonical, trailing, lhs, rhs,
          by rw [split, used]; simp only [List.append_assoc, List.cons_append, List.nil_append],
          CallbackPrefix.appendExecutedCallbacks (CallbackPrefix.appendExecutedCallbacks front compared) continued, ending⟩
      | nonGrowingUpdate failed => exact stop (.boundary (.nonGrowingUpdate failed) step tail)

theorem foldCallbackSlices (cross : CallbackGiveCrossing profile ready base bindings)
    (run : Steps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    CallbackSlice profile ready base bindings older start incoming labels finish :=
  foldCallbackSlicesWith cross none none none none none none run paired

private theorem callbackEndSteps {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (ending : CallbackSliceEnd profile ready base bindings changes start incoming labels finish) :
    Steps profile ready (specDispatch ready base) start labels finish := by
  induction ending with
  | exhausted => exact .refl _
  | boundary _ step tail => exact .cons step tail
  | observation _ _ paths tail => exact append (paths.choose_spec.1 none).1.steps tail
  | refused _ _ reply =>
    obtain ⟨_, _, rfl, front, completed, tail, _, _, _⟩ := reply
    exact append front (append completed tail)
  | entryPrefix _ run _ _ => exact run
  | directGiveEntry _ _ _ _ paths _ _ _ tail => exact append (paths.choose_spec.1 none).1.steps tail
  | lookup _ install _ _ tail => exact .cons install.step tail
  | admissionTrap _ _ _ checked _ tail => exact append checked tail
  | compilerRefused _ _ _ checked _ _ _ _ tail => exact append (checked (.active 0 0)).steps tail
  | placementTrap _ _ _ checked _ _ _ _ tail => exact append (checked (.active 0 0)).steps tail
  | body _ cut _ => exact append (cut.paths.choose_spec.1 none).1.steps cut.residual
  | allocator _ cut _ _ _ _ => exact append (cut.paths.choose_spec.1 none).1.steps cut.residual
  | uncertified _ _ _ paths residual => exact append (paths.choose_spec.1 none).1.steps residual
  | pollTerminal paths _ _ residual => exact append (paths.choose_spec.1 none).1.steps residual
  | waitTerminal paths _ _ residual => exact append (paths.choose_spec.1 none).1.steps residual
  | cancelTerminal paths _ _ _ residual => exact append (paths.choose_spec.1 none).1.steps residual
  | cancelHookBody paths _ _ _ ih => exact append (paths.choose_spec.1 none).1.steps ih
  | cancelDecisionTerminal paths _ _ _ residual => exact append (paths.choose_spec.1 none).1.steps residual
  | cancelParked paths _ _ ih => exact append (paths.choose_spec.1 none).1.steps ih

private theorem returningCallbackEndSteps {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {resume value}
    (ending : CallbackSliceEnd profile ready base bindings changes start incoming labels finish)
    (focus : start.ctl = { cursor with frames := .prog resume :: cursor.frames }.control (.pure value)) :
    Steps profile ready (specDispatch ready base) start labels finish := by
  cases ending with
  | exhausted => exact .refl _
  | boundary _ step tail => exact .cons step tail
  | observation read _ _ _ => simp_all [PayloadPrefix.Cursor.control]
  | refused install _ _ => cases install <;> simp_all [PayloadPrefix.Cursor.control]
  | entryPrefix install _ _ _ => cases install <;> simp_all [PayloadPrefix.Cursor.control]
  | directGiveEntry _ _ _ _ paths _ _ _ tail => exact append (paths.choose_spec.1 none).1.steps tail
  | lookup _ install _ _ _ => cases install <;> simp_all [PayloadPrefix.Cursor.control]
  | admissionTrap _ install _ _ _ _ => cases install <;> simp_all [PayloadPrefix.Cursor.control]
  | compilerRefused _ install _ _ _ _ _ _ _ => cases install <;> simp_all [PayloadPrefix.Cursor.control]
  | placementTrap _ install _ _ _ _ _ _ _ => cases install <;> simp_all [PayloadPrefix.Cursor.control]
  | body install _ _ => cases install <;> simp_all [PayloadPrefix.Cursor.control]
  | allocator install _ _ _ _ _ => cases install <;> simp_all [PayloadPrefix.Cursor.control]
  | uncertified install _ _ _ _ => cases install <;> simp_all [PayloadPrefix.Cursor.control]
  | pollTerminal paths _ _ residual => exact append (paths.choose_spec.1 none).1.steps residual
  | waitTerminal paths _ _ residual => exact append (paths.choose_spec.1 none).1.steps residual
  | cancelTerminal paths _ _ _ residual => exact append (paths.choose_spec.1 none).1.steps residual
  | cancelHookBody paths _ _ ending => exact append (paths.choose_spec.1 none).1.steps (callbackEndSteps ending)
  | cancelDecisionTerminal paths _ _ _ residual => exact append (paths.choose_spec.1 none).1.steps residual
  | cancelParked paths _ ending => exact append (paths.choose_spec.1 none).1.steps (callbackEndSteps ending)

private theorem callbackTerminalSlice {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired changes start incoming)
    (ending : CallbackSliceEnd profile ready base bindings changes start incoming labels finish) :
    CallbackSlice profile ready base bindings changes start incoming labels finish :=
  ⟨[], [], _, start, incoming, rfl,
    ⟨.refl _, rfl, paired, CallbackPrefix.stationaryTransport (fun place => .done _ place) (fun place => .done _ place)⟩,
    ending⟩

theorem prependCheckedOnlyReply {route : GiveEffectRoute} {destination ticket issue}
    {left right checkStop canonStop : Config (core3 grow) (HostState sig)}
    {checkPrefix canonPrefix checkBody canonBody trailing : Trace grow sig} {marks}
    (leading : OccurrenceTransport profile ready base bindings start incoming checkPrefix canonPrefix left right marks)
    (reply : CheckedOnlyGiveReply profile ready base bindings route destination ticket issue left right checkStop canonStop
      checkBody canonBody trailing finish) :
    CheckedOnlyGiveReply profile ready base bindings route destination ticket issue start incoming checkStop canonStop
      (checkPrefix ++ checkBody) (canonPrefix ++ canonBody) trailing finish := by
  obtain ⟨move, before, _⟩ := leading
  obtain ⟨suffix, checked, split, front, complete, tail, stored, recorded, paths⟩ := reply
  refine ⟨suffix, checked, split, append (before none).1.steps front, complete, tail, stored, recorded, fun place => ?_⟩
  obtain ⟨checkedMark, canonicalMark, checkPath, canonPath⟩ := paths (move place)
  exact ⟨checkedMark, canonicalMark,
    (List.append_assoc _ _ _).symm ▸ (before place).1.append checkPath, (before place).2.append canonPath⟩

theorem sliceInstalledCallback
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    {checkEntry canonEntry : Config (core3 grow) (HostState sig)} {checkCount canonCount : Nat}
    (installed : PairedAllocatorInstall profile ready base bindings older first second start incoming checkEntry canonEntry
      checkCount canonCount)
    (positive : 0 < checkCount) (run : Steps profile ready (specDispatch ready base) start labels finish)
    (compare : ShorterCallbackSlices profile ready base bindings labels.length) :
    InstalledCallbackSlice profile ready base bindings older first second checkEntry canonEntry checkCount labels finish := by
  rcases splitSilent installed.checkedRun run with ⟨residual, split, tail⟩ | inside
  · have smaller : residual.length < labels.length := by
      simp only [split, List.length_append, List.length_replicate]
      omega
    obtain ⟨checked, canonical, trailing, reached, peer, splitTail, segment, ending⟩ := compare smaller tail installed.paired
    exact .inr ⟨checked, canonical, trailing, reached, peer, by rw [split, splitTail, List.append_assoc], .executed segment, ending⟩
  · exact .inl inside

private theorem faultUnique {before : Config (core3 grow) (HostState sig)} {left right : String}
    (first : Fault before left) (second : Fault before right) : left = right := by
  cases first <;> cases second <;> simp_all
  all_goals
    have heads := (show (_ ∧ Prog.op (S := Eff (core3 grow) (HostState sig)) (α := Ret (core3 grow)) _ _ = Prog.op _ _ ∧ _) ∧ _
      from by assumption)
    obtain ⟨⟨_, programs, _⟩, _⟩ := heads
    exact (by cases (progOpEq programs).1 : False).elim

set_option maxHeartbeats 2000000 in
private theorem differentStepBranch {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {before left right : Config (core3 grow) (HostState sig)} {expected taken}
    (planned : Step profile ready dispatch before expected left) (actual : Step profile ready dispatch before taken right)
    (different : expected ≠ taken) : workerBranchLabel expected ∧ workerBranchLabel taken := by
  cases planned <;> cases actual
  case fault.fault =>
    rename_i first leftFault second rightFault
    have same := faultUnique leftFault rightFault
    subst second
    exact (different rfl).elim
  all_goals try (cases (show Fault before _ from by assumption))
  all_goals simp_all [workerBranchLabel, StepDefs.HostReadyCfg]
  all_goals
    have heads := (show (_ ∧ Prog.op (S := Eff (core3 grow) (HostState sig)) (α := Ret (core3 grow)) _ _ = Prog.op _ _ ∧ _) ∧ _
      from by assumption)
    obtain ⟨⟨_, programs, _⟩, _⟩ := heads
    obtain ⟨operation, continuation⟩ := progOpEq programs
    simp_all
  all_goals (injection operation; subst_vars; simp_all)

private theorem alignWorkerBody {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {before body finish : Config (core3 grow) (HostState sig)} {bodyLabels actual : Trace grow sig}
    (bodyRun : Steps profile ready dispatch before bodyLabels body)
    (checkedRun : Steps profile ready dispatch before actual finish) :
    WorkerBodyAlignment profile ready dispatch before body bodyLabels actual finish := by
  classical
  induction bodyRun generalizing actual with
  | refl => exact .reached rfl checkedRun
  | @cons before middle body expected rest planned bodyTail ih =>
    cases checkedRun with
    | refl => exact .inside rfl (List.cons_ne_nil _ _) (.cons planned bodyTail)
    | @cons _ actualNext _ taken suffix actualStep actualTail =>
      by_cases agree : expected = taken
      · subst taken
        cases labelledStepUnique planned actualStep
        cases ih actualTail with
        | reached split tail => exact .reached (congrArg (expected :: ·) split) tail
        | inside split nonempty remaining => exact .inside (congrArg (expected :: ·) split) nonempty remaining
        | departure bodySplit actualSplit shared different branch first afterFirst second afterSecond =>
          exact .departure (congrArg (expected :: ·) bodySplit) (congrArg (expected :: ·) actualSplit)
            (.cons planned shared) different branch first afterFirst second afterSecond
      · exact .departure (leading := []) rfl rfl (.refl _) agree (differentStepBranch planned actualStep agree)
          planned bodyTail actualStep actualTail

private theorem alignLocalBody {before target last : Config (core3 grow) (HostState sig)}
    {planned actual : Trace grow sig}
    (localRun : Steps profile ready (specDispatch ready base) before planned target)
    (actualRun : Steps profile ready (specDispatch ready base) before actual last)
    (notBranch : ∀ action ∈ planned, ¬ workerBranchLabel action) :
    LocalRunAlignment profile ready (specDispatch ready base) target planned actual last := by
  cases alignWorkerBody localRun actualRun with
  | reached split tail => exact .reached split tail
  | inside split nonempty tail => exact .inside split nonempty tail
  | departure split _ _ _ branch _ _ _ _ =>
    exact False.elim (notBranch _ (split ▸ List.mem_append_right _ (List.mem_cons_self ..)) branch.1)

private theorem noBranchOfVisible {raw observed : Trace grow sig} (seen : PayloadPrefix.visible raw = observed)
    (notBranch : ∀ action ∈ observed, ¬ workerBranchLabel action) :
    ∀ action ∈ raw, ¬ workerBranchLabel action := by
  intro action member branch
  apply notBranch action _ branch
  rw [← seen]
  apply List.mem_filter.mpr
  refine ⟨member, ?_⟩
  cases action <;> simp_all [workerBranchLabel]

theorem driveValueCommit {output : Stored.Lower.Output} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output}
    {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output}
    {published : LinkedCallback.MemorySequence.ValueFinish grow sig output}
    (commit : LiveValueCommit profile ready base bindings output checkNext canonNext published start incoming check canon)
    (actual : Steps profile ready (specDispatch ready base) start labels finish) :
    ValueCommitRun profile ready base bindings output checkNext canonNext published start incoming check canon labels finish := by
  obtain ⟨store, verdict, effects, shape, checked, _, movement, continues⟩ := commit
  refine ⟨store, verdict, effects, movement, alignLocalBody checked.steps actual (noBranchOfVisible (CallbackPrefix.visibleLeaf shape) ?_),
    fun value success => (continues value success).2.2⟩
  cases verdict <;> simp [workerBranchLabel]

private theorem silentVisible {trace : Trace grow sig} (silent : trace.all (· matches .tau) = true) :
    PayloadPrefix.visible trace = [] := by
  induction trace with
  | nil => rfl
  | cons label trace ih =>
    have main := List.all_eq_true.mp silent label List.mem_cons_self
    cases label <;> try contradiction
    apply ih
    exact List.all_eq_true.mpr fun next member => List.all_eq_true.mp silent next (List.mem_cons_of_mem _ member)

private theorem entryVisible {route : GiveEffectRoute}
    (entry : Transition profile ready base start (.give route .entered) labels finish) : PayloadPrefix.visible labels = [] := by
  cases entry with
  | giveEntry _ _ silent _ _ _ => exact silent
  | giveStopped _ _ _ _ _ _ stopped => cases stopped

private theorem visibleAppend (left right : Trace grow sig) :
    PayloadPrefix.visible (left ++ right) = PayloadPrefix.visible left ++ PayloadPrefix.visible right :=
  List.filter_append left right

private theorem visibleTauCons (labels : Trace grow sig) :
    PayloadPrefix.visible (.tau :: labels) = PayloadPrefix.visible labels := rfl

private theorem visibleTaus (count : Nat) :
    PayloadPrefix.visible (List.replicate count (.tau : Label (core3 grow) (HostState sig))) = [] := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [List.replicate_succ]
    exact (visibleAppend [_] _).trans ih

open PayloadPrefix ReturnFrame.Occurrence in
theorem driveStringSlice {cx : LiftLowerContext (core3 grow)}
    {checkNext canonNext : Nat → Session grow sig (Ret (core3 grow))}
    {check canon : Cursor (E := core3 grow) (HostState sig)} {length budget : Nat}
    {describe : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Cursor (E := core3 grow) (HostState sig) → Prop}
    (paths : LiveStringReplay profile ready base bindings older cx checkNext canonNext describe length start incoming check canon)
    (same : start.store = incoming.store)
    (actual : Steps profile ready (specDispatch ready base) start labels finish)
    (bounded : labels.length ≤ budget) (compare : ShorterCallbackSlices profile ready base bindings budget) :
    StringRunSlice profile ready base bindings older describe start incoming labels finish := by
  classical
  induction length using Nat.strong_induction_on generalizing start incoming check canon labels with
  | ind length ih =>
    rw [LiveStringReplay] at paths
    obtain ⟨store, result, localLabels, _observed, checked, _canonical, localTrail, visit⟩ := paths
    cases alignWorkerBody checked.steps actual with
    | inside _ nonempty localTail =>
      exact ⟨[], [], labels, start, incoming, [], rfl, rfl,
        CallbackPrefix.stationaryTransport (fun place => .done _ place) (fun place => .done _ place),
        same, actual, .localPrefix nonempty localTail⟩
    | departure _ split shared _ branch _ _ step tail =>
      exact ⟨[], [], labels, start, incoming, [], rfl, rfl,
        CallbackPrefix.stationaryTransport (fun place => .done _ place) (fun place => .done _ place),
        same, actual, .localChoice split branch.2 shared step tail⟩
    | @reached remaining split remainder =>
      cases result with
      | error reason => exact ⟨localLabels, localLabels, remaining, _, _, [], split, rfl, localTrail, rfl,
          remainder, .trap rfl rfl⟩
      | ok front =>
        obtain ⟨_, _, visit⟩ := visit front rfl
        cases front with
        | done pointer => exact ⟨localLabels, localLabels, remaining, _, _, [], split, rfl, localTrail, rfl,
            remainder, .descriptor visit⟩
        | call pointer oldSize alignment size rest smaller =>
          have boundedLocal : remaining.length ≤ budget := by
            rw [split, List.length_append] at bounded
            omega
          rcases sliceInstalledCallback visit.1 (by decide) remainder
            (fun smaller run pair => compare (Nat.lt_of_lt_of_le smaller boundedLocal) run pair) with
            beforeInstall | ⟨checkCall, canonCall, trailing, reached, reference, installSplit, input, boundary⟩
          · exact ⟨localLabels, localLabels, remaining, _, _, [], split, rfl, localTrail, rfl, remainder,
              .installPrefix beforeInstall⟩
          obtain ⟨checkProof, canonProof, referenceProof, mark, _, _, checkSeen, canonSeen, paired, _,
            tracked, movement, index, returns⟩ := visit.2 input
          change (checkCall, canonCall, reference) = (checkProof, canonProof, referenceProof) at index
          rcases Prod.mk.inj index with ⟨rfl, paths⟩
          rcases Prod.mk.inj paths with ⟨rfl, rfl⟩
          have reachedRun := callbackEndSteps boundary
          have ending (stopped : trailing = [] ∨ mark ≠ some (.active 0 0) ∨ ¬ ∃ (value : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)),
              reached.ctl = { cursor with frames := .prog (stringPlanResume cx rest checkNext) :: cursor.frames }.control (.pure (.nat value))) :
              StringRunSlice profile ready base bindings older describe start incoming labels finish := by
            exact ⟨localLabels ++ .tau :: checkCall, localLabels ++ .tau :: canonCall, trailing, reached, reference,
              [mark], by rw [split, installSplit]; simp [List.append_assoc],
              by rw [visibleAppend, visibleAppend]; exact congrArg (PayloadPrefix.visible localLabels ++ ·) (canonSeen.trans checkSeen.symm),
              (CallbackPrefix.transportAppend localTrail movement).choose_spec.1, paired.data.1,
              reachedRun, .callback tracked paired boundary stopped⟩
          by_cases atTop : mark = some (.active 0 0)
          · by_cases returning : ∃ (value : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)),
              reached.ctl = { cursor with frames := .prog (stringPlanResume cx rest checkNext) :: cursor.frames }.control (.pure (.nat value))
            · obtain ⟨value, cursor, focus⟩ := returning
              cases returningCallbackEndSteps boundary focus with
              | refl => exact ending (.inl rfl)
              | @cons _ next _ label residual first tail =>
                have pop : Step profile ready (specDispatch ready base) reached .tau
                    { reached with ctl := cursor.control (stringPlanResume cx rest checkNext (.nat value)) } := .popProg focus
                obtain ⟨rfl, rfl⟩ := silentStepUnique pop first
                obtain ⟨peer, _, _, transported, continued⟩ := returns value cursor atTop focus
                have smallerRun : residual.length < labels.length := by
                  rw [split, installSplit]
                  simp only [List.length_append, List.length_cons, List.length_replicate]
                  omega
                obtain ⟨checkLabels, canonLabels, trailing, reached, reference, marks, used, observed, travel, store, after, ending⟩ :=
                  ih rest.length smaller continued paired.data.1 tail (Nat.le_trans (Nat.le_of_lt smallerRun) bounded)
                have movement := (CallbackPrefix.transportAppend
                  (CallbackPrefix.transportAppend localTrail transported).choose_spec.1 travel).choose_spec.1
                refine ⟨localLabels ++ (.tau :: checkCall ++ [.tau]) ++ checkLabels,
                  localLabels ++ (.tau :: canonCall ++ [.tau]) ++ canonLabels, trailing, reached, reference, marks,
                  ?_, ?_, by simpa only [List.map_nil, List.append_nil] using movement, store, after, ending⟩
                · rw [split, installSplit, used]
                  simp only [List.replicate_succ, List.replicate_zero, List.append_assoc, List.cons_append, List.nil_append]
                · have quiet (trace : Trace grow sig) : PayloadPrefix.visible (.tau :: trace ++ [.tau]) = PayloadPrefix.visible trace := by
                    change PayloadPrefix.visible (trace ++ [.tau]) = PayloadPrefix.visible trace
                    rw [visibleAppend, show PayloadPrefix.visible ([.tau] : Trace grow sig) = [] from rfl, List.append_nil]
                  have view (middle next : Trace grow sig) :
                      PayloadPrefix.visible (localLabels ++ (.tau :: middle ++ [.tau]) ++ next) =
                        PayloadPrefix.visible localLabels ++ PayloadPrefix.visible middle ++ PayloadPrefix.visible next :=
                    (visibleAppend ..).trans (congrArg (· ++ PayloadPrefix.visible next)
                      ((visibleAppend ..).trans (congrArg (PayloadPrefix.visible localLabels ++ ·) (quiet middle))))
                  rw [view canonCall canonLabels, view checkCall checkLabels, canonSeen, checkSeen, observed]
            · exact ending (.inr (.inr returning))
          · exact ending (.inr (.inl atTop))

open PayloadPrefix ReturnFrame.Occurrence in
theorem driveStringValue {destination : RecordDestination} {inst : InstId} {key : LinkedCallback.StringField}
    {output : Stored.Lower.Output} {check canon : Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output}
    {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output} {budget : Nat}
    {describe : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Cursor (E := core3 grow) (HostState sig) → Prop}
    (field : StringValueThen profile ready base bindings older destination inst key output start incoming check canon checkNext canonNext describe)
    (actual : Steps profile ready (specDispatch ready base) start labels finish)
    (bounded : labels.length ≤ budget) (compare : ShorterCallbackSlices profile ready base bindings budget) :
    StringRunSlice profile ready base bindings older describe start incoming labels finish := by
  obtain ⟨checkEntry, canonEntry, checkQuiet, canonQuiet, entry, enterPeer, frame, body⟩ := field
  have same : start.store = incoming.store := frame.store
  cases alignWorkerBody (entry (.active 0 0)).toTrail.steps actual with
  | inside _ nonempty localTail =>
    exact ⟨[], [], labels, start, incoming, [], rfl, rfl,
      CallbackPrefix.stationaryTransport (fun place => .done _ place) (fun place => .done _ place),
      same, actual, .localPrefix nonempty localTail⟩
  | departure _ split shared _ branch _ _ step tail =>
    exact ⟨[], [], labels, start, incoming, [], rfl, rfl,
      CallbackPrefix.stationaryTransport (fun place => .done _ place) (fun place => .done _ place),
      same, actual, .localChoice split branch.2 shared step tail⟩
  | @reached remaining split remainder =>
    have shorter : remaining.length ≤ budget := by rw [split, List.length_append] at bounded; omega
    obtain ⟨checked, canonical, trailing, reached, peer, marks, used, observed, traces, same, tail, ending⟩ :=
      driveStringSlice body frame.store remainder shorter compare
    exact ⟨checkEntry ++ checked, canonEntry ++ canonical, trailing, reached, peer, marks,
      by rw [split, used, List.append_assoc],
      by rw [visibleAppend, visibleAppend, checkQuiet, canonQuiet, observed],
      by simpa only [List.map_nil, List.append_nil] using
        (CallbackPrefix.transportAppend (CallbackPrefix.stationaryTransport entry enterPeer) traces).choose_spec.1,
      same, tail, ending⟩

open PayloadPrefix ReturnFrame.Occurrence in
theorem driveStringCommit {destination : RecordDestination} {inst : InstId} {key : LinkedCallback.StringField}
    {output : Stored.Lower.Output} {check canon : Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output}
    {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output} {budget : Nat}
    {published : LinkedCallback.MemorySequence.ValueFinish grow sig output}
    (field : StringValueThen profile ready base bindings older destination inst key output start incoming check canon checkNext canonNext
      (fun _ => LiveValueCommit profile ready base bindings output checkNext canonNext published))
    (actual : Steps profile ready (specDispatch ready base) start labels finish)
    (bounded : labels.length ≤ budget) (compare : ShorterCallbackSlices profile ready base bindings budget) :
    StringRunSlice profile ready base bindings older
      (fun _ lhs rhs cursor peer => ∃ value, published value lhs rhs cursor peer) start incoming labels finish := by
  obtain ⟨checked, canonical, trailing, reached, reference, marks, split, observed, movement, same, remainder, ending⟩ :=
    driveStringValue field actual bounded compare
  have stop (stopped : StringSliceEnd profile ready base bindings older
      (fun _ lhs rhs cursor peer => ∃ value, published value lhs rhs cursor peer) reached reference trailing finish marks) :
      StringRunSlice profile ready base bindings older (fun _ lhs rhs cursor peer => ∃ value, published value lhs rhs cursor peer)
        start incoming labels finish :=
    ⟨checked, canonical, trailing, reached, reference, marks, split, observed, movement, same, remainder, stopped⟩
  cases ending with
  | localPrefix nonempty tail => exact stop (.localPrefix nonempty tail)
  | localChoice split choice shared step tail => exact stop (.localChoice split choice shared step tail)
  | installPrefix short => exact stop (.installPrefix short)
  | collectionInstall short => exact stop (.collectionInstall short)
  | collectionRange nonempty tail => exact stop (.collectionRange nonempty tail)
  | callback mark paired ending noPop => exact stop (.callback mark paired ending noPop)
  | trap checked canonical => exact stop (.trap checked canonical)
  | @descriptor pointer cursor peer commit =>
    obtain ⟨store, verdict, effects, writes, aligned, continues⟩ := driveValueCommit commit remainder
    cases aligned with
    | inside _ nonempty tail => exact stop (.localPrefix nonempty tail)
    | @reached suffix used tail =>
      have reachedWrites := (CallbackPrefix.transportAppend movement writes).choose_spec.1
      refine ⟨checked ++ effects, canonical ++ effects, suffix, _, _, [],
        by rw [split, used, List.append_assoc],
        by rw [visibleAppend, visibleAppend, observed],
        by simpa only [List.nil_append, List.map_nil] using reachedWrites, ?_, tail, ?_⟩
      · cases verdict <;> rfl
      · cases verdict with
        | error reason => exact .trap rfl rfl
        | ok value => exact .descriptor (pointer := pointer) ⟨value, continues value rfl⟩

private theorem mapStringEnd
    {first second : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop}
    {trailing : Trace grow sig} {marks}
    (map : ∀ pointer check canon, first pointer start incoming check canon → second pointer start incoming check canon)
    (ending : StringSliceEnd profile ready base bindings older first start incoming trailing finish marks) :
    StringSliceEnd profile ready base bindings older second start incoming trailing finish marks := by
  cases ending with
  | descriptor reached => exact .descriptor (map _ _ _ reached)
  | trap left right => exact .trap left right
  | localPrefix nonempty tail => exact .localPrefix nonempty tail
  | localChoice split choice shared step tail => exact .localChoice split choice shared step tail
  | installPrefix short => exact .installPrefix short
  | collectionInstall short => exact .collectionInstall short
  | collectionRange nonempty tail => exact .collectionRange nonempty tail
  | callback tracked paired terminal notPopped => exact .callback tracked paired terminal notPopped

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback in
private theorem consumeFlatLocal {origin : CStore (core3 grow)}
    {checkNext : FlatSequenceCheckNext grow sig} {canonNext : FlatSequenceCanonNext grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older start incoming check canon)
    (localCut : LocalCutKeepingBetween profile ready (specDispatch ready base) (specDispatch ready (LiveDispatch.host bindings base))
      (fun store => Core3.Grows origin.core store.core) start incoming check canon (fun words => checkNext (.ok words)) canonNext true)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    FlatVisitRun profile ready base bindings older origin checkNext canonNext start incoming labels finish := by
  obtain ⟨store, result, checked, canonical, lhs, _, observed, cut, trails⟩ := localCut
  have stop (ending : StringSliceEnd profile ready base bindings older
      (fun _ => FlatVisitFocus older origin checkNext canonNext) start incoming labels finish []) :
      FlatVisitRun profile ready base bindings older origin checkNext canonNext start incoming labels finish :=
    ⟨[], [], labels, start, incoming, [], rfl, rfl,
      CallbackPrefix.stationaryTransport (fun place => .done _ place) (fun place => .done _ place), frame.store, run, ending⟩
  cases alignWorkerBody lhs run with
  | inside _ nonempty tail => exact stop (.localPrefix nonempty tail)
  | departure _ split shared _ branch _ _ step tail => exact stop (.localChoice split branch.2 shared step tail)
  | reached split tail =>
    refine ⟨checked, canonical, _, _, _, [], split, observed.symm, CallbackPrefix.localLeafTransport trails, ?_, tail, ?_⟩
    · cases result <;> rfl
    · cases result with
      | error reason => exact .trap rfl rfl
      | ok words =>
        exact .descriptor (pointer := 0) (cursor := check) (peer := canon) (.returned words
          ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩ cut.1 rfl rfl)

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback in
private theorem driveFlatScalar {origin : CStore (core3 grow)} (destination : RecordDestination) (inst : InstId) (budget : Nat)
    (type : Stored.TypeOf) (localType : LocalDataType type) (payload : Stored.Payload type)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width) :
    FlatVisitField profile ready base bindings older origin destination inst budget (.data type payload) := by
  intro index checkNext canonNext left right check canon frame growth checkAt canonAt actual finish run bounded
  have widthAt : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width := growth.memAddrType width
  exact consumeFlatLocal frame
    (local_data_leaf_frame_between destination inst type localType payload index .flat origin left right (frame.store ▸ growth)
      (by simp [ptrTypeIn, CanonOpts.ptrType, RecordDestination.context, widthAt]) rfl
      (trackOccurrences := true) frame.store check canon frame.thread checkNext canonNext checkAt canonAt) run

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback ReturnFrame.Occurrence in
private theorem driveFlatHandle {origin : CStore (core3 grow)} (destination : RecordDestination) (inst : InstId) (budget : Nat)
    (item : Field) (nominal : CanonicalHandle item) :
    FlatVisitField profile ready base bindings older origin destination inst budget item := by
  intro index checkNext canonNext left right check canon frame growth checkAt canonAt actual finish run bounded
  have leaf := frame.handle_field_then_between
    (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst item nominal index .flat
    checkNext canonNext growth checkAt canonAt (next := fun value lhs rhs cursor peer =>
      FlatVisitFocus older origin checkNext canonNext lhs rhs cursor peer)
    (fun words _ _ _ _ related grown lhs rhs => .returned words related grown lhs rhs)
  have stop (ending : StringSliceEnd profile ready base bindings older
      (fun _ => FlatVisitFocus older origin checkNext canonNext) left right actual finish []) :
      FlatVisitRun profile ready base bindings older origin checkNext canonNext left right actual finish :=
    ⟨[], [], actual, left, right, [], rfl, rfl,
      CallbackPrefix.stationaryTransport (fun place => .done _ place) (fun place => .done _ place), frame.store, run, ending⟩
  unfold LinkedCallback.HandleFieldThenBetween at leaf
  cases decision : liveLeafPlan left.store left.host.writer index item with
  | error issue =>
    rw [decision] at leaf
    obtain ⟨guard, tau, tracks⟩ := leaf
    have quiet : visible guard = [] := silentVisible (List.all_eq_true.mpr (fun action member => by rw [tau action member]))
    cases alignLocalBody (prefix_survives (tracks (.active 0 0))).1 run (noBranchOfVisible quiet (by simp)) with
    | inside _ nonempty tail => exact stop (.localPrefix nonempty tail)
    | reached split tail =>
      exact ⟨guard, [], _, { left with ctl := check.control (checkNext (.error issue)) }, right, [], split, quiet.symm,
        CallbackPrefix.stationaryTransport tracks (fun place => .done right place), frame.store, tail,
        .descriptor (pointer := 0) (cursor := check) (peer := canon) (.refused issue rfl)⟩
  | ok plan =>
    rw [decision] at leaf
    obtain ⟨store, verdict, guard, checkLabels, canonLabels, tau, leftKind, rightKind, checkRun, _, tracks, continued⟩ := leaf
    have quiet : visible guard = [] := silentVisible (List.all_eq_true.mpr (fun action member => by rw [tau action member]))
    have observed : visible (guard ++ checkLabels) = visible canonLabels := by
      rw [visibleAppend, quiet, List.nil_append, CallbackPrefix.visibleLeaf leftKind, CallbackPrefix.visibleLeaf rightKind]
      cases verdict <;> rfl
    have localOnly : ∀ action ∈ visible canonLabels, ¬ workerBranchLabel action := by
      rw [CallbackPrefix.visibleLeaf rightKind]
      cases verdict <;> simp [workerBranchLabel]
    cases alignLocalBody checkRun run (noBranchOfVisible observed localOnly) with
    | inside _ nonempty tail => exact stop (.localPrefix nonempty tail)
    | reached split tail =>
      refine ⟨guard ++ checkLabels, canonLabels, _, _, _, [], split, observed.symm,
        CallbackPrefix.localLeafTransport tracks, ?_, tail, ?_⟩
      · cases verdict <;> rfl
      · cases verdict with
        | error reason => exact .trap rfl rfl
        | ok words => exact .descriptor (pointer := 0) (continued words rfl).2.2

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback in
private theorem driveFlatSequence {origin : CStore (core3 grow)} {budget : Nat}
    (destination : RecordDestination) (inst : InstId) (items : List Field) (index : Nat) (leading : List FlatValue)
    (rules : ∀ item ∈ items, FlatVisitField profile ready base bindings older origin destination inst budget item)
    (checkNext : FlatSequenceCheckNext grow sig) (canonNext : FlatSequenceCanonNext grow sig)
    {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older start incoming check canon) (growth : Core3.Grows origin.core start.store.core)
    (checkAt : start.ctl = check.control (flatSequenceChecked destination inst items index leading checkNext))
    (canonAt : incoming.ctl = canon.control (flatSequenceCanonical destination inst items leading canonNext))
    (actual : Steps profile ready (specDispatch ready base) start labels finish) (bounded : labels.length ≤ budget) :
    FlatVisitRun profile ready base bindings older origin checkNext canonNext start incoming labels finish := by
  induction items generalizing index leading start incoming check canon labels with
  | nil =>
    refine ⟨[], [], labels, start, incoming, [], rfl, rfl,
      CallbackPrefix.stationaryTransport (fun place => .done _ place) (fun place => .done _ place), frame.store, actual,
      .descriptor (pointer := 0) (cursor := check) (peer := canon) (.returned leading frame growth ?_ ?_)⟩
    · simpa [flatSequenceChecked, Record.Effects.flat, Prog.bind_eq, Prog.pure_eq, Except.map] using checkAt
    · simpa [flatSequenceCanonical, CanonicalTree.flat, Prog.bind_eq, Prog.pure_eq] using canonAt
  | cons item rest ih =>
    obtain ⟨checked, canonical, trailing, lhs, rhs, marks, split, seen, movement, same, tail, ending⟩ :=
      rules item (List.mem_cons_self ..) index _ _ _ _ check canon frame growth
        (checkAt.trans (congrArg check.control (flat_sequence_checked_cons destination inst item rest index leading checkNext)))
        (canonAt.trans (congrArg canon.control (flat_sequence_canonical_cons destination inst item rest leading canonNext)))
        _ finish actual bounded
    have stop (why : StringSliceEnd profile ready base bindings older (fun _ => FlatVisitFocus older origin checkNext canonNext)
        lhs rhs trailing finish marks) : FlatVisitRun profile ready base bindings older origin checkNext canonNext start incoming labels finish :=
      ⟨checked, canonical, trailing, lhs, rhs, marks, split, seen, movement, same, tail, why⟩
    cases ending with
    | trap left right => exact stop (.trap left right)
    | localPrefix nonempty rest => exact stop (.localPrefix nonempty rest)
    | localChoice divided choice shared step suffix => exact stop (.localChoice divided choice shared step suffix)
    | installPrefix short => exact stop (.installPrefix short)
    | collectionInstall short => exact stop (.collectionInstall short)
    | collectionRange nonempty tail => exact stop (.collectionRange nonempty tail)
    | callback tracked paired terminal notPopped => exact stop (.callback tracked paired terminal notPopped)
    | @descriptor pointer cursor peer reached =>
      cases reached with
      | refused issue checkAt => exact stop (.descriptor (pointer := pointer) (peer := peer) (.refused issue checkAt))
      | returned words related grew atCheck atCanon =>
        have remaining : trailing.length ≤ budget := by rw [split, List.length_append] at bounded; omega
        obtain ⟨left, right, residual, reached, peer, marks, divided, observed, trails, equal, actualTail, done⟩ :=
          ih (index + 1) (leading ++ words) (fun child member => rules child (List.mem_cons_of_mem _ member))
            related grew atCheck atCanon tail remaining
        exact ⟨checked ++ left, canonical ++ right, residual, reached, peer, marks,
          by rw [split, divided, List.append_assoc], by rw [visibleAppend canonical right, visibleAppend checked left, seen, observed],
          by simpa using (CallbackPrefix.transportAppend movement trails).choose_spec.1, equal, actualTail, done⟩

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback in
private theorem driveFlatSumTail {origin : CStore (core3 grow)} (width : AddrType) (type : Stored.TypeOf)
    (count tag : Nat) (haves : List CoreType) (words : List FlatValue)
    {checkNext : FlatSequenceCheckNext grow sig} {canonNext : FlatSequenceCanonNext grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older start incoming check canon) (growth : Core3.Grows origin.core start.store.core)
    (checkAt : start.ctl = check.control (flatSumTail width type count tag haves words >>= fun result => checkNext (.ok result)))
    (canonAt : incoming.ctl = canon.control (flatSumTail width type count tag haves words >>= canonNext))
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    FlatVisitRun profile ready base bindings older origin checkNext canonNext start incoming labels finish :=
  consumeFlatLocal frame
    (variant_tail_frame_between count ((flatten width type).drop 1) tag haves words
      (keep := fun store => Core3.Grows origin.core store.core) start incoming (frame.store ▸ growth)
      (trackOccurrences := true) frame.store check canon frame.thread checkNext canonNext
      (by simpa only [flatSumTail, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using! checkAt) canonAt) run

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback in
private theorem driveFlatSum {origin : CStore (core3 grow)} {budget : Nat}
    (destination : RecordDestination) (inst : InstId) {type : Stored.TypeOf} {arms : List (Option Stored.TypeOf)}
    {tag : Nat} {selected : Option Field} (matched : Field.LayoutMatches (.sum type arms tag selected) type)
    (child : ∀ field, selected = some field → FlatVisitField profile ready base bindings older origin destination inst budget field) :
    FlatVisitField profile ready base bindings older origin destination inst budget (.sum type arms tag selected) := by
  have valid : tag < arms.length := by
    cases matched with
    | variant found _ => exact (List.getElem?_eq_some_iff.mp found).1
    | optionNone | optionSome | resultOk | resultError => simp
  intro index checkNext canonNext left right check canon frame growth checkAt canonAt actual finish run bounded
  cases selected with
  | none =>
    apply driveFlatSumTail destination.width type arms.length tag [] [] frame growth _ _ run
    · rw [Record.Effects.field] at checkAt
      let body : Session grow sig (List FlatValue) := flatSumTail destination.width type arms.length tag [] []
      change left.ctl = check.control ((body.bind fun value => .pure (.ok value)).bind checkNext) at checkAt
      rw [Prog.bind_assoc] at checkAt
      exact checkAt
    · simpa only [CanonicalTree.field, flatSumTail] using! canonAt
  | some field =>
    let haves := flatten destination.width field.type
    let checkedNext := flatSumCheckNext destination.width type arms.length tag index haves checkNext
    let canonicalNext := fun words => flatSumTail destination.width type arms.length tag haves words >>= canonNext
    have checkChild : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
        (destination.context inst) destination.width field 0 .flat >>= checkedNext) := by
      rw [checkAt, Record.Effects.field]
      let body : Session grow sig (Except Stored.Endpoints.RecordLower.Issue (List FlatValue)) :=
        Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width field 0 .flat
      let tail := flatSumTail (grow := grow) (sig := sig) destination.width type arms.length tag haves
      change check.control ((body.bind fun verdict => match verdict with
        | .error issue => .pure (.error (.nested index issue))
        | .ok words => (tail words).bind fun value => .pure (.ok value)).bind checkNext) =
          check.control (body.bind checkedNext)
      rw [Prog.bind_assoc]
      apply congrArg (fun next => check.control (body.bind next))
      funext verdict
      cases verdict with
      | error issue => rfl
      | ok words => rw [Prog.bind_assoc]; rfl
    have canonChild : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
        (destination.context inst) destination.width field .flat >>= canonicalNext) := by
      rw [canonAt, CanonicalTree.field]
      congr 1
      let body : Session grow sig (List FlatValue) := CanonicalTree.field Limits.spec Quirks.none
        (destination.context inst) destination.width field .flat
      change (lowerFlatVariantWith arms.length ((flatten destination.width type).drop 1) tag haves body).bind canonNext =
        body.bind fun words => (flatSumTail destination.width type arms.length tag haves words).bind canonNext
      simp only [flatSumTail, lowerFlatVariantWith, valid, ↓reduceIte, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind']
      exact Prog.bind_assoc _ _ _
    obtain ⟨checked, canonical, trailing, lhs, rhs, marks, split, seen, movement, same, tail, ending⟩ :=
      child field rfl 0 checkedNext canonicalNext left right check canon frame growth checkChild canonChild actual finish run bounded
    have stop (why : StringSliceEnd profile ready base bindings older (fun _ => FlatVisitFocus older origin checkNext canonNext)
        lhs rhs trailing finish marks) : FlatVisitRun profile ready base bindings older origin checkNext canonNext left right actual finish :=
      ⟨checked, canonical, trailing, lhs, rhs, marks, split, seen, movement, same, tail, why⟩
    cases ending with
    | trap left right => exact stop (.trap left right)
    | localPrefix nonempty rest => exact stop (.localPrefix nonempty rest)
    | localChoice divided choice shared step suffix => exact stop (.localChoice divided choice shared step suffix)
    | installPrefix short => exact stop (.installPrefix short)
    | collectionInstall short => exact stop (.collectionInstall short)
    | collectionRange nonempty tail => exact stop (.collectionRange nonempty tail)
    | callback tracked paired terminal notPopped => exact stop (.callback tracked paired terminal notPopped)
    | @descriptor pointer cursor peer reached =>
      cases reached with
      | refused issue checkAt => exact stop (.descriptor (pointer := pointer) (peer := peer) (.refused (.nested index issue) checkAt))
      | returned words related grew atCheck atCanon =>
        obtain ⟨left, right, residual, reached, peer, marks, divided, observed, trails, equal, actualTail, done⟩ :=
          driveFlatSumTail destination.width type arms.length tag haves words related grew atCheck atCanon tail
        exact ⟨checked ++ left, canonical ++ right, residual, reached, peer, marks,
          by rw [split, divided, List.append_assoc], by rw [visibleAppend canonical right, visibleAppend checked left, seen, observed],
          by simpa using (CallbackPrefix.transportAppend movement trails).choose_spec.1, equal, actualTail, done⟩

private theorem visiblePrefix {left right : Trace grow sig} (initial : left <+: right) :
    PayloadPrefix.visible left <+: PayloadPrefix.visible right := by
  obtain ⟨tail, rfl⟩ := initial
  rw [visibleAppend]
  exact List.prefix_append _ _

private theorem prefixBefore {left right : Trace grow sig} (front : Trace grow sig) (initial : left <+: right) :
    front ++ left <+: front ++ right := by
  obtain ⟨tail, rfl⟩ := initial
  exact ⟨tail, List.append_assoc _ _ _⟩

theorem source (plan : NestedPlan bindings profile ready base start labels finish) :
    Steps profile ready (specDispatch ready base) start labels finish := by
  induction plan with
  | segment path => exact path
  | localSegment path => exact path.steps
  | closedGive _ path => exact path
  | syncReady focused _ => exact .cons (.hostGet focused) (.refl _)
  | commit resolve => exact (Transition.commit (impl := base) resolve).steps
  | poll poll pending branch => exact (Transition.poll (impl := base) poll pending branch).steps
  | waitBlock wait empty => exact (Transition.waitBlock (impl := base) wait empty).steps
  | waitReady wait available early allowed => exact (Transition.waitReady (impl := base) wait available early allowed).steps
  | waitResume resume saved => exact (Transition.waitResume (impl := base) resume saved).steps
  | waitTake delivery focused pending branch => exact (Transition.waitTake (impl := base) delivery focused pending branch).steps
  | cancelReturned cancel pending available => exact (Transition.cancelReturned (impl := base) cancel pending available).steps
  | cancelRequest cancel record live unresolved notDelivered notRequested notJoined =>
    exact (Transition.cancelRequest (impl := base) cancel record live unresolved notDelivered notRequested notJoined).steps
  | cancelReentry request mode saved => exact (Transition.cancelReentry (impl := base) request mode saved).steps
  | cancelCallbackDone request => exact (Transition.cancelCallbackDone (impl := base) request).steps
  | cancelPark wait => exact (Transition.cancelPark (impl := base) wait).steps
  | cancelResume resume saved => exact (Transition.cancelResume (impl := base) resume saved).steps
  | cancelFinish cancel record focused live resolved pending => exact cancel.finish_delivers record focused live resolved pending
  | sequence _ _ front back => exact append front back
  | rootStop _ _ stop => cases stop <;> rename_i edge <;> exact edge.steps
  | compilerStop _ _ checked => exact checked
  | give _ _ entry checkedBody _ _ replies _ _ => exact append (append entry.steps checkedBody) (replies.1 _)
  | stop _ _ entry checkedBody _ _ _ _ _ => exact append entry.steps checkedBody

private theorem localStepHost {before after : Config (core3 grow) (HostState sig)} {label}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (focus : PayloadPrefix.LocalFocus before) (step : Step profile ready dispatch before label after) :
    after.host = before.host := by
  cases step <;> try rfl
  all_goals first | (rename_i focused; simp [PayloadPrefix.LocalFocus, focused] at focus)

private theorem pairedLocalFocus {left right : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older left right) (localFocus : PayloadPrefix.LocalFocus left) :
    PayloadPrefix.LocalFocus right := by
  cases focused : left.ctl with
  | nil => simp [PayloadPrefix.LocalFocus, focused] at localFocus
  | cons activation rest =>
    rcases activation with ⟨thread, focus, frames⟩
    cases focus with
    | core => simp [PayloadPrefix.LocalFocus, focused] at localFocus
    | prog program =>
      cases program with
      | op operation next =>
        obtain ⟨_, _, other, _⟩ := paired.retarget focused (.prog (.op operation next)) left.host right.host
        simp only [PayloadPrefix.LocalFocus, focused] at localFocus
        simpa only [PayloadPrefix.LocalFocus, other] using localFocus
      | pure result =>
        cases frames with
        | nil => simp [PayloadPrefix.LocalFocus, focused] at localFocus
        | cons frame tail =>
          cases frame with
          | prog => simp [PayloadPrefix.LocalFocus, focused] at localFocus
          | core =>
            obtain ⟨_, _, other, _⟩ := paired.retarget_core_frame focused (.prog (.pure result)) left.host right.host
            simp [PayloadPrefix.LocalFocus, other]

theorem replayLocal (run : PayloadPrefix.LocalSteps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ reached, Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming labels reached ∧
      HostFrame.Related.Paired older finish reached ∧ finish.host = start.host ∧ reached.host = incoming.host := by
  induction run generalizing incoming with
  | refl => exact ⟨_, .refl _, paired, rfl, rfl⟩
  | @cons before next finish label labels localFocus step tail ih =>
    have unchanged : UnchangedAt bindings before := by
      constructor
      · intro thread call cont frames rest focused
        simp [PayloadPrefix.LocalFocus, focused] at localFocus
      · intro thread core cont frames rest callee args focused calling
        simp [PayloadPrefix.LocalFocus, focused] at localFocus
    rcases LiveDispatch.classify_step (bindings := bindings) step with canonical | install
    · obtain ⟨_, reached, aligned | boundary⟩ := HostFrame.Related.paired_step paired canonical
      · obtain ⟨_, replay, last⟩ := ih aligned
        exact ⟨_, .cons reached replay, last.1, last.2.1.trans (localStepHost localFocus step),
          last.2.2.trans (localStepHost (pairedLocalFocus paired localFocus) reached)⟩
      · cases boundary with
        | read cut _ =>
          cases cut with
          | mk focused _ => simp [PayloadPrefix.LocalFocus, focused] at localFocus
        | returned cut =>
          obtain ⟨_, _, _, _, _, _, _, focused⟩ := cut.left_input
          simp only [HostFrame.replace] at focused
          simp [PayloadPrefix.LocalFocus, focused] at localFocus
    · cases install with
      | direct focused give => exact (give (unchanged.direct focused)).elim
      | core focused calling give => exact (give (unchanged.core focused calling)).elim

theorem planOfSteps (run : Steps profile ready (specDispatch ready base) start labels finish) :
    NestedPlan bindings profile ready base start labels finish := by
  classical
  induction run with
  | refl _ => exact .localSegment (.refl _)
  | @cons before next finish label labels step _ tail =>
    have front : NestedPlan bindings profile ready base before [label] next := by
      by_cases localFocus : PayloadPrefix.LocalFocus before
      · exact .localSegment (.cons localFocus step (.refl _))
      · exact .segment (.cons step (.refl _))
    exact .sequence front tail

theorem closedGivePlan (callout : LinkedCallback.ClosedGive bindings start)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    ∃ count, NestedPlan bindings profile ready base start (List.replicate count .tau) callout.resume := by
  obtain ⟨count, run, _, _⟩ := Plain.parked_closed_give_steps bindings callout.name callout.type callout.args
    callout.inst callout.destination callout.schema start callout.thread profile ready callout.parked callout.calling
    callout.linked callout.caller callout.live callout.closed base embedder
  exact ⟨count, .closedGive callout run.steps⟩

theorem callbackPlan {protectedReturn}
    (path : LinkedCallback.PrefixFor profile ready bindings protectedReturn start labels finish) :
    ∃ trace, NestedPlan bindings profile ready (Scheduled.host bindings) start trace finish ∧
      PayloadPrefix.visible trace = labels := by
  induction path with
  | done state => exact ⟨[], .localSegment (.refl state), rfl⟩
  | step _ _ run _ ih =>
    obtain ⟨trace, tail, seen⟩ := ih
    exact ⟨_ ++ trace, .sequence (planOfSteps (.cons run (.refl _))) tail, by rw [visibleAppend, seen]⟩
  | closedGive callout _ ih =>
    obtain ⟨trace, tail, seen⟩ := ih
    obtain ⟨count, head⟩ := closedGivePlan (profile := profile) (ready := ready) callout rfl
    exact ⟨_, .sequence head tail, by rw [visibleAppend, visibleTaus, List.nil_append, seen]⟩
  | syncReady focused readyAgreement _ ih =>
    obtain ⟨trace, tail, seen⟩ := ih
    exact ⟨_, .sequence (.syncReady focused readyAgreement) tail, (visibleAppend _ _).trans seen⟩

theorem callbackPlanExact {right reference : Config (core3 grow) (HostState sig)} {referenceLabels}
    (trace : LinkedCallback.ReplayTrace profile ready bindings start labels finish right referenceLabels reference) :
    NestedPlan bindings profile ready (Scheduled.host bindings) start labels finish := by
  induction trace with
  | done left _ => exact .localSegment (.refl left)
  | segments lhs _ => exact planOfSteps lhs
  | append _ _ head tail => exact .sequence head tail
  | step lhs _ _ ih => exact .sequence (planOfSteps (.cons lhs (.refl _))) ih
  | closedGive callout _ lhs _ _ _ _ ih => exact .sequence (.closedGive callout lhs) ih
  | syncReady focused agrees _ _ _ ih => exact .sequence (.syncReady focused agrees) ih

theorem callbackPeerPlanExact {right reference : Config (core3 grow) (HostState sig)} {referenceLabels}
    (trace : LinkedCallback.ReplayTrace profile ready bindings start labels finish right referenceLabels reference) :
    NestedPlan bindings profile ready (Scheduled.host bindings) right referenceLabels reference := by
  induction trace with
  | done _ right => exact .localSegment (.refl right)
  | segments _ rhs => exact planOfSteps rhs
  | append _ _ head tail => exact .sequence head tail
  | step _ rhs _ ih => exact .sequence (planOfSteps (.cons rhs (.refl _))) ih
  | closedGive _ peer _ rhs _ _ _ ih => exact .sequence (.closedGive peer rhs) ih
  | syncReady _ _ focused agrees _ ih => exact .sequence (.syncReady focused agrees) ih

private theorem noDirectCompatible {callees : List (ComponentCall.Callee sig)}
    (run : Plain.NoDirectCalls profile ready (Dispatch.coreOnly ready bindings) start labels finish) :
    Dispatch.Compatible profile ready bindings callees start labels finish := by
  induction run with
  | done => exact .done _
  | next closed step _ ih => exact .next (Dispatch.ClosedAt.agrees fun focused => (closed focused).elim) step ih

private theorem rawOverlay {callees : List (ComponentCall.Callee sig)}
    (run : Steps profile ready (Dispatch.coreOnly ready bindings) start labels finish) :
    CallbackOverlayPlan bindings profile ready callees start labels finish ∨
      CallbackOverlayCut bindings profile ready callees start labels finish := by
  rcases Dispatch.compatible_or_lookup (callees := callees) run with result | cut
  · exact .inl ⟨result, planOfSteps result.steps⟩
  · exact .inr ⟨start, finish, [], labels, [], by simp, .localSegment (.refl _), cut, .refl _⟩

private theorem spliceOverlay {callees : List (ComponentCall.Callee sig)}
    {middle : Config (core3 grow) (HostState sig)} {front back}
    (head : CallbackOverlayPlan bindings profile ready callees start front middle ∨
      CallbackOverlayCut bindings profile ready callees start front middle)
    (tail : CallbackOverlayPlan bindings profile ready callees middle back finish ∨
      CallbackOverlayCut bindings profile ready callees middle back finish)
    (sourceTail : Steps profile ready (Dispatch.coreOnly ready bindings) middle back finish) :
    CallbackOverlayPlan bindings profile ready callees start (front ++ back) finish ∨
      CallbackOverlayCut bindings profile ready callees start (front ++ back) finish := by
  rcases head with head | ⟨cut, after, leading, window, suffix, rfl, head, lookup, rest⟩
  · rcases tail with tail | ⟨cut, after, leading, window, suffix, rfl, tail, lookup, rest⟩
    · exact .inl ⟨head.1.append tail.1, .sequence head.2 tail.2⟩
    · exact .inr ⟨cut, after, front ++ leading, window, suffix, by simp only [List.append_assoc],
        .sequence head.2 tail, lookup, rest⟩
  · exact .inr ⟨cut, after, leading, window, suffix ++ back, by simp only [List.append_assoc], head, lookup,
      append rest sourceTail⟩

theorem linkedCallbackPeer {right reference : Config (core3 grow) (HostState sig)} {referenceLabels}
    {callees : List (ComponentCall.Callee sig)}
    (trace : LinkedCallback.ReplayTrace profile ready bindings start labels finish right referenceLabels reference) :
    CallbackOverlayPlan bindings profile ready callees right referenceLabels reference ∨
      CallbackOverlayCut bindings profile ready callees right referenceLabels reference := by
  induction trace with
  | done _ right => exact .inl ⟨.done right, .localSegment (.refl right)⟩
  | segments _ rhs => exact rawOverlay rhs
  | append _ tail headPlan tailPlan => exact spliceOverlay headPlan tailPlan (source (callbackPeerPlanExact tail))
  | step _ rhs tail ih => exact spliceOverlay (rawOverlay (.cons rhs (.refl _))) ih (source (callbackPeerPlanExact tail))
  | closedGive _ peer _ _ _ closed tail ih =>
    have compatible := noDirectCompatible (callees := callees) closed
    exact spliceOverlay (.inl ⟨compatible, .closedGive peer compatible.steps⟩) ih (source (callbackPeerPlanExact tail))
  | @syncReady _ right _ _ _ _ _ _ _ _ _ _ _ _ _ focused agrees tail ih =>
    have closed : Dispatch.ClosedAt right := by
      intro _ _ _ _ _ atCall
      rw [focused] at atCall
      cases atCall
    have compatible := Dispatch.Compatible.next (profile := profile) (ready := ready) (bindings := bindings)
      (callees := callees) (Dispatch.ClosedAt.agrees closed)
      (Step.hostGet focused) (.done _)
    exact spliceOverlay (.inl ⟨compatible, .syncReady focused agrees⟩) ih (source (callbackPeerPlanExact tail))

private theorem swapTrace {right reference : Config (core3 grow) (HostState sig)} {referenceLabels}
    (trace : LinkedCallback.ReplayTrace profile ready bindings start labels finish right referenceLabels reference) :
    LinkedCallback.ReplayTrace profile ready bindings right referenceLabels reference start labels finish := by
  induction trace with
  | done left right => exact .done right left
  | segments lhs rhs => exact .segments rhs lhs
  | append _ _ head tail => exact .append head tail
  | step lhs rhs _ ih => exact .step rhs lhs ih
  | closedGive callout peer lhs rhs leftClosed rightClosed _ ih =>
    exact .closedGive peer callout rhs lhs rightClosed leftClosed ih
  | syncReady focused agrees rightFocused rightAgrees _ ih => exact .syncReady rightFocused rightAgrees focused agrees ih

theorem rejoinedBodyPlan {route : GiveEffectRoute} {site : PayloadRoot.Site grow sig route}
    {value : route.output.Result} {checked reference : Config (core3 grow) (HostState sig)}
    (comparison : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings checked reference) :
    ∃ checkLabels referenceLabels,
      Steps profile ready (specDispatch ready (Scheduled.host bindings)) site.checked checkLabels checked ∧
      NestedPlan bindings profile ready (Scheduled.host bindings) (site.reference site.referenceReply) referenceLabels reference ∧
      PayloadPrefix.visible checkLabels = PayloadPrefix.visible referenceLabels := by
  obtain ⟨checkLabels, referenceLabels, seen, retained, _, classified⟩ := comparison.1
  exact ⟨checkLabels, referenceLabels, (ReturnFrame.Occurrence.prefix_survives (retained 0)).1,
    callbackPeerPlanExact classified, seen⟩

theorem rootAdmission {route} {site : PayloadRoot.Site grow sig route} {body : Prop} (linked : site.Linked bindings)
    (cut : PayloadRoot.Cut site profile ready bindings body base) : RootAdmission bindings profile ready base site body := by
  cases cut with
  | @refused issue labels silent run =>
    have seen : PayloadPrefix.visible (labels ++ [.tau, .tau, .tau]) = [] := by rw [visibleAppend, silent]; rfl
    let stop := RootStop.refused issue seen (.giveRefused site linked issue silent run.steps)
    exact .stopped stop (.rootStop site linked stop)
  | placementTrap reason count verdict run =>
    let stop := RootStop.placementTrap reason count (.givePlacementTrap site linked reason count verdict run.steps)
    exact .stopped stop (.rootStop site linked stop)
  | placed silent verdict prepared run compared =>
    exact .entered (.giveEntry site linked silent verdict prepared run.steps) compared

theorem memoryAdmission {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} :
    ∃ depth, RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedRejoinedMemory site depth profile ready bindings) := by
  obtain ⟨depth, cut⟩ := LinkedCallback.MemorySequence.parked_memory_rejoined site linked
    (ComponentCall.hostWithComponent bindings callees) rfl
  exact ⟨depth, rootAdmission linked cut⟩

theorem flatAdmission {schema : Stored.TypeOf} (site : PayloadRoot.Site grow sig (.flat schema))
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} :
    ∃ flatDepth entryDepth, RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedRejoinedFlat site flatDepth entryDepth profile ready bindings) := by
  obtain ⟨flatDepth, entryDepth, cut⟩ := LinkedCallback.MemorySequence.parked_flat_rejoined site linked
    (ComponentCall.hostWithComponent bindings callees) rfl
  exact ⟨flatDepth, entryDepth, rootAdmission linked cut⟩

theorem comparedGive {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {entryLabels checkLabels canonLabels reached reference checked baseline} (value : route.output.Result)
    (entry : Transition profile ready base site.start (.give route .entered) entryLabels site.checked)
    (left : Steps profile ready (specDispatch ready base) site.checked checkLabels reached)
    (right : Steps profile ready (specDispatch ready base) (site.reference site.referenceReply) canonLabels reference)
    (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels)
    (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline) :
    NestedPlan bindings profile ready base site.start (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked :=
  .give site linked entry left (planOfSteps (append right (replies.2.1 _))) value replies seen

theorem rejoinedGive {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {entryLabels reached reference} (value : route.output.Result)
    (entry : Transition profile ready (Scheduled.host bindings) site.start (.give route .entered) entryLabels site.checked)
    (compared : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference) :
    ∃ checkLabels checked baseline,
      NestedPlan bindings profile ready (Scheduled.host bindings) site.start (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked ∧
      LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline := by
  obtain ⟨⟨checkLabels, _, seen, left, _, classified⟩, checked, baseline, replies⟩ := compared
  exact ⟨checkLabels, checked, baseline, .give site linked entry (ReturnFrame.Occurrence.prefix_survives (left 0)).1
    (.sequence (callbackPeerPlanExact classified) (planOfSteps (replies.2.1 _))) value replies seen, replies⟩

theorem linkedRejoinedGive {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {callees : List (ComponentCall.Callee sig)} {entryLabels reached reference} (value : route.output.Result)
    (entry : Transition profile ready (ComponentCall.hostWithComponent bindings callees)
      site.start (.give route .entered) entryLabels site.checked)
    (compared : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference) :
    LinkedGiveExit bindings profile ready callees site entryLabels value reached reference := by
  obtain ⟨⟨checkLabels, canonLabels, seen, _, _, classified⟩, checked, baseline, replies⟩ := compared
  refine ⟨checkLabels, canonLabels, checked, baseline, replies, ?_⟩
  rcases linkedCallbackPeer (callees := callees) (swapTrace classified) with accepted | lookup
  · rcases linkedCallbackPeer (callees := callees) classified with canonical | lookup
    · exact .inl (.give site linked entry accepted.1.steps
        (.sequence canonical.2 (planOfSteps (replies.2.1 _))) value replies seen)
    · exact .inr (.inr lookup)
  · exact .inr (.inl lookup)

private theorem composeLinkedReturn {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} :
    LinkedCallback.MemorySequence.OnGiveReturn site profile ready bindings (ComponentCall.hostWithComponent bindings callees)
      (fun value reached reference => ∃ entryLabels, LinkedGiveExit bindings profile ready callees site entryLabels value reached reference) := by
  intro labels silent verdict prepared run value reached reference comparison
  exact ⟨labels, linkedRejoinedGive site linked value (.giveEntry site linked silent verdict prepared run) comparison⟩

theorem linkedMemoryExit {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} :
    ∃ depth, RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedMemoryBody site depth profile ready bindings (fun reached reference =>
        ∃ entryLabels, LinkedGiveExit bindings profile ready callees site entryLabels () reached reference)) := by
  obtain ⟨depth, cut⟩ := LinkedCallback.MemorySequence.parked_memory_then (profile := profile) (ready := ready) site linked
    (ComponentCall.hostWithComponent bindings callees) rfl
    (finish := fun reached reference => ∃ entryLabels, LinkedGiveExit bindings profile ready callees site entryLabels () reached reference)
    (by
      intro labels silent verdict prepared run value reached reference compared
      cases value
      exact composeLinkedReturn site linked (callees := callees) (labels := labels) silent verdict prepared run () reached reference compared)
  exact ⟨depth, rootAdmission linked cut⟩

theorem linkedFlatExit {schema : Stored.TypeOf} (site : PayloadRoot.Site grow sig (.flat schema))
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} :
    ∃ flatDepth entryDepth, RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedFlatResult site flatDepth entryDepth profile ready bindings (fun value reached reference =>
        ∃ entryLabels, LinkedGiveExit bindings profile ready callees site entryLabels value reached reference)) := by
  obtain ⟨flatDepth, entryDepth, cut⟩ := LinkedCallback.MemorySequence.parked_flat_then (profile := profile) (ready := ready) site linked
    (ComponentCall.hostWithComponent bindings callees) rfl
    (composeLinkedReturn (profile := profile) (ready := ready) site linked (callees := callees))
  exact ⟨flatDepth, entryDepth, rootAdmission linked cut⟩

theorem reachedGiveAdmission {route : GiveEffectRoute} {request : CoreGiveRequest bindings start}
    (selection : request.Selected route) {callees : List (ComponentCall.Callee sig)} :
    ReachedGiveAdmission profile ready callees selection := by
  cases preflight : selection.preflight with
  | error issue =>
    obtain ⟨count, checked⟩ := selection.compiler_refusal (profile := profile) (ready := ready) preflight
      (ComponentCall.hostWithComponent bindings callees) rfl
    exact .refused preflight checked
  | ok result =>
    obtain ⟨field, plan⟩ := result
    obtain ⟨tag, payload, arity, children, root, linked⟩ := selection.compiler_success preflight
    refine .compiled preflight root linked ?_
    cases route with
    | memory pointer => exact linkedMemoryExit _ linked
    | flat schema => exact linkedFlatExit _ linked

theorem pairedLinkedAdmission {route : GiveEffectRoute} {request : CoreGiveRequest bindings start}
    (selection : request.Selected route) {callees : List (ComponentCall.Callee sig)}
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {incoming : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start incoming)
    (reads : ∀ handle, request.lookupDemand = some handle →
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted handle) :
    ∃ entryLabels entered, entryLabels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming entryLabels entered ∧
      HostFrame.Related.Paired older selection.canonicalPending entered ∧
      ReachedGiveAdmission profile ready callees selection := by
  obtain ⟨labels, entered, silent, path, aligned⟩ := selection.paired_canonical_pending paired reads
  exact ⟨labels, entered, silent, path, aligned, reachedGiveAdmission selection⟩

theorem linkedAdmissionAfterInterleaving {route : GiveEffectRoute} {request : CoreGiveRequest bindings finish}
    (selection : request.Selected route) {callees : List (ComponentCall.Callee sig)} {actions incoming outgoing}
    (between : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      start incoming actions labels finish outgoing)
    (roots : incoming.writer.accepted = start.host.writer.accepted) :
    ∃ entryLabels canonical, entryLabels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
        (HostFrame.replace start incoming) (labels ++ entryLabels) canonical ∧
      HostFrame.Related.Paired (fun _ _ => False) selection.canonicalPending canonical ∧
      canonical.host.writer.accepted = finish.host.writer.accepted ∧
      ReachedGiveAdmission profile ready callees selection := by
  obtain ⟨entryLabels, canonical, silent, path, aligned, accepted⟩ := selection.pending_after_interleaving between roots
  exact ⟨entryLabels, canonical, silent, path, aligned, accepted, reachedGiveAdmission selection⟩

theorem linkedAdmissionAfterCallback {route : GiveEffectRoute} {request : CoreGiveRequest bindings finish}
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
      canonical.host.writer.accepted = finish.host.writer.accepted ∧ ReachedGiveAdmission profile ready callees selection := by
  obtain ⟨checkedLabels, canonLabels, reached, checked, prefixRun, aligned, checkSeen, canonSeen, _, checkRoots, canonRoots⟩ :=
    CallbackPrefix.replay path rfl covers paired
  have observed := checkRoots.trans (roots.trans canonRoots.symm)
  obtain ⟨entryLabels, canonical, silent, entry, entryHost, pending⟩ :=
    selection.paired_canonical_pending_host (profile := profile) (ready := ready)
      (base := ComponentCall.hostWithComponent bindings callees) aligned (fun _ _ => by rw [observed])
  exact ⟨checkedLabels, canonLabels, entryLabels, canonical, checked, append prefixRun entry, checkSeen,
    by rw [visibleAppend, silentVisible silent, List.append_nil, canonSeen], pending,
    (congrArg (·.writer.accepted) entryHost).trans observed.symm, reachedGiveAdmission selection⟩

theorem compilerRefusalAfterInterleaving {route : GiveEffectRoute} {request : CoreGiveRequest bindings finish}
    (selection : request.Selected route) {callees : List (ComponentCall.Callee sig)} {actions incoming outgoing}
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
      canonical.host.writer.accepted = (selection.compilerRefused issue).host.writer.accepted := by
  obtain ⟨entryLabels, canonical, silent, right, aligned, accepted⟩ := selection.pending_after_interleaving between roots
  obtain ⟨count, left⟩ := selection.compiler_refusal (profile := profile) (ready := ready) refused
    (ComponentCall.hostWithComponent bindings callees) rfl
  exact ⟨count, entryLabels, canonical, silent, append between.runs.1.steps left, right, aligned, accepted⟩

theorem compilerRefusalPlan {route : GiveEffectRoute} {request : CoreGiveRequest bindings start}
    (selection : request.Selected route) {issue : Stored.Endpoints.RecordLower.Issue}
    (refused : selection.preflight = .error issue)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    ∃ count, NestedPlan bindings profile ready base start (List.replicate count .tau) (selection.compilerRefused issue) := by
  obtain ⟨count, checked⟩ := selection.compiler_refusal (profile := profile) (ready := ready) refused base embedder
  exact ⟨count, .compilerStop selection refused checked⟩

theorem linkedGiveStop {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
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
      Dispatch.LookupCut profile ready bindings callees (site.reference site.referenceReply) canonLabels reference := by
  rcases Dispatch.compatible_or_lookup (callees := callees) left with accepted | lookup
  · rcases Dispatch.compatible_or_lookup (callees := callees) right with canonical | lookup
    · exact .inl (.stop site linked entry accepted.steps (planOfSteps canonical.steps) stop store seen)
    · exact .inr (.inr lookup)
  · exact .inr (.inl lookup)

theorem linkedAllocatorCut {route : GiveEffectRoute} {site : PayloadRoot.Site grow sig route}
    {callees : List (ComponentCall.Callee sig)} {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {beforeCheck beforeCanon left right reached reference : State grow sig}
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
      CallbackOverlayCut bindings profile ready callees right canonLabels reference := by
  rcases linkedCallbackPeer (callees := callees) (swapTrace cut.classified) with good | lookup
  · rcases linkedCallbackPeer (callees := callees) cut.classified with matched | lookup
    · obtain ⟨step, _, seen⟩ := cut.session checkEntry canonEntry seenEntry checkInstall canonInstall good.1 matched.1
      exact .inl ⟨step, .sequence (.sequence (planOfSteps canonEntry.steps) (planOfSteps canonInstall)) matched.2, seen⟩
    · exact .inr (.inr lookup)
  · exact .inr (.inl lookup)

theorem runs (plan : NestedPlan bindings profile ready base start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ trace reached, Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming trace reached ∧
      PayloadPrefix.visible trace <+: PayloadPrefix.visible labels ∧
      ((PayloadPrefix.visible labels = PayloadPrefix.visible trace ∧ HostFrame.Related.Paired older finish reached) ∨
        NestedCut bindings profile ready base older reached) := by
  classical
  induction plan generalizing incoming with
  | segment path =>
    cases LiveDispatch.paired_replay (bindings := bindings) paired path with
    | complete replay aligned => exact ⟨_, _, replay, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
    | request split _ replay aligned install _ =>
      exact ⟨_, _, replay, visiblePrefix ⟨_, split.symm⟩, .inr (.request aligned install)⟩
    | @boundary _ _ trailing _ _ _ _ split _ replay aligned cut lhs rhs _ =>
      refine ⟨_, _, append replay (.cons rhs (.refl _)), visiblePrefix ⟨trailing, ?_⟩, .inr (.boundary aligned cut lhs rhs)⟩
      simpa only [List.append_assoc, List.singleton_append] using split.symm
  | localSegment path =>
    obtain ⟨_, replay, aligned, _, _⟩ := replayLocal (bindings := bindings) path paired
    exact ⟨_, _, replay, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | @closedGive _ count callout _ =>
    obtain ⟨trace, _, silent, path, aligned, _, _⟩ := LiveDispatch.closed_give_paired (profile := profile)
      (ready := ready) (base := base) callout paired
    have seen := (visibleTaus (grow := grow) (sig := sig) count).trans (silentVisible silent).symm
    exact ⟨_, _, path, by rw [seen], .inl ⟨seen, aligned⟩⟩
  | @syncReady start task inst thread frames rest focused agrees =>
    let residual := syncLiftCandidates (E := core3 grow) (σ := HostState sig) task
      (start.store.instCandidates (ready start.host) inst)
    obtain ⟨otherFrames, otherRest, atOther, aligned⟩ := paired.retarget focused (.prog residual) start.host incoming.host
    have candidates := HostFrame.instCandidates_eq start.store inst (ready start.host) (ready incoming.host)
      (fun entry live thread member suspended found blocked query condition =>
        agrees entry live thread member suspended found blocked query condition incoming.host)
    have replay : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau
        { incoming with ctl := ⟨thread, .prog residual, otherFrames⟩ :: otherRest } := by
      unfold residual
      rw [candidates]
      exact .hostGet atOther
    exact ⟨_, _, .cons replay (.refl _), List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | commit resolve =>
    by_cases compatible : ∃ writer, incoming.host.writer.register resolve.tree = .ok writer ∧
        writer.accepted.length = resolve.writer.accepted.length
    · obtain ⟨_, registered, handle⟩ := compatible
      obtain ⟨_, replay, aligned, _, _⟩ :=
        Transition.commit_paired (profile := profile) (ready := ready) (impl := LiveDispatch.host bindings base)
          resolve paired registered handle
      exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
    · exact ⟨[], _, .refl _, ⟨_, rfl⟩, .inr (.publication resolve paired compatible)⟩
  | poll poll pending branch =>
    obtain ⟨_, replay, aligned, _⟩ :=
      Transition.poll_paired (ready := ready) (impl := LiveDispatch.host bindings base) poll pending branch paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | waitBlock wait empty =>
    obtain ⟨_, replay, aligned⟩ :=
      Transition.wait_block_paired (profile := profile) (ready := ready) (impl := LiveDispatch.host bindings base) wait empty paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | waitReady wait available early allowed =>
    obtain ⟨_, replay, aligned⟩ :=
      Transition.wait_ready_paired (ready := ready) (impl := LiveDispatch.host bindings base) wait available early allowed paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | waitResume resume saved =>
    obtain ⟨_, replay, aligned⟩ :=
      Transition.wait_resume_paired (profile := profile) (ready := ready) (impl := LiveDispatch.host bindings base) resume saved paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | waitTake delivery focused pending branch =>
    obtain ⟨_, replay, aligned, _⟩ :=
      Transition.wait_take_paired (ready := ready) (impl := LiveDispatch.host bindings base) delivery focused pending branch paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | cancelReturned cancel pending available =>
    obtain ⟨_, replay, aligned, _⟩ :=
      Transition.cancel_returned_paired (profile := profile) (ready := ready) (impl := LiveDispatch.host bindings base)
        cancel pending available paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | cancelRequest cancel record live unresolved notDelivered notRequested notJoined =>
    have installed := LiveDispatch.cancel_dispatch (bindings := bindings) (ready := ready) (base := base) record.onCancel
    obtain ⟨_, replay, aligned⟩ := Transition.cancel_request_paired (profile := profile) cancel record live unresolved
      notDelivered notRequested notJoined paired installed
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | cancelReentry request mode saved =>
    by_cases available : request.callee.state = .started →
        request.markedStore.threadReady (ready incoming.host) request.implicitThread = true
    · obtain ⟨_, replay, aligned⟩ := Transition.cancel_reentry_paired (profile := profile)
        (impl := LiveDispatch.host bindings base) request mode saved paired available
      exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
    · exact ⟨[], _, .refl _, ⟨_, rfl⟩, .inr (.cancelReadiness request mode paired available)⟩
  | cancelCallbackDone request =>
    obtain ⟨_, replay, aligned⟩ := Transition.cancel_callback_done_paired (profile := profile) (ready := ready)
      (impl := LiveDispatch.host bindings base) request paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | cancelPark wait =>
    obtain ⟨_, replay, aligned⟩ := Transition.cancel_park_paired (profile := profile) (ready := ready)
      (impl := LiveDispatch.host bindings base) wait paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | cancelResume resume saved =>
    obtain ⟨_, replay, aligned⟩ := Transition.cancel_resume_paired (profile := profile) (ready := ready)
      (impl := LiveDispatch.host bindings base) resume saved paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | cancelFinish cancel record focused live resolved pending =>
    obtain ⟨_, replay, aligned⟩ := cancel_finish_paired (profile := profile) (ready := ready)
      (impl := LiveDispatch.host bindings base) cancel record focused live resolved pending paired
    exact ⟨_, _, replay, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | sequence _ _ replayFront replayBack =>
    obtain ⟨_, _, front, frontPrefix, ⟨seenFront, aligned⟩ | cut⟩ := replayFront paired
    · obtain ⟨_, _, back, backPrefix, result⟩ := replayBack aligned
      refine ⟨_, _, append front back, ?_, ?_⟩
      · rw [visibleAppend, visibleAppend, seenFront]
        exact prefixBefore _ backPrefix
      · rcases result with ⟨seenBack, final⟩ | cut
        · exact .inl ⟨by rw [visibleAppend, visibleAppend, seenFront, seenBack], final⟩
        · exact .inr cut
    · refine ⟨_, _, front, ?_, .inr cut⟩
      rw [visibleAppend]
      exact frontPrefix.trans (List.prefix_append _ _)
  | rootStop site linked stop =>
    by_cases selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree
    · obtain ⟨installedLabels, _, installedSilent, installed, aligned, _⟩ := LiveDispatch.entry_paired (base := base) site linked paired selected
      exact ⟨installedLabels, _, installed, by rw [silentVisible installedSilent]; exact ⟨_, rfl⟩,
        .inr (.rootStop site linked stop aligned)⟩
    · exact ⟨[], _, .refl _, ⟨_, rfl⟩, .inr (.unselected site linked paired selected)⟩
  | @compilerStop origin _ _ count request selection refused checked =>
    by_cases selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle = some selection.tree
    · have reads (handle : BitVec IntType.i32.width) (demanded : request.lookupDemand = some handle) :
          Stored.Endpoints.Core.childFromHistory origin.host.writer.accepted handle =
            Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted handle := by
        rw [selection.lookup_demand] at demanded
        rw [← Option.some.inj demanded]
        exact selection.selected.trans selected.symm
      obtain ⟨entryLabels, entered, silent, entry, installed⟩ := selection.paired_canonical_pending
        (base := base) (profile := profile) (ready := ready) paired reads
      have seen := (visibleTaus (grow := grow) (sig := sig) count).trans (silentVisible silent).symm
      exact ⟨entryLabels, entered, entry, seen ▸ List.prefix_refl _, .inr (.compilerStop selection refused checked installed)⟩
    · exact ⟨[], _, .refl _, ⟨_, rfl⟩, .inr (.compilerLookup selection paired selected)⟩
  | @give _ site linked entryLabels checkLabels referenceLabels _ _ checked baseline entry _ _ _ replies seen replayBody =>
    by_cases selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree
    · obtain ⟨installed, _, silent, install, aligned, _⟩ := LiveDispatch.entry_paired (base := base) site linked paired selected
      obtain ⟨trace, reached, body, bodyPrefix, result⟩ := replayBody aligned
      have checkedSeen : PayloadPrefix.visible (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) =
          PayloadPrefix.visible (referenceLabels ++ [.tau]) := by
        rw [visibleAppend, visibleAppend, entryVisible entry, List.nil_append, seen, visibleAppend]
        rfl
      have liveSeen : PayloadPrefix.visible (installed ++ trace) = PayloadPrefix.visible trace := by
        rw [visibleAppend, silentVisible silent, List.nil_append]
      refine ⟨_, _, append install body, by rw [checkedSeen, liveSeen]; exact bodyPrefix, ?_⟩
      rcases result with ⟨bodySeen, rejoined⟩ | cut
      · have same := congrArg (fun state => HostFrame.replace state reached.host) replies.scheduler_rejoin
        change HostFrame.replace baseline reached.host = HostFrame.replace checked reached.host at same
        have baselinePair : ReturnFrame.Related.Paired older (HostFrame.replace baseline reached.host) reached := rejoined
        have caller : HostFrame.Related.Paired older checked reached :=
          show ReturnFrame.Related.Paired older (HostFrame.replace checked reached.host) reached from same ▸ baselinePair
        exact .inl ⟨checkedSeen.trans (bodySeen.trans liveSeen.symm), caller⟩
      · exact .inr cut
    · exact ⟨[], _, .refl _, ⟨_, rfl⟩, .inr (.unselected site linked paired selected)⟩
  | stop site linked entry checkedBody _ stopped store seen replayBody =>
    by_cases selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree
    · obtain ⟨_, _, silent, install, aligned, _⟩ := LiveDispatch.entry_paired (base := base) site linked paired selected
      obtain ⟨_, _, body, bodyPrefix, result⟩ := replayBody aligned
      refine ⟨_, _, append install body, ?_, .inr ?_⟩
      · rw [visibleAppend, visibleAppend, entryVisible entry, silentVisible silent, List.nil_append, List.nil_append, seen]
        exact bodyPrefix
      · rcases result with ⟨bodySeen, reached⟩ | cut
        · exact .stopped site stopped checkedBody body reached (store.trans reached.data.1) (seen.trans bodySeen)
        · exact cut
    · exact ⟨[], _, .refl _, ⟨_, rfl⟩, .inr (.unselected site linked paired selected)⟩

theorem stackfulEnd {task : TaskId} (edge : StackfulBodyEnd task start labels finish)
    (outer : ∀ (site : StackfulReturn start), site.segments = []) :
    NestedPlan bindings profile ready base start labels finish := by
  cases edge with
  | «prefix» => exact .segment (.refl _)
  | @exited site _ exit =>
    exact .sequence (.segment (Transition.stackfulComplete (impl := base) exit).steps)
      (.segment (Transition.stackfulExit (impl := base) exit (outer site)).steps)
  | unresolved site _ records last unresolved =>
    exact .segment (Transition.stackfulUnresolved (impl := base) site records.live records.implicitThread last unresolved).steps

theorem stackfulWorker {start reached first : State grow sig} {site : OnStartSite start} {handoff : LowerStartAt site}
    {returned : LowerArgumentReturn handoff reached} {callees : List (ComponentCall.Callee sig)}
    (args : CalleeArguments returned) {Result : Type} (words : Result → List FlatValue)
    (lowered : StringPlanPair profile ready bindings callees first (fun result => args.enter (words result)))
    (asyncMode : args.record.opts.async_ = true) (callback : args.record.opts.callback = none)
    (body : ∀ (entry : State grow sig) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue),
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
        (StringPlanStopped profile ready bindings first leading entry ∧ trailing = [] ∧ last = entry)) := by
  obtain ⟨leading, entry, _, linked, entered | stopped⟩ := args.enter_stackful_after_strings words lowered asyncMode callback
  · obtain ⟨cursor, flat, control⟩ := entered
    obtain ⟨_, _, _, _, _, _, coreRun, ending, outer, delivery⟩ := body entry cursor flat control
    have tail := NestedPlan.sequence coreRun (.sequence (stackfulEnd ending outer) delivery)
    exact ⟨_, _, _, _, linked, .sequence (.segment linked) tail, .inl ⟨cursor, flat, control, tail⟩⟩
  · exact ⟨leading, entry, [], entry, linked, by simpa only [List.append_nil] using NestedPlan.segment (bindings := bindings) linked,
      .inr ⟨stopped, rfl, rfl⟩⟩

theorem localDataGive {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    (data : PayloadPrefix.LocalDataType (sig.payload site.tag)) (payload : Stored.Payload (sig.payload site.tag))
    (field : site.field = .data (sig.payload site.tag) payload) {entryLabels}
    (entryPath : Steps profile ready (specDispatch ready base) site.start entryLabels site.checked)
    (silent : PayloadPrefix.visible entryLabels = [])
    (placed : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok ())
    (prepared : Stored.OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ()) :
    ∃ bodyLabels finish, NestedPlan bindings profile ready base site.start (entryLabels ++ bodyLabels) finish ∧
      ((∃ value checkedLabels reached,
        Steps profile ready (specDispatch ready base) site.checked checkedLabels reached ∧
        reached.ctl = site.cursor.control (site.reply (.ok value)) ∧ bodyLabels = checkedLabels ++ [.tau, .tau, .tau] ∧
        finish.host = reached.host.record (route.reply site.destination site.start.host.nextTicket (.ok value)).1) ∨
      (finish.ctl = [] ∧ ∃ leading reason, PayloadPrefix.visible bodyLabels = leading ++ [.trap reason])) ∧
      finish.host.writer.accepted = site.start.host.writer.accepted ∧
      ∃ canonLabels baseline,
        PayloadPrefix.LocalSteps profile ready (specDispatch ready base) (site.reference site.referenceReply) canonLabels baseline ∧
        PayloadPrefix.visible bodyLabels = PayloadPrefix.visible canonLabels ∧
        baseline = HostFrame.replace finish baseline.host := by
  have entry := Transition.giveEntry site linked silent placed prepared entryPath
  have width : ptrTypeIn site.checked.store (site.destination.context site.inst) = site.destination.width := by
    have memory := site.destination.check_width site.start.store linked.destination
    simp only [PayloadRoot.Site.checked, PayloadRoot.Site.withBody, ptrTypeIn, RecordDestination.context,
      CanonOpts.ptrType, memory, Option.getD_some]
  let reference := site.reference site.referenceReply
  have canonAt := site.reference_at linked site.referenceReply
  rw [field] at canonAt
  have checkAt : site.checked.ctl = site.cursor.control
      (Stored.OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
        (site.destination.context site.inst) site.destination.width (.data (sig.payload site.tag) payload) 0 route.output >>= site.reply) := by
    simp only [PayloadRoot.Site.checked, PayloadRoot.Site.withBody, field]
  obtain ⟨store, result, checkedLabels, canonLabels, checked, canon, seen, outcome⟩ :=
    PayloadPrefix.local_data_leaf_frame (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
      site.destination site.inst (sig.payload site.tag) data payload 0 route.output site.start.store site.checked reference
      (Core3.Grows.refl _) width placed rfl site.cursor site.cursor rfl site.reply site.referenceReply checkAt canonAt
  cases result with
  | error reason =>
    obtain ⟨leading, trapped⟩ := outcome
    exact ⟨_, _, .stop site linked entry checked (.localSegment canon)
      (.trapped (check := site.cursor) rfl rfl ⟨leading, trapped⟩) rfl seen,
      .inr ⟨rfl, leading, reason, seen.trans trapped⟩, rfl, _, _, canon, seen, rfl⟩
  | ok value =>
    let reached := localLeafEnd site.checked site.checked.host store site.cursor.thread site.cursor.frames site.cursor.rest
      (fun result => site.reply (.ok result)) (.ok value)
    let canonical := localLeafEnd reference reference.host store site.cursor.thread site.cursor.frames site.cursor.rest
      site.referenceReply (.ok value)
    let older : ReturnFrame.Substitutions (core3 grow) (HostState sig) := fun _ _ => False
    have segments : ∀ frames, List.Forall₂ (ReturnFrame.Related.Segment older) frames frames :=
      fun _ => List.forall₂_same.mpr fun frame _ => .same frame
    have active : ∀ act, ReturnFrame.Related.Active older act act := fun ⟨_, _, frames⟩ => .mk (segments frames)
    have saved : ∀ act, ReturnFrame.Related.Saved older act act
      | none => .none
      | some act => .some (active act)
    have frame : LinkedCallback.ChildFrameOver older reached canonical site.cursor site.cursor :=
      ⟨rfl, rfl, rfl, rfl, List.forall₂_same.mpr fun act _ => saved act, rfl,
        segments site.cursor.frames, List.forall₂_same.mpr fun act _ => active act⟩
    obtain ⟨left, right, checkReply, canonReply, storeEq, checkHost, canonHost, paired, _, _⟩ :=
      LinkedCallback.MemorySequence.resume_returned_give site value frame (outcome.2.1 0) rfl rfl
    have popFocus : PayloadPrefix.LocalFocus canonical := by
      simp only [canonical, localLeafEnd, PayloadRoot.Site.cursor, PayloadRoot.Site.referenceReply, PayloadPrefix.LocalFocus]
      exact True.intro
    have pop : PayloadPrefix.LocalSteps profile ready (specDispatch ready base) canonical [.tau] right := by
      generalize traceEq : ([.tau] : Trace grow sig) = trace
      have run := canonReply (specDispatch ready base)
      rw [traceEq] at run
      cases run with
      | refl => contradiction
      | cons step tail =>
        cases traceEq
        cases tail
        exact .cons popFocus step (.refl _)
    have replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached canonical left right :=
      ⟨checkReply, canonReply, storeEq, checkHost, canonHost, paired⟩
    refine ⟨_, _, ?_, .inl ⟨value, checkedLabels, reached, checked, rfl, rfl, checkHost⟩,
      ?_, _, _, canon.append pop, ?_, replies.scheduler_rejoin⟩
    · rw [← List.append_assoc]
      exact .give site linked entry checked (.localSegment (canon.append pop)) value replies seen
    · rw [checkHost]
      rfl
    · rw [visibleAppend, visibleAppend, seen]
      rfl

theorem pairedLocalDataGive {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
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
      checked.host.writer.accepted = canonical.host.writer.accepted := by
  have selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree :=
    roots ▸ linked.selected
  obtain ⟨leading, entered, silentEntry, installed, aligned, entryHost⟩ :=
    LiveDispatch.entry_paired (profile := profile) (ready := ready) (base := base) site linked paired selected
  obtain ⟨bodyLabels, checked, plan, _, checkRoots, canonLabels, baseline, body, seen, rejoined⟩ :=
    localDataGive site linked data payload field entryPath silent placed prepared
  obtain ⟨canonical, replay, bodyPair, _, bodyHost⟩ := replayLocal body aligned
  have shared := congrArg (fun current => HostFrame.replace current canonical.host) rejoined
  change HostFrame.replace baseline canonical.host = HostFrame.replace checked canonical.host at shared
  have aligned : HostFrame.Related.Paired older checked canonical :=
    show ReturnFrame.Related.Paired older (HostFrame.replace checked canonical.host) canonical from shared ▸ bodyPair
  refine ⟨_, _, checked, canonical, source plan, append installed replay, aligned, ?_, ?_⟩
  · rw [visibleAppend, visibleAppend, silent, silentVisible silentEntry, List.nil_append, List.nil_append, seen]
  · rw [checkRoots, bodyHost, entryHost, roots]

private theorem rejoinedTail {callees : List (ComponentCall.Callee sig)}
    {left right : Config (core3 grow) (HostState sig)} (paired : HostFrame.Related.Paired older left right) :
    RejoinedWorkerTail profile ready bindings callees older left right := by
  refine ⟨fun run => LiveDispatch.paired_replay paired run, ?_⟩
  intro empty _ _ _ _ between
  have replace : HostFrame.replace left right.host = right :=
    ReturnFrame.Related.Paired.without_substitution paired empty
  exact ⟨between.runs.1.steps, replace ▸ LiveDispatch.interleaving_steps between,
    fun roots => (LiveDispatch.interleaving_paired_roots between roots).2⟩

open ReturnFrame.Occurrence in
theorem rejoinedOccurrenceWorker {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
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
        RejoinedWorkerTail profile ready bindings callees older checked canonical) := by
  obtain ⟨checkBody, canonBody, mark, leftMark, rightMark, _, reply⟩ :=
    CallbackRange.rebasePublicOccurrenceExit site checked canonical checkQuiet canonQuiet body
  exact ⟨checkBody, canonBody, mark, leftMark, rightMark, fun active =>
    let ⟨checked, canonical, tracks, paired⟩ := reply active
    ⟨checked, canonical, tracks, rejoinedTail paired⟩⟩

private theorem pendingRecursiveRoot {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {callees : List (ComponentCall.Callee sig)} (linked : site.Linked bindings)
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree) :
    PendingRecursiveRoot profile ready bindings callees older site incoming := by
  obtain ⟨labels, entered, quiet, installed, aligned, hostEq⟩ := LiveDispatch.entry_paired_tracks
    (profile := profile) (ready := ready) (base := ComponentCall.hostWithComponent bindings callees) site linked paired selected
  exact ⟨labels, entered, silentVisible quiet, installed, aligned, hostEq⟩

open ReturnFrame.Occurrence in
private theorem rootRefusalTrails {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {callees : List (ComponentCall.Callee sig)} {issue leading}
    (checked : site.EntryPrefix profile ready (ComponentCall.hostWithComponent bindings callees) leading
      (site.withBody (site.reply (.error issue)))) :
    ∀ place, Trail profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
      site.start (some place) (leading ++ [.tau, .tau, .tau]) (site.refusedReply issue) (some place) := by
  intro place
  refine (checked place).toTrail.append ?_
  let reply := route.reply site.destination site.start.host.nextTicket (.error issue)
  have completion := Plain.give_completion_trail (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (ComponentCall.hostWithComponent bindings callees))
    (start := site.withBody (site.reply (.error issue))) reply (site.entryPlace place) rfl
  have restored : (Edit.pop : Edit (core3 grow) (HostState sig)).follow (site.entryPlace place) = some place := by
    cases place with
    | active activation _ => cases activation <;> rfl
    | saved _ _ => rfl
  exact restored ▸ completion

private theorem classifyRecursiveRoot {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {callees : List (ComponentCall.Callee sig)} (linked : site.Linked bindings)
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (cut : PayloadRoot.Cut site profile ready bindings (RecursiveGivePaths profile ready bindings callees older incoming route site)
      (ComponentCall.hostWithComponent bindings callees)) :
    ReachedRecursiveRoot profile ready bindings callees older incoming site := by
  have pending : PendingRecursiveRoot profile ready bindings callees older site incoming :=
    pendingRecursiveRoot site linked paired selected
  cases cut with
  | refused _ silent run => exact .refused silent (rootRefusalTrails site run) pending
  | placementTrap _ _ verdict run => exact .placementTrap verdict run pending
  | placed silent verdict prepared run body => exact .placed silent verdict prepared run pending body

theorem reachedRecursiveGive {route : GiveEffectRoute} {request : CoreGiveRequest bindings start}
    (selection : request.Selected route) {callees : List (ComponentCall.Callee sig)}
    (family : RecursiveGiveDomain selection)
    (paired : HostFrame.Related.Paired older start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle = some selection.tree) :
    ReachedRecursiveGive profile ready callees selection older incoming := by
  cases preflight : selection.preflight with
  | error issue =>
    obtain ⟨count, checked⟩ := selection.compiler_refusal_tracks (profile := profile) (ready := ready) preflight
      (ComponentCall.hostWithComponent bindings callees) rfl
    have reads : ∀ handle, request.lookupDemand = some handle →
        Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted handle := by
      intro handle demand
      rw [selection.lookup_demand] at demand
      cases demand
      exact selection.selected.trans selected.symm
    obtain ⟨labels, _, silent, canonical, kept, pending⟩ := selection.paired_canonical_pending_tracks
      (profile := profile) (ready := ready) (base := ComponentCall.hostWithComponent bindings callees) paired reads
    refine .refused preflight (checked (.active 0 0)).steps (silentVisible silent) (canonical (.active 0 0)).toTrail.steps pending kept ?_
    exact ⟨List.replicate count .tau, labels, visibleTaus count, silentVisible silent,
      fun place => ⟨some place, _, checked place, (canonical place).toTrail⟩⟩
  | ok result =>
    obtain ⟨field, plan⟩ := result
    obtain ⟨tag, payload, arity, children, picked, linked⟩ := selection.compiler_success preflight
    have supported := family tag payload arity children field plan picked preflight
    have liveRoot : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted
        (selection.site tag payload arity children field).handle = some (selection.site tag payload arity children field).tree :=
      selected.trans (congrArg some picked)
    have tail (left right : Config (core3 grow) (HostState sig)) (aligned : HostFrame.Related.Paired older left right) :
        RejoinedWorkerTail profile ready bindings callees older left right := rejoinedTail aligned
    have occurrences : PayloadRoot.Cut (selection.site tag payload arity children field) profile ready bindings
        (RecursiveGiveOccurrencePaths profile ready bindings callees older incoming route (selection.site tag payload arity children field))
        (ComponentCall.hostWithComponent bindings callees) := by
      cases route with
      | memory pointer => exact CallbackRange.linkedMemoryOccurrenceBody _ linked supported paired liveRoot rfl
      | flat schema => exact CallbackRange.linkedFlatOccurrenceBody _ linked supported paired liveRoot rfl
    refine .compiled preflight picked linked (classifyRecursiveRoot _ linked paired liveRoot ?_) occurrences
    cases route with
    | memory pointer =>
      exact CallbackRange.linkedMemoryRejoinPaths (profile := profile) (ready := ready)
        (base := ComponentCall.hostWithComponent bindings callees) _ linked supported paired liveRoot rfl _ tail
    | flat schema =>
      exact CallbackRange.linkedFlatAggregateRejoinPaths (profile := profile) (ready := ready)
        (base := ComponentCall.hostWithComponent bindings callees) _ linked supported paired liveRoot rfl _ tail

open ReturnFrame.Occurrence in
theorem alignRecursiveEntry {route : GiveEffectRoute} {request : CoreGiveRequest bindings start}
    {selection : request.Selected route} {callees : List (ComponentCall.Callee sig)}
    (entry : ReachedRecursiveGive profile ready callees selection older incoming)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish) :
    RecursiveGiveEntryAlignment profile ready callees selection older incoming labels finish := by
  cases entry with
  | refused preflight checked _ _ pending _ tracks =>
    exact .compilerRefused preflight pending tracks (alignWorkerBody checked run)
  | @compiled tag payload arity children field plan preflight root linked cut occurrenceCut =>
    have pending : PendingRecursiveRoot profile ready bindings callees older
        (selection.site tag payload arity children field) incoming := by
      cases cut <;> assumption
    refine .compiled preflight root linked pending ?_
    cases occurrenceCut with
    | refused issue silent checked =>
      have tracks := rootRefusalTrails (selection.site tag payload arity children field) checked
      exact .refused (issue := issue) silent tracks (alignWorkerBody (tracks (.active 0 0)).steps run)
    | placementTrap reason count verdict checked =>
      exact .placementTrap (reason := reason) (count := count) verdict checked (alignWorkerBody checked.steps run)
    | placed silent verdict prepared checked body =>
      exact .placed silent verdict prepared checked body (alignWorkerBody checked.steps run)

theorem recursiveGiveAfterCallback {route : GiveEffectRoute} {request : CoreGiveRequest bindings finish}
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
        Stored.Endpoints.Core.childFromHistory reached.host.writer.accepted selection.handle ≠ some selection.tree) := by
  obtain ⟨checkedLabels, canonLabels, reached, checked, canonical, aligned, checkSeen, canonSeen, _, checkRoots, canonRoots⟩ :=
    CallbackPrefix.replay path rfl covers paired
  refine ⟨checkedLabels, canonLabels, reached, checked, canonical, checkSeen, canonSeen, aligned, ?_, ?_⟩
  · intro earlier
    apply reachedRecursiveGive selection family aligned
    rw [canonRoots, ← earlier, ← checkRoots]
    exact selection.selected
  · by_cases selected : Stored.Endpoints.Core.childFromHistory reached.host.writer.accepted selection.handle = some selection.tree
    · exact .inl (reachedRecursiveGive selection family aligned selected)
    · exact .inr selected

theorem recursiveGiveAfterInterleaving {route : GiveEffectRoute} {request : CoreGiveRequest bindings finish}
    (selection : request.Selected route) {callees : List (ComponentCall.Callee sig)} {actions prior outgoing}
    (between : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      start prior actions labels finish outgoing)
    (roots : prior.writer.accepted = start.host.writer.accepted) (family : RecursiveGiveDomain selection) :
    Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish ∧
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
      (HostFrame.replace start prior) labels (HostFrame.replace finish outgoing) ∧
    ReachedRecursiveGive profile ready callees selection (fun _ _ => False) (HostFrame.replace finish outgoing) := by
  obtain ⟨paired, reachedRoots⟩ := LiveDispatch.interleaving_paired_roots between roots
  refine ⟨between.runs.1.steps, LiveDispatch.interleaving_steps between, reachedRecursiveGive selection family paired ?_⟩
  change Stored.Endpoints.Core.childFromHistory outgoing.writer.accepted selection.handle = some selection.tree
  rw [reachedRoots]
  exact selection.selected

theorem recursiveRequestCut (request : CoreGiveRequest bindings start) {callees : List (ComponentCall.Callee sig)}
    (paired : HostFrame.Related.Paired older start incoming) : RecursiveRequestCut profile ready callees request older incoming := by
  classical
  by_cases reads : ∀ handle, request.lookupDemand = some handle →
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle =
      Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted handle
  · rcases request.selector_result with ⟨reason, trap⟩ | ⟨verdict, evaluated⟩
    · obtain ⟨_, _, left, right⟩ := request.paired_admission_trap (profile := profile) (ready := ready)
        (base := ComponentCall.hostWithComponent bindings callees) (ComponentCall.hostWithComponent bindings callees) rfl paired trap
      exact .trapped trap left right
    · cases verdict with
      | error issue =>
        obtain ⟨_, _, _, _, progress, left, right, aligned, checkedHost, canonicalHost⟩ := request.paired_admission_refusal_tracks
          (profile := profile) (ready := ready) (base := ComponentCall.hostWithComponent bindings callees)
          (ComponentCall.hostWithComponent bindings callees) rfl paired evaluated reads
        exact .refused evaluated progress left right aligned checkedHost canonicalHost (rejoinedTail aligned)
      | ok result =>
        obtain ⟨route, ⟨selection⟩⟩ := request.selected_of_return evaluated
        have selected := (reads selection.handle selection.lookup_demand).symm.trans selection.selected
        exact .admitted selection selected (fun family => reachedRecursiveGive selection family paired selected)
  · push Not at reads
    obtain ⟨handle, demand, different⟩ := reads
    exact .lookup demand different

theorem recursiveInstallCut {callees : List (ComponentCall.Callee sig)} {label}
    (install : GiveInstall bindings (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start label finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    DirectGiveAt bindings start ∨ ∃ request : CoreGiveRequest bindings start, RecursiveRequestCut profile ready callees request older incoming := by
  rcases install.request with ⟨⟨request⟩⟩ | direct
  · exact .inr ⟨request, recursiveRequestCut request paired⟩
  · exact .inl direct

open ReturnFrame.Occurrence in
theorem actualCallbackGive {callees : List (ComponentCall.Callee sig)} {protectedReturn label trailing}
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
      (WorkerOccurrencePrefix profile ready bindings callees retained start incoming mark) := by
  obtain ⟨peer, finalMark, live, aligned, kept, checkedTrail, liveTrail, movement, _⟩ := replay covers paired outside
  exact ⟨append checkedTrail.steps (.cons actual tail), .request rfl checkedTrail.steps live aligned
    ⟨finalMark, checkedTrail, liveTrail, kept, movement⟩ install (recursiveInstallCut install aligned) tail⟩

theorem classifyReplay {callees : List (ComponentCall.Callee sig)}
    (replay : PairedReplay bindings profile ready (ComponentCall.hostWithComponent bindings callees)
      older start incoming labels finish) : ClassifiedWorkerTail profile ready bindings callees older start incoming labels finish := by
  cases replay with
  | complete live paired => exact .complete live paired trivial
  | request split checked live paired install tail =>
    exact .request split checked live paired trivial install (recursiveInstallCut install paired) tail
  | boundary split checked live paired boundary stepLeft stepRight tail =>
    exact .boundary split checked live paired trivial boundary stepLeft stepRight tail

open ReturnFrame.Occurrence in
theorem classifyWithOccurrence {callees : List (ComponentCall.Callee sig)} {mark : Option Location}
    {retained : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming)
    (outside : Outside retained (segmentStorage start) (segmentStorage incoming) mark) :
    ClassifiedWorkerTail profile ready bindings callees older start incoming labels finish
      (WorkerOccurrencePrefix profile ready bindings callees retained start incoming mark) := by
  induction run generalizing incoming mark with
  | refl => exact .complete (.refl _) paired ⟨mark, .done _ _, .done _ _, outside, fun cursor => ⟨cursor, .done _ _, .done _ _⟩⟩
  | @cons before middle after label labels step tail ih =>
    have empty : WorkerOccurrencePrefix profile ready bindings callees retained before incoming mark [] before incoming :=
      ⟨mark, .done _ _, .done _ _, outside, fun cursor => ⟨cursor, .done _ _, .done _ _⟩⟩
    rcases LiveDispatch.classify_step (bindings := bindings) step with unchanged | install
    · obtain ⟨other, live, aligned | boundary⟩ := HostFrame.Related.paired_step paired unchanged
      · have edit := pair_edit paired label
        let nextMark := mark.bind (transitionEdit before label).follow
        have nextOutside : Outside retained (segmentStorage middle) (segmentStorage other) nextMark := by
          rw [step_edit step, step_edit live, ← edit]
          exact outside_edit outside _
        have extend {prefixLabels left right}
            (tracks : WorkerOccurrencePrefix profile ready bindings callees retained middle other nextMark prefixLabels left right) :
            WorkerOccurrencePrefix profile ready bindings callees retained before incoming mark (label :: prefixLabels) left right := by
          obtain ⟨last, lhs, rhs, kept, movement⟩ := tracks
          refine ⟨last, .step step lhs, .step live (edit ▸ rhs), kept, ?_⟩
          intro cursor
          obtain ⟨target, leftTrail, rightTrail⟩ := movement (cursor.bind (transitionEdit before label).follow)
          exact ⟨target, .step step leftTrail, .step live (edit ▸ rightTrail)⟩
        cases ih aligned nextOutside with
        | complete replay paired trails => exact .complete (.cons live replay) paired (extend trails)
        | request split checked replay paired trails install cut rest =>
          exact .request (congrArg (List.cons _) split) (.cons step checked) (.cons live replay)
            paired (extend trails) install cut rest
        | boundary split checked replay paired trails cut lhs rhs rest =>
          exact .boundary (congrArg (List.cons _) split) (.cons step checked) (.cons live replay)
            paired (extend trails) cut lhs rhs rest
      · exact .boundary (leading := []) rfl (.refl _) (.refl _) paired empty boundary step live tail
    · exact .request (leading := []) rfl (.refl _) (.refl _) paired empty install (recursiveInstallCut install paired) tail

private theorem mapWorkerTrack {callees : List (ComponentCall.Callee sig)} {track next}
    (path : ClassifiedWorkerTail profile ready bindings callees older start incoming labels finish track)
    (carry : ∀ trace left right, HostFrame.Related.Paired older left right → track trace left right → next trace left right) :
    ClassifiedWorkerTail profile ready bindings callees older start incoming labels finish next := by
  cases path with
  | complete live paired trail => exact .complete live paired (carry _ _ _ paired trail)
  | request split checked live paired trail install cut tail =>
    exact .request split checked live paired (carry _ _ _ paired trail) install cut tail
  | boundary split checked live paired trail cut lhs rhs tail =>
    exact .boundary split checked live paired (carry _ _ _ paired trail) cut lhs rhs tail

open ReturnFrame.Occurrence in
private theorem requestWorkerTail {callees : List (ComponentCall.Callee sig)}
    {request reference : Config (core3 grow) (HostState sig)} {seen : Trace grow sig}
    (arrived : RequestExitOccurrences profile ready (ComponentCall.hostWithComponent bindings callees) bindings
      request reference seen start incoming)
    (paired : HostFrame.Related.Paired older start incoming) :
    RequestWorkerTail profile ready bindings callees older request reference seen start incoming := by
  intro labels finish run
  refine mapWorkerTrack (classifyWithOccurrence run paired
    (paired_outside (left := HostFrame.replace start incoming.host) paired)) ?_
  intro added left right _ worker
  obtain ⟨leading, referenceLabels, checkSeen, canonSeen, requestPaths⟩ := arrived
  obtain ⟨_, _, _, _, movement⟩ := worker
  refine ⟨leading ++ added, referenceLabels ++ added, ?_, ?_, ?_⟩
  · rw [visibleAppend, checkSeen]
  · rw [visibleAppend, canonSeen]
  · intro place
    obtain ⟨leftPlace, rightPlace, checkPath, canonPath⟩ := requestPaths place
    obtain ⟨checkReached, checkTail, _⟩ := movement leftPlace
    obtain ⟨canonReached, _, canonTail⟩ := movement rightPlace
    exact ⟨checkReached, canonReached, checkPath.append checkTail, canonPath.append canonTail⟩

open ReturnFrame.Occurrence in
private theorem appendRefusalTracks {callees : List (ComponentCall.Callee sig)}
    {request reference left right : Config (core3 grow) (HostState sig)} {seen : Trace grow sig} {checkCount canonCount : Nat}
    (arrived : RequestExitOccurrences profile ready (ComponentCall.hostWithComponent bindings callees) bindings
      request reference seen start incoming)
    (checked : ∀ place, Prefix profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
      start place (List.replicate checkCount .tau) left place)
    (canonical : ∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
      incoming place (List.replicate canonCount .tau) right place) :
    RequestExitOccurrences profile ready (ComponentCall.hostWithComponent bindings callees) bindings request reference seen left right := by
  obtain ⟨frontLeft, frontRight, leftSeen, rightSeen, paths⟩ := arrived
  refine ⟨frontLeft ++ List.replicate checkCount .tau, frontRight ++ List.replicate canonCount .tau, ?_, ?_, ?_⟩
  · rw [visibleAppend, leftSeen, visibleTaus, List.append_nil]
  · rw [visibleAppend, rightSeen, visibleTaus, List.append_nil]
  intro mark
  obtain ⟨leftMost, rightMost, leftPath, rightPath⟩ := paths mark
  refine ⟨leftMost, rightMost, leftPath.append ?_, rightPath.append ?_⟩
  · cases leftMost with
    | none => exact Trail.absent (checked (.active 0 0)).toTrail.steps
    | some place => exact (checked place).toTrail
  · cases rightMost with
    | none => exact Trail.absent (canonical (.active 0 0)).toTrail.steps
    | some place => exact (canonical place).toTrail

open ReturnFrame.Occurrence in
theorem requestWorkerRefusals {callees : List (ComponentCall.Callee sig)}
    {request reference : Config (core3 grow) (HostState sig)} {seen : Trace grow sig}
    (arrived : RequestExitOccurrences profile ready (ComponentCall.hostWithComponent bindings callees) bindings
      request reference seen start incoming)
    (paired : HostFrame.Related.Paired older start incoming) :
    RequestWorkerRefusals profile ready bindings callees older request reference seen start incoming := by
  intro labels finish run
  induction lengthEq : labels.length using Nat.strong_induction_on generalizing start incoming seen labels finish with
  | ind limit ih =>
    cases requestWorkerTail arrived paired run with
    | complete live paired trail =>
      exact ⟨labels, labels, [], finish, _, (List.append_nil _).symm, run, live, rfl, .refl _, paired, trail, .done⟩
    | @boundary leading label remaining beforeLeft beforeRight afterLeft afterRight split checked live paired trail cut lhs rhs tail =>
      exact ⟨leading, leading, label :: remaining, beforeLeft, beforeRight, split, checked, live, rfl, .cons lhs tail,
        paired, trail, .boundary cut lhs rhs⟩
    | @request leading label remaining beforeLeft beforeRight afterLeft split checked live paired trail install cut tail =>
      have first : Step profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) beforeLeft label afterLeft := by
        cases install with
        | direct focused _ => exact .call focused
        | core focused calling _ => exact .coreCallout focused calling
      have run := Steps.cons first tail
      have stop (endCut : WorkerRefusalCut profile ready bindings callees older beforeLeft beforeRight (label :: remaining)) :
          WorkerRefusalRun profile ready bindings callees older request reference seen start incoming labels finish :=
        ⟨leading, leading, label :: remaining, beforeLeft, beforeRight, split, checked, live, rfl, run, paired, trail, endCut⟩
      rcases cut with direct | ⟨next, cut⟩
      · exact stop (.request install (.inl direct))
      cases cut with
      | lookup demand different =>
        exact stop (.request install (.inr ⟨next, .lookup demand different, .inl ⟨_, demand, different⟩⟩))
      | trapped caller left right =>
        exact stop (.request install (.inr ⟨next, .trapped caller left right, .inr (.inl ⟨_, caller⟩)⟩))
      | admitted selection selected body =>
        exact stop (.request install (.inr ⟨next, .admitted selection selected body, .inr (.inr (.inl ⟨_, ⟨selection⟩⟩))⟩))
      | @refused issue checkCount canonCount replied liveReply verdict positive left right aligned leftHost rightHost rest =>
        have reflected := (left (.active 0 0)).toTrail.steps
        rcases splitSilent reflected run with ⟨suffix, spliced, suffixRun⟩ | short
        · have smaller : suffix.length < limit := by
            rw [← lengthEq, split, spliced, List.length_append, List.length_append, List.length_replicate]
            omega
          have continued := appendRefusalTracks trail left right
          obtain ⟨middle, canonMiddle, trailing, lastLeft, lastRight, ends, checkMiddle, liveMiddle, matched, checkTail, related, paths, cut⟩ :=
            ih suffix.length smaller continued aligned suffixRun rfl
          refine ⟨leading ++ (List.replicate checkCount .tau ++ middle), leading ++ (List.replicate canonCount .tau ++ canonMiddle),
            trailing, lastLeft, lastRight, ?_, append checked (append reflected checkMiddle),
            append live (append (right (.active 0 0)).toTrail.steps liveMiddle), ?_, checkTail, related, ?_, cut⟩
          · rw [split, spliced, ends]
            simp only [List.append_assoc]
          · simp only [visibleAppend, visibleTaus, List.nil_append, matched]
          · simpa only [visibleAppend, visibleTaus, List.nil_append, List.append_assoc] using paths
        · exact stop (.request install (.inr ⟨next, .refused verdict positive left right aligned leftHost rightHost rest,
            .inr (.inr (.inr ⟨issue, checkCount, replied, short, verdict, reflected⟩))⟩))

open ReturnFrame.Occurrence in
private theorem appendExitOccurrences {origin reference left right : Config (core3 grow) (HostState sig)}
    {seen next : Trace grow sig}
    (front : RequestExitOccurrences profile ready base bindings origin reference seen start incoming)
    (back : RequestExitOccurrences profile ready base bindings start incoming next left right) :
    RequestExitOccurrences profile ready base bindings origin reference (seen ++ next) left right := by
  obtain ⟨beforeLeft, beforeRight, leftSeen, rightSeen, older⟩ := front
  obtain ⟨afterLeft, afterRight, leftNext, rightNext, newer⟩ := back
  refine ⟨beforeLeft ++ afterLeft, beforeRight ++ afterRight, ?_, ?_, ?_⟩
  · rw [visibleAppend, leftSeen, leftNext]
  · rw [visibleAppend, rightSeen, rightNext]
  · intro mark
    obtain ⟨leftPlace, rightPlace, leftPath, rightPath⟩ := older mark
    have leftTail : ∃ reached, Trail profile ready (specDispatch ready base) start leftPlace afterLeft left reached := by
      cases leftPlace with
      | none => obtain ⟨_, _, run, _⟩ := newer mark; exact ⟨none, .absent run.steps⟩
      | some place => obtain ⟨reached, _, run, _⟩ := newer place; exact ⟨reached, run⟩
    have rightTail : ∃ reached, Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming rightPlace afterRight right reached := by
      cases rightPlace with
      | none => obtain ⟨_, _, _, run⟩ := newer mark; exact ⟨none, .absent run.steps⟩
      | some place => obtain ⟨_, reached, _, run⟩ := newer place; exact ⟨reached, run⟩
    obtain ⟨leftReached, lrun⟩ := leftTail
    obtain ⟨rightReached, rrun⟩ := rightTail
    exact ⟨leftReached, rightReached, leftPath.append lrun, rightPath.append rrun⟩

theorem compilerStopAfterWorkerPrefix {callees : List (ComponentCall.Callee sig)} {route : GiveEffectRoute}
    {request : CoreGiveRequest bindings start} (selection : request.Selected route) {issue : Stored.Endpoints.RecordLower.Issue}
    {origin reference : Config (core3 grow) (HostState sig)} {seen : Trace grow sig}
    (refused : selection.preflight = .error issue)
    (paired : HostFrame.Related.Paired older start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle = some selection.tree)
    (arrived : RequestExitOccurrences profile ready (ComponentCall.hostWithComponent bindings callees) bindings
      origin reference seen start incoming)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish) :
    CompilerStopSuffix profile ready callees selection issue older origin reference incoming seen labels finish := by
  have domain : RecursiveGiveDomain selection := by
    intro _ _ _ _ _ _ _ compiled
    rw [refused] at compiled
    contradiction
  cases reachedRecursiveGive (callees := callees) (profile := profile) (ready := ready) selection domain paired selected with
  | @refused reported count leading entered verdict checked _ canonical pending host paths =>
    have same := Except.error.inj (refused.symm.trans verdict)
    subst reported
    refine ⟨count, checked, ?_⟩
    rcases splitSilent checked run with ⟨suffix, exactTrace, actualTail⟩ | short
    · exact .inr ⟨suffix, leading, entered, exactTrace, actualTail, canonical, pending, host,
        (List.append_nil seen) ▸ appendExitOccurrences arrived paths⟩
    · exact .inl short
  | compiled verdict _ _ _ _ =>
    rw [refused] at verdict
    contradiction

open ReturnFrame.Occurrence in
private theorem replayRejoinedCallback {callees : List (ComponentCall.Callee sig)}
    {request reference : Config (core3 grow) (HostState sig)} {checkPrefix canonPrefix : Trace grow sig}
    (arrived : CoupledOccurrencePaths profile ready (ComponentCall.hostWithComponent bindings callees) bindings
      request reference checkPrefix canonPrefix start incoming)
    (paired : HostFrame.Related.Paired older start incoming)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish) :
    RejoinedCallbackReplay profile ready bindings callees older request reference start incoming checkPrefix canonPrefix labels finish := by
  let protectedReturn := fun resume => ∃ peer, older resume peer
  have replayPrefix {leading reached}
      (replay : ActualCallbackReplay bindings profile ready (ComponentCall.hostWithComponent bindings callees)
        protectedReturn start leading reached) :
      ∃ peer, Steps profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming leading peer ∧ HostFrame.Related.Paired older reached peer ∧
        OccurrenceTransport profile ready (ComponentCall.hostWithComponent bindings callees) bindings
          start incoming leading leading reached peer ∧
        CoupledOccurrencePaths profile ready (ComponentCall.hostWithComponent bindings callees) bindings request reference
          (checkPrefix ++ leading) (canonPrefix ++ leading) reached peer := by
    obtain ⟨peer, _, live, aligned, _, _, _, tracks, movement⟩ :=
      replay (fun first second holds => ⟨second, holds⟩) paired
        (paired_outside (left := HostFrame.replace start incoming.host) paired)
    refine ⟨peer, live, aligned, movement, ?_⟩
    intro place
    obtain ⟨middle, checked, canonical⟩ := arrived place
    obtain ⟨next, checkTail, canonTail⟩ := tracks middle
    exact ⟨next, checked.append checkTail, canonical.append canonTail⟩
  cases CallbackPrefix.classifyActual (bindings := bindings) (protectedReturn := protectedReturn) run with
  | complete _ replay _ =>
    obtain ⟨peer, live, aligned, movement, tracks⟩ := replayPrefix replay
    exact ⟨labels, [], finish, peer, (List.append_nil _).symm, run, live, aligned, tracks, movement, .inl ⟨rfl, rfl⟩⟩
  | boundary split _ growing replay cut step tail =>
    obtain ⟨peer, live, aligned, movement, tracks⟩ := replayPrefix replay
    exact ⟨_, _, _, peer, split, growing.steps, live, aligned, tracks, movement,
      .inr ⟨_, _, _, rfl, step, tail, cut, fun install => recursiveInstallCut install aligned⟩⟩

open ReturnFrame.Occurrence in
private theorem carryAllocatorTransport {callees : List (ComponentCall.Callee sig)}
    {checkEntry canonEntry checked canonical : Config (core3 grow) (HostState sig)}
    {checkTrace canonTrace checkReply canonReply : Trace grow sig} {mark : Option Location}
    (tracked : AllocatorMark profile ready (ComponentCall.hostWithComponent bindings callees) bindings older
      checkEntry canonEntry checkTrace canonTrace start incoming mark)
    (returned : OccurrenceTransport profile ready (ComponentCall.hostWithComponent bindings callees) bindings
      start incoming checkReply canonReply checked canonical) :
    ∃ reached, AllocatorMark profile ready (ComponentCall.hostWithComponent bindings callees) bindings older
      checkEntry canonEntry (checkTrace ++ checkReply) (canonTrace ++ canonReply) checked canonical reached := by
  obtain ⟨move, trails, transport⟩ := returned
  have kept := transport older [mark] (outsideMarks_singleton.mpr tracked.outside)
  obtain ⟨left, right⟩ := trails mark
  refine ⟨move mark, outsideMarks_singleton.mp kept, tracked.checkedTrail.append left,
    tracked.canonicalTrail.append right, ?_⟩
  intro place
  obtain ⟨middle, lhs, rhs⟩ := tracked.movement place
  exact ⟨move middle, lhs.append (trails middle).1, rhs.append (trails middle).2⟩

open ReturnFrame.Occurrence in
theorem alignPublicTransportWorker {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {callees : List (ComponentCall.Callee sig)} {entered left right : Config (core3 grow) (HostState sig)}
    {checkEntry canonEntry seen : Trace grow sig} {value : route.output.Result}
    (body : PublicSuccessTransport profile ready (ComponentCall.hostWithComponent bindings callees) bindings older
      site incoming entered checkEntry canonEntry value seen left right)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) site.start labels finish) :
    PublicTransportWorkerAlignment profile ready bindings callees older site incoming left right checkEntry canonEntry seen labels finish := by
  obtain ⟨checkBody, canonBody, mark, checkSeen, canonSeen, transport, _, _, complete⟩ := body
  obtain ⟨moveBody, through, outsideBody⟩ := transport
  refine ⟨checkBody, canonBody, mark, checkSeen, canonSeen, ⟨moveBody, through, outsideBody⟩,
    alignWorkerBody (through none).1.steps run, ?_⟩
  intro tail split actualTail active
  obtain ⟨checked, canonical, _, _, paired, returned⟩ := complete active
  obtain ⟨move, tracks, outside⟩ := returned
  let dispatch := specDispatch ready (ComponentCall.hostWithComponent (grow := grow) bindings callees)
  have reply : Steps profile ready dispatch left (List.replicate 3 .tau) checked :=
    stripExactPrefix (through none).1.steps (tracks none).1.steps
  rcases splitSilent reply actualTail with ⟨suffix, replySplit, suffixRun⟩ | short
  · have smaller : suffix.length < labels.length := by
      simp only [split, replySplit, List.length_append, List.length_replicate]
      omega
    refine .inr ⟨suffix, checked, canonical, replySplit, smaller, suffixRun, paired, ⟨move, tracks, outside⟩, rejoinedTail paired,
      replayRejoinedCallback (fun cursor => ⟨move cursor, tracks cursor⟩) paired suffixRun, ?_, ?_⟩
    · intro entrySeen
      rcases classifyReachedGrowth (tracks none).1.steps with certified | openUpdate
      · refine .inl ⟨certified, ?_, paired, ⟨move, tracks, outside⟩⟩
        rw [visibleAppend, visibleAppend, visibleAppend, visibleAppend, checkSeen, canonSeen, entrySeen]
        have silentCanon : PayloadPrefix.visible ([.tau] : Trace grow sig) = [] := visibleTaus 1
        have silentCheck : PayloadPrefix.visible ([.tau, .tau, .tau] : Trace grow sig) = [] := visibleTaus 3
        rw [silentCanon, silentCheck]
      · exact .inr openUpdate
    · intro retained enclosingLeft enclosingRight leftTrace rightTrace cursor tracked
      obtain ⟨reached, marked⟩ := carryAllocatorTransport tracked ⟨move, tracks, outside⟩
      exact ⟨reached, marked, classifyWithOccurrence suffixRun paired marked.outside⟩
  · exact .inl short

open ReturnFrame.Occurrence in
theorem alignPublicGiveWorker {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {callees : List (ComponentCall.Callee sig)} {origin reference entered left right : Config (core3 grow) (HostState sig)}
    {checkLabels canonLabels prior seen : Trace grow sig} {verdict : Except Stored.Endpoints.RecordLower.Issue route.output.Result}
    (checked : site.EntryPrefix profile ready (ComponentCall.hostWithComponent bindings callees) checkLabels site.checked)
    (canonical : ∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
      incoming place canonLabels entered (site.entryPlace place))
    (checkQuiet : PayloadPrefix.visible checkLabels = []) (canonQuiet : PayloadPrefix.visible canonLabels = [])
    (body : PublicOccurrenceExit profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site entered verdict seen left right)
    (arrived : RequestExitOccurrences profile ready (ComponentCall.hostWithComponent bindings callees) bindings
      origin reference prior site.start incoming)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) site.start labels finish) :
    PublicGiveWorkerAlignment profile ready bindings callees older site entered left right verdict
      origin reference incoming checkLabels canonLabels prior seen labels finish := by
  obtain ⟨bodyLabels, liveLabels, mark, checkBody, canonBody, bodyTracks, reached⟩ :=
    CallbackRange.rebasePublicOccurrenceExitWithPop site checked canonical checkQuiet canonQuiet body
  have throughBody := append (checked (.active 0 0)).toTrail.steps checkBody.steps
  refine ⟨bodyLabels, liveLabels, mark, checkBody, canonBody, appendExitOccurrences arrived bodyTracks,
    alignWorkerBody throughBody run, ?_⟩
  intro tail split actualTail active
  obtain ⟨replied, peer, pop, tracks, kind, coupled⟩ := reached active
  rcases splitSilent (count := 3) pop actualTail with ⟨suffix, replySplit, suffixRun⟩ | short
  · have smaller : suffix.length < labels.length := by
      simp only [split, replySplit, List.length_append, List.length_replicate]
      omega
    have paths := appendExitOccurrences arrived tracks
    refine .inr ⟨suffix, replied, peer, replySplit, smaller, suffixRun, paths, ?_⟩
    cases verdict with
    | error => exact kind
    | ok => exact ⟨kind, coupled, replayRejoinedCallback coupled kind suffixRun, requestWorkerRefusals paths kind suffixRun⟩
  · exact .inl short

open ReturnFrame.Occurrence in
private theorem alignLocalPublicRefusal {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {callees : List (ComponentCall.Callee sig)} {entered left right : Config (core3 grow) (HostState sig)}
    {checkEntry canonEntry seen : Trace grow sig} {issue : Stored.Endpoints.RecordLower.Issue}
    (checked : site.EntryPrefix profile ready (ComponentCall.hostWithComponent bindings callees) checkEntry site.checked)
    (canonical : ∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
      incoming place canonEntry entered (site.entryPlace place))
    (canonQuiet : PayloadPrefix.visible canonEntry = [])
    (reached : PublicOccurrenceExit profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site entered (.error issue) seen left right)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) site.start labels finish)
    (checkQuiet : PayloadPrefix.visible checkEntry = []) :
    PublicGiveWorkerAlignment profile ready bindings callees older site entered left right (.error issue)
      site.start incoming incoming checkEntry canonEntry [] seen labels finish := by
  have arrived : RequestExitOccurrences profile ready (ComponentCall.hostWithComponent bindings callees) bindings
      site.start incoming [] site.start incoming :=
    ⟨[], [], rfl, rfl, fun place => ⟨some place, some place, .done _ _, .done _ _⟩⟩
  exact alignPublicGiveWorker site checked canonical checkQuiet canonQuiet reached arrived run

theorem linkedMemoryWorkerBody {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    {callees : List (ComponentCall.Callee sig)}
    (linked : site.Linked bindings) (family : RecursiveCollectionType (sig.payload site.tag))
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : (ComponentCall.hostWithComponent bindings callees).embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) site.start labels finish) :
    PayloadRoot.Cut site profile ready bindings (LinkedMemoryWorkerBody profile ready bindings callees older site incoming labels finish)
      (ComponentCall.hostWithComponent bindings callees) := by
  apply CallbackRange.linkedMemoryTransportBodyWith site linked family paired selected embedder
  · exact fun _ _ _ _ _ _ reached => alignPublicTransportWorker site reached run
  · exact fun _ _ _ _ _ _ _ checked canonical quiet reached => alignLocalPublicRefusal site checked canonical quiet reached run

theorem linkedFlatWorkerBody {type : Stored.TypeOf} (site : PayloadRoot.Site grow sig (.flat type))
    {callees : List (ComponentCall.Callee sig)}
    (linked : site.Linked bindings) (family : RecursiveCollectionType (sig.payload site.tag))
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : (ComponentCall.hostWithComponent bindings callees).embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) site.start labels finish) :
    PayloadRoot.Cut site profile ready bindings (LinkedFlatWorkerBody profile ready bindings callees older site incoming labels finish)
      (ComponentCall.hostWithComponent bindings callees) := by
  apply CallbackRange.linkedFlatTransportBodyWith site linked family paired selected embedder
  · exact fun _ _ _ _ _ _ _ reached => ⟨reached, alignPublicTransportWorker site reached run⟩
  · exact fun _ _ _ _ _ _ _ checked canonical quiet reached => alignLocalPublicRefusal site checked canonical quiet reached run

theorem actualSelectedGive {route : GiveEffectRoute} {request : CoreGiveRequest bindings start}
    (selection : request.Selected route) {callees : List (ComponentCall.Callee sig)} {label}
    {next : Config (core3 grow) (HostState sig)}
    (install : GiveInstall bindings (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start label next)
    (tail : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) next labels finish)
    (family : RecursiveGiveDomain selection) (paired : HostFrame.Related.Paired older start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle = some selection.tree) :
    ActualSelectedGive profile ready callees selection older incoming (label :: labels) finish := by
  have step : Step profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start label next := by
    cases install with
    | direct focused _ => exact .call focused
    | core focused calling _ => exact .coreCallout focused calling
  have run := Steps.cons step tail
  have entry := alignRecursiveEntry (reachedRecursiveGive selection family paired selected) run
  cases preflight : selection.preflight with
  | error issue => exact .compilerRefused preflight entry
  | ok result =>
    obtain ⟨field, plan⟩ := result
    obtain ⟨tag, payload, arity, children, root, linked⟩ := selection.compiler_success preflight
    have supported := family tag payload arity children field plan root preflight
    have liveRoot := selected.trans (congrArg some root)
    refine .compiled preflight root linked ?_ entry
    cases route with
    | memory pointer => exact linkedMemoryWorkerBody _ linked supported paired liveRoot rfl run
    | flat schema => exact linkedFlatWorkerBody _ linked supported paired liveRoot rfl run

open ReturnFrame.Occurrence in
theorem rejoinedTrackedWorker {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
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
        RejoinedWorkerTail profile ready bindings callees older checked canonical) := by
  obtain ⟨checkBody, canonBody, mark, leftMark, rightMark, _, reply⟩ :=
    CallbackRange.rebasePublicOccurrenceExit site checked canonical checkQuiet canonQuiet body
  refine ⟨checkBody, canonBody, mark, leftMark, rightMark, fun active => ?_⟩
  obtain ⟨checked, canonical, tracks, paired⟩ := reply active
  exact ⟨checked, canonical, requestWorkerTail tracks paired, rejoinedTail paired⟩

theorem requestWorkerTailAfterDelivery {callees : List (ComponentCall.Callee sig)}
    {request reference delivered queued : Config (core3 grow) (HostState sig)} {seen deliveryLabels workerLabels : Trace grow sig}
    {actions outgoing}
    (tail : RequestWorkerTail profile ready bindings callees older request reference seen start incoming)
    (delivery : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees) start incoming.host
      actions deliveryLabels delivered outgoing)
    (worker : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) delivered workerLabels queued) :
    ClassifiedWorkerTail profile ready bindings callees older start incoming (deliveryLabels ++ workerLabels) queued
      (fun added left right => RequestExitOccurrences profile ready (ComponentCall.hostWithComponent bindings callees)
        bindings request reference (seen ++ PayloadPrefix.visible added) left right) :=
  tail (append delivery.runs.1.steps worker)

theorem requestWorkerRefusalsAfterDelivery {callees : List (ComponentCall.Callee sig)}
    {request reference delivered finish : Config (core3 grow) (HostState sig)} {seen deliveryLabels workerLabels : Trace grow sig}
    {actions outgoing}
    (tail : RequestWorkerRefusals profile ready bindings callees older request reference seen start incoming)
    (delivery : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees) start incoming.host
      actions deliveryLabels delivered outgoing)
    (worker : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) delivered workerLabels finish) :
    WorkerRefusalRun profile ready bindings callees older request reference seen start incoming (deliveryLabels ++ workerLabels) finish :=
  tail (append delivery.runs.1.steps worker)

open ReturnFrame.Occurrence in
private theorem extendMark {callees : List (ComponentCall.Callee sig)}
    {checkEntry canonEntry : Config (core3 grow) (HostState sig)} {checkTrace canonTrace : Trace grow sig}
    {mark : Option Location} {added : Trace grow sig} {left right : Config (core3 grow) (HostState sig)}
    (tracked : AllocatorMark profile ready (ComponentCall.hostWithComponent bindings callees) bindings older
      checkEntry canonEntry checkTrace canonTrace start incoming mark)
    (trails : WorkerOccurrencePrefix profile ready bindings callees older start incoming mark added left right) :
    ∃ reached, AllocatorMark profile ready (ComponentCall.hostWithComponent bindings callees) bindings older checkEntry canonEntry
      (checkTrace ++ added) (canonTrace ++ added) left right reached := by
  obtain ⟨reached, checked, live, outside, movement⟩ := trails
  refine ⟨reached, outside, tracked.checkedTrail.append checked, tracked.canonicalTrail.append live, ?_⟩
  intro cursor
  obtain ⟨middle, checkFront, canonFront⟩ := tracked.movement cursor
  obtain ⟨target, checkTail, canonTail⟩ := movement middle
  exact ⟨target, checkFront.append checkTail, canonFront.append canonTail⟩

open ReturnFrame.Occurrence in
theorem classifyAllocatorTail {callees : List (ComponentCall.Callee sig)}
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
  mapWorkerTrack (classifyWithOccurrence run paired tracked.outside) (fun _ _ _ _ => extendMark tracked)

open ReturnFrame.Occurrence in
theorem alignAllocatorPop
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
      check first second value labels last := by
  by_cases top : mark = some (.active 0 0)
  · subst mark
    cases run with
    | refl => exact .inr (.inl ⟨rfl, rfl⟩)
    | @cons _ _ _ _ trailing head tail =>
      obtain ⟨canon, frame, checked, live, _, _, paths, canonAt⟩ := CallbackPrefix.pop marked paired returning installed
      obtain ⟨rfl, rfl⟩ := silentStepUnique checked head
      exact .inr (.inr ⟨trailing, canon, rfl, rfl, by simp, tail, live, frame, paths,
        fun transport => CallbackPrefix.transportAllocatorPop returning canonAt transport⟩)
  · exact .inl top

open ReturnFrame.Occurrence in
private theorem cursorAtInstalledReply {cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {resume : ReturnFrame.Continuation (core3 grow) (HostState sig)} {value : Ret (core3 grow)}
    (focused : start.ctl = cursor.control (.pure value))
    (installed : segmentAt (segmentStorage start) (.active 0 0) = some (.prog resume)) :
    ∃ after : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
      cursor = { after with frames := .prog resume :: after.frames } := by
  cases cursor with
  | mk thread frames rest =>
    cases frames with
    | nil => simp [segmentStorage, segmentAt, focused, PayloadPrefix.Cursor.control] at installed
    | cons frame frames =>
      have exactFrame : frame = .prog resume := by
        simpa [segmentStorage, segmentAt, focused, PayloadPrefix.Cursor.control] using installed
      subst frame
      exact ⟨⟨thread, frames, rest⟩, rfl⟩

open ReturnFrame.Occurrence in
private theorem compareComponentMarkedReply
    {reached peer : Config (core3 grow) (HostState sig)} {leading suffix : Trace grow sig}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (leftInstalled : segmentAt (segmentStorage start) (.active 0 0) = some (.prog first))
    (rightInstalled : segmentAt (segmentStorage incoming) (.active 0 0) = some (.prog second))
    (outside : Outside older (segmentStorage start) (segmentStorage incoming) (some (.active 0 0)))
    (moved : OccurrenceTransport profile ready base bindings start incoming leading leading reached peer)
    (residual : Steps profile ready (specDispatch ready base) reached suffix finish)
    (atReply : reached.ctl = check.control (.pure (.cancel .none)) →
      suffix = [] ∨ HostFrame.Related.Paired wider reached peer) :
    ComponentMarkedReplyTail profile ready base bindings older start incoming reached peer leading
      check first second suffix finish := by
  have paths := CallbackPrefix.transportPaths moved
  obtain ⟨move, trails, transported⟩ := moved
  let mark := move (some (.active 0 0))
  have tracked : AllocatorMark profile ready base bindings older start incoming leading leading reached peer mark :=
    ⟨outsideMarks_singleton.mp (transported older _ (outsideMarks_singleton.mpr outside)),
      (trails _).1, (trails _).2, paths⟩
  refine ⟨mark, tracked, ?_⟩
  intro atReturn
  by_cases top : mark = some (.active 0 0)
  · apply Or.inr
    have sameTop := top ▸ tracked.checkedTrail
    obtain ⟨place, placeEq, survived⟩ := sameTop.survives
    cases placeEq
    obtain ⟨after, replaced⟩ := cursorAtInstalledReply atReturn ((prefix_survives survived).2.trans leftInstalled)
    refine ⟨after, replaced, ?_⟩
    rcases atReply atReturn with rfl | atPeer
    · cases residual
      exact .inr (.inl ⟨rfl, rfl⟩)
    · exact alignAllocatorPop tracked atPeer (replaced ▸ atReturn) rightInstalled residual
  · exact .inl top

open ReturnFrame.Occurrence in
theorem cutAdmittedRefusalMarkedReply (callee : ComponentCall.Callee sig) (caller : CallerId) (issue : Scheduled.Issue)
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
    ComponentEarlyPrefix profile ready base bindings wider check canon start incoming labels finish (if record.index.isSome then 8 else 7) := by
  rcases cutAdmittedRefusalResult (bindings := bindings) callee caller issue record leftFocus rightFocus callerRecord live admitted paired run with
    ⟨leading, suffix, reached, peer, split, shorter, moved, residual, frontier⟩ | early
  · refine .inl ⟨leading, suffix, reached, peer, split, shorter, moved, residual, frontier,
      compareComponentMarkedReply leftInstalled rightInstalled outside moved residual (wider := wider) ?_⟩
    intro atReturn
    cases frontier with
    | returned _ left right aligned =>
      apply Or.inr
      unfold PairedComponentSite at aligned
      rw [← left, ← right] at aligned
      exact aligned
    | pending _ _ left _ _ _ =>
      rw [left] at atReturn
      simp [PayloadPrefix.Cursor.control] at atReturn
    | trapped left _ _ =>
      rw [left] at atReturn
      simp [PayloadPrefix.Cursor.control] at atReturn
  · exact .inr early

open ReturnFrame.Occurrence in
theorem cutSuccessfulMarkedReply (callee : ComponentCall.Callee sig) (caller : CallerId)
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
        check first second suffix finish := by
  have same := Stored.OwnedMemory.Claims.register_observations claims length
  rw [leftLive] at same
  cases rightLive : incoming.host.writer.register (.node callee.tag valid children) with
  | error issue => simp [rightLive, Except.map] at same
  | ok rightWriter =>
    have rightHandle : handle = rightWriter.accepted.length := by
      simpa [rightLive, Except.map, leftHandle] using same
    obtain ⟨leading, suffix, reached, peer, split, moved, residual, frontier⟩ :=
      cutSuccessfulPublication (bindings := bindings) callee caller argument payload children validated
        leftFocus rightFocus paired record resultType indirect leftLive rightLive leftHandle rightHandle room run
    refine ⟨leading, suffix, reached, peer, split, moved, residual, frontier,
      compareComponentMarkedReply leftInstalled rightInstalled outside moved residual (wider := wider) ?_⟩
    intro atReturn
    cases frontier with
    | pending _ exhausted => exact .inl exhausted
    | trapped checked _ _ =>
      rw [checked] at atReturn
      simp [PayloadPrefix.Cursor.control] at atReturn
    | published _ _ pair _ _ => exact .inr pair

private theorem lowerRecordOfShape {initial reached : CStore (core3 grow)} {caller : CallerId}
    {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)} {args : List FlatValue}
    {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat}
    (original : ArenaField.callers.get? initial caller = some (.lower subtask cx args pos ft limits results))
    (retained : LowerSt.callerShape reached caller = LowerSt.callerShape initial caller) :
    ∃ advanced, ArenaField.callers.get? reached caller = some (.lower subtask cx args advanced ft limits results) := by
  unfold LowerSt.callerShape CStore.caller? at retained
  rw [original] at retained
  cases live : ArenaField.callers.get? reached caller with
  | none => simp [live] at retained
  | some record =>
    rw [live] at retained
    cases record with
    | lower reachedSubtask reachedCx reachedArgs advanced reachedType reachedLimits reachedResults =>
      cases retained
      exact ⟨advanced, rfl⟩
    | host => cases retained
    | sub => cases retained

open AsyncRef ReturnFrame.Occurrence in
private theorem cutObservedRefusal (caller : CallerId) (issue : Scheduled.Issue)
    {leftTicket rightTicket : Nat} {subtask : SubtaskId} {cx : LiftLowerContext (core3 grow)}
    {args : List FlatValue} {pos : Nat} {ft : WIT.FuncType Empty RtId} {limits results : Nat}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (ComponentCall.resolveRefused leftTicket caller issue))
    (rightFocus : incoming.ctl = canon.control (ComponentCall.resolveRefused rightTicket caller issue))
    (record : ArenaField.callers.get? start.store caller = some (.lower subtask cx args pos ft limits results))
    (resultType : ft.result = some ComponentCall.resultType) (indirect : results ≤ 1)
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer, labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      (ComponentStoreFrontier (Result := Unit) older check canon (fun _ => .pure (.cancel .none))
        (fun _ => .pure (.cancel .none)) reached peer suffix True ∨
        (suffix = [] ∧ PairedComponentSite older reached peer check canon)) := by
  rcases cutComponentResolveRefused (bindings := bindings) caller issue leftFocus rightFocus record resultType indirect paired run with
    ⟨residualLabels, split, moved, aligned, residual⟩ | early
  · let body : Session grow sig Unit := do
      maybeOnProgress subtask
      let flat ← lowerFlatValues Limits.spec Quirks.none cx results [.variant 1 none]
        [ComponentCall.resultType] (some ⟨args, pos⟩)
      Subtask.resolve subtask .returned flat
    let tailProgram : Session grow sig (Ret (core3 grow)) := do
      maybeOnProgress subtask
      let flat ← lowerFlatValues Limits.spec Quirks.none cx results [.variant 1 none]
        [ComponentCall.resultType] (some ⟨args, pos⟩)
      Subtask.resolve subtask .returned flat
      return .cancel .none
    let reachedAt := fun (state : Config (core3 grow) (HostState sig))
        (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) ticket =>
      { state with host := state.host.record (.refused ticket issue), ctl := cursor.control tailProgram }
    have tailEq : tailProgram = body >>= fun _ => .pure (.cancel .none) := by
      simp only [tailProgram, body, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq]
    change HostFrame.Related.Paired older (reachedAt start check leftTicket) (reachedAt incoming canon rightTicket) at aligned
    have site : PairedComponentSite older (reachedAt start check leftTicket) (reachedAt incoming canon rightTicket) check canon := by
      obtain ⟨_, _, focus, normalized⟩ := aligned.retarget rfl (.prog (.pure (.cancel .none)))
        (start.host.record (.refused leftTicket issue)) (incoming.host.record (.refused rightTicket issue))
      simp only [reachedAt, PayloadPrefix.Cursor.control, List.cons.injEq, Activation.mk.injEq, true_and] at focus
      obtain ⟨⟨threadEq, framesEq⟩, restEq⟩ := focus
      simpa only [PairedComponentSite, reachedAt, PayloadPrefix.Cursor.control, ← threadEq, ← framesEq, ← restEq] using normalized
    change Steps profile ready (specDispatch ready base) (reachedAt start check leftTicket) residualLabels finish at residual
    obtain ⟨leading, suffix, reached, peer, tailSplit, finishMove, remaining, frontier, _, _⟩ :=
      cutComponentStoreBody (bindings := bindings) (closed := True) body _ _
        (fun _ => resultEffects subtask cx _ results indirect none)
        (congrArg check.control tailEq) (congrArg canon.control tailEq) site residual
    refine ⟨[.tau, .tau, .tau] ++ leading, suffix, reached, peer, ?_, ?_, remaining, .inl frontier⟩
    · rw [split, tailSplit, List.append_assoc]
    · simpa only [List.map_nil, List.append_nil] using (CallbackPrefix.transportAppend moved finishMove).choose_spec.1
  · obtain ⟨_, peer, moved, endpoint, _, _⟩ := early
    exact ⟨labels, [], finish, peer, (List.append_nil _).symm, moved, .refl _, .inr ⟨rfl, endpoint⟩⟩

private def rejectBody : Session grow sig Empty := trap (.hostTrap "invalid mixed acceptor import binding")

private def rejectAt (state : Config (core3 grow) (HostState sig))
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (ticket : Nat) (issue : Scheduled.Issue) :
    Config (core3 grow) (HostState sig) :=
  { state with
    host := state.host.record (.bindingTrap ticket issue)
    ctl := cursor.control (rejectBody >>= fun _ => .pure (.cancel .none)) }

open ReturnFrame.Occurrence in
private theorem rejectPath (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (ticket : Nat) (issue : Scheduled.Issue) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (ComponentCall.reject ticket issue)) :
    ComponentQuietPath profile ready dispatch cursor start [id, id] (rejectAt start cursor ticket issue) := by
  cases cursor with
  | mk thread frames rest =>
    let tail : Session grow sig (Ret (core3 grow)) := do
      let _ ← (trap (.hostTrap "invalid mixed acceptor import binding") : Session grow sig (List FlatValue))
      return .cancel .none
    have sameTrap : tail = rejectBody >>= fun _ => .pure (.cancel .none) := by
      simp only [tail, rejectBody, trap, Prog.bind_eq]
      apply congrArg (Prog.op (S := Eff (core3 grow) (HostState sig)) (.trap (.hostTrap "invalid mixed acceptor import binding")))
      funext denied
      exact nomatch denied
    refine .step (.hostGet focused) (by rw [transitionEdit, focused]; rfl) ?_
    let writing : Session grow sig (Ret (core3 grow)) := hostSet (start.host.record (.bindingTrap ticket issue)) >>= fun _ => tail
    have journal := Step.hostSet (prof := profile) (hr := ready) (dispatch := dispatch)
      (m := { start with ctl := ⟨thread, .prog writing, frames⟩ :: rest }) rfl
    change Step profile ready dispatch { start with ctl := ⟨thread, .prog writing, frames⟩ :: rest } .tau
      { start with host := start.host.record (.bindingTrap ticket issue), ctl := ⟨thread, .prog tail, frames⟩ :: rest } at journal
    have recorded : Step profile ready dispatch { start with ctl := ⟨thread, .prog writing, frames⟩ :: rest } .tau
        (rejectAt start ⟨thread, frames, rest⟩ ticket issue) := by
      rw [sameTrap] at journal
      exact journal
    exact .step recorded rfl (.done _)

open ReturnFrame.Occurrence in
private theorem cutObservedReject (issue : Scheduled.Issue) {leftTicket rightTicket : Nat}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (ComponentCall.reject leftTicket issue))
    (rightFocus : incoming.ctl = canon.control (ComponentCall.reject rightTicket issue))
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer, labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ((suffix = [] ∧ PairedComponentSite older reached peer check canon) ∨
        (reached.ctl = [] ∧ peer.ctl = [] ∧ HostFrame.Related.Paired older reached peer)) := by
  have left := rejectPath (profile := profile) (ready := ready) (specDispatch ready base) leftTicket issue check leftFocus
  have right := rejectPath (profile := profile) (ready := ready) (specDispatch ready (LiveDispatch.host bindings base))
    rightTicket issue canon rightFocus
  rcases splitSilent (count := 2) (left.track (.active 0 0)).toTrail.steps run with ⟨tailLabels, split, residual⟩ | short
  · have site : PairedComponentSite older (rejectAt start check leftTicket issue) (rejectAt incoming canon rightTicket issue) check canon := by
      unfold PairedComponentSite at paired ⊢
      obtain ⟨_, _, focus, normalized⟩ := paired.retarget rfl (.prog (.pure (.cancel .none)))
        (start.host.record (.bindingTrap leftTicket issue)) (incoming.host.record (.bindingTrap rightTicket issue))
      simp only [PayloadPrefix.Cursor.control, List.cons.injEq, Activation.mk.injEq, true_and] at focus
      obtain ⟨⟨threadEq, framesEq⟩, restEq⟩ := focus
      simpa only [rejectAt, PayloadPrefix.Cursor.control, ← threadEq, ← framesEq, ← restEq] using normalized
    have moved : OccurrenceTransport profile ready base bindings start incoming (List.replicate 2 .tau) (List.replicate 2 .tau)
        (rejectAt start check leftTicket issue) (rejectAt incoming canon rightTicket issue) :=
      CallbackPrefix.stationaryTransport (bindings := bindings) left.track right.track
    obtain ⟨leading, suffix, reached, peer, tailSplit, finishMove, remaining, frontier, _, _⟩ :=
      cutComponentStoreBody (bindings := bindings) (closed := True) rejectBody (fun _ => .pure (.cancel .none)) (fun _ => .pure (.cancel .none))
        (fun _ => storeEffectTrap _) rfl rfl site residual
    refine ⟨List.replicate 2 .tau ++ leading, suffix, reached, peer, ?_, ?_, remaining, ?_⟩
    · rw [split, tailSplit, List.append_assoc]
    · simpa only [List.map_nil, List.append_nil] using (CallbackPrefix.transportAppend moved finishMove).choose_spec.1
    · cases frontier with
      | returned impossible _ _ _ => exact nomatch impossible
      | pending _ _ _ _ atSite boundary => exact .inl ⟨boundary.resolve_right (fun openFrontier => openFrontier.1 trivial), atSite⟩
      | trapped checked canonical aligned => exact .inr ⟨checked, canonical, aligned⟩
  · obtain ⟨_, peer, moved, endpoint, _, _⟩ := compareQuietShort left right paired ⟨_, leftFocus⟩ ⟨_, rightFocus⟩ run short
    exact ⟨labels, [], finish, peer, (List.append_nil _).symm, moved, .refl _, .inl ⟨rfl, endpoint⟩⟩

private theorem rejectPayloadShape (callee : ComponentCall.Callee sig) (caller : CallerId) (ticket : Nat)
    {planned : Option (List (Stored.OwnedMemory.Tree sig))} {values : List Stored.OwnedMemory.Observed}
    (wrong : ¬ ∃ argument payload children, values = [argument, payload] ∧ planned = some children) :
    ComponentCall.acceptPayload (grow := grow) callee caller ticket planned values = ComponentCall.reject ticket .wrongType := by
  rcases values with _ | ⟨argument, _ | ⟨payload, _ | ⟨extra, rest⟩⟩⟩
  · rfl
  · rfl
  · cases planned with
    | none => rfl
    | some children => exact (wrong ⟨argument, payload, children, rfl, rfl⟩).elim
  · rfl

private theorem registrationProgram (ticket : Nat) (caller : CallerId) (tree : Stored.OwnedMemory.Tree sig) :
    ComponentCall.resolveTree (grow := grow) ticket caller tree =
      .op .hostGet (fun state => componentRegistrationProgram ticket caller tree (componentRegistration state.writer tree)) := by
  apply congrArg (Prog.op (S := Eff (core3 grow) (HostState sig)) .hostGet)
  funext state
  cases registered : state.writer.register tree with
  | error issue =>
    simp only [Prog.bind, registered, componentRegistration, componentRegistrationProgram]
  | ok writer =>
    by_cases full : writer.accepted.length ≥ 2 ^ 32
    · simp only [Prog.bind, registered, componentRegistration, componentRegistrationProgram, full, ite_true]
    · simp only [Prog.bind, registered, componentRegistration, componentRegistrationProgram, full, ite_false]

private theorem registeredHandle (writer : Stored.OwnedMemory.Claims.State sig) (tree : Stored.OwnedMemory.Tree sig)
    {handle : Nat} (fresh : componentRegistration writer tree = .fresh handle) :
    ∃ registered, writer.register tree = .ok registered ∧ handle = registered.accepted.length ∧ handle < 2 ^ 32 := by
  cases registered : writer.register tree with
  | error issue => simp [componentRegistration, registered] at fresh
  | ok updated =>
    by_cases full : updated.accepted.length ≥ 2 ^ 32
    · simp only [componentRegistration, registered, full, ite_true, reduceCtorEq] at fresh
    · simp only [componentRegistration, registered, full, ite_false, ComponentRegistration.fresh.injEq] at fresh
      exact ⟨updated, rfl, fresh.symm, fresh ▸ Nat.lt_of_not_ge full⟩

open ReturnFrame.Occurrence in
private theorem cutRegistrationProbe (caller : CallerId) (tree : Stored.OwnedMemory.Tree sig) {leftTicket rightTicket : Nat}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (ComponentCall.resolveTree leftTicket caller tree))
    (rightFocus : incoming.ctl = canon.control (ComponentCall.resolveTree rightTicket caller tree))
    (site : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    let atProbe := fun (state : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) ticket =>
      { state with ctl := cursor.control (componentRegistrationProgram ticket caller tree (componentRegistration state.host.writer tree)) }
    (labels = [] ∧ finish = start) ∨ ∃ suffix, labels = .tau :: suffix ∧
      OccurrenceTransport profile ready base bindings start incoming [.tau] [.tau]
        (atProbe start check leftTicket) (atProbe incoming canon rightTicket) ∧
      PairedComponentSite older (atProbe start check leftTicket) (atProbe incoming canon rightTicket) check canon ∧
      Steps profile ready (specDispatch ready base) (atProbe start check leftTicket) suffix finish := by
  dsimp only
  rw [registrationProgram] at leftFocus rightFocus
  cases run with
  | refl => exact .inl ⟨rfl, rfl⟩
  | cons actual tail =>
    have left := Step.hostGet (prof := profile) (hr := ready) (dispatch := specDispatch ready base) leftFocus
    have right := Step.hostGet (prof := profile) (hr := ready) (dispatch := specDispatch ready (LiveDispatch.host bindings base)) rightFocus
    obtain ⟨rfl, rfl⟩ := silentStepUnique left actual
    refine .inr ⟨_, rfl, CallbackPrefix.stationaryTransport (fun place => .step left ?_ (.done _ _))
      (fun place => .step right ?_ (.done _ _)), site, tail⟩
    · rw [transitionEdit, leftFocus]
      cases place <;> rfl
    · rw [transitionEdit, rightFocus]
      cases place <;> rfl

open ReturnFrame.Occurrence in
theorem cutObservedAcceptance (callee : ComponentCall.Callee sig) (caller : CallerId)
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
        planned check canon first second start incoming reached peer leading suffix finish := by
  classical
  let Outcome : Prop := ∃ leading suffix reached peer, labels = leading ++ suffix ∧
    OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
    Steps profile ready (specDispatch ready base) reached suffix finish ∧
    ComponentObservedAcceptance profile ready base bindings older wider callee caller leftTicket rightTicket
      planned check canon first second start incoming reached peer leading suffix finish
  change Outcome
  have guards := admittedRefusalGuards callee admitted
  have refuse {used rest : Trace grow sig} {leftAt rightAt : Config (core3 grow) (HostState sig)} {issue cursor}
      (split : labels = used ++ rest)
      (moved : OccurrenceTransport profile ready base bindings start incoming used used leftAt rightAt)
      (residual : Steps profile ready (specDispatch ready base) leftAt rest finish)
      (site : PairedComponentSite wider leftAt rightAt check canon)
      (liveRecord : ArenaField.callers.get? leftAt.store caller = some (.lower subtask cx args cursor ft limits results))
      (left : leftAt.ctl = check.control (ComponentCall.resolveRefused leftTicket caller issue))
      (right : rightAt.ctl = canon.control (ComponentCall.resolveRefused rightTicket caller issue)) : Outcome := by
    obtain ⟨more, finalSuffix, lhs, rhs, refusalSplit, refusalPath, finalRun, refused⟩ :=
      cutObservedRefusal (bindings := bindings) caller _ left right liveRecord guards.1 guards.2 site residual
    have whole : OccurrenceTransport profile ready base bindings start incoming (used ++ more) (used ++ more) lhs rhs := by
      simpa only [List.map_nil, List.append_nil] using (CallbackPrefix.transportAppend moved refusalPath).choose_spec.1
    refine ⟨used ++ more, finalSuffix, lhs, rhs, ?_, whole, finalRun, ?_⟩
    · rw [split, refusalSplit, List.append_assoc]
    · rcases refused with frontier | ⟨exhausted, aligned⟩
      · refine .refused frontier (compareComponentMarkedReply leftInstalled rightInstalled outside whole finalRun (wider := wider) ?_)
        intro atReturn
        cases frontier with
        | returned _ checked canonical paired =>
          unfold PairedComponentSite at paired
          rw [← checked, ← canonical] at paired
          exact .inr paired
        | pending _ _ checked _ _ _ =>
          rw [checked] at atReturn
          simp [PayloadPrefix.Cursor.control] at atReturn
        | trapped checked _ _ =>
          rw [checked] at atReturn
          simp [PayloadPrefix.Cursor.control] at atReturn
      · exact .pending exhausted aligned
  have reject {used rest : Trace grow sig} {leftAt rightAt : Config (core3 grow) (HostState sig)} {issue}
      (split : labels = used ++ rest)
      (moved : OccurrenceTransport profile ready base bindings start incoming used used leftAt rightAt)
      (residual : Steps profile ready (specDispatch ready base) leftAt rest finish)
      (site : PairedComponentSite wider leftAt rightAt check canon)
      (left : leftAt.ctl = check.control (ComponentCall.reject leftTicket issue))
      (right : rightAt.ctl = canon.control (ComponentCall.reject rightTicket issue)) : Outcome := by
    obtain ⟨more, finalSuffix, lhs, rhs, rejectSplit, rejectPath, finalRun, rejected⟩ :=
      cutObservedReject (bindings := bindings) _ left right site residual
    have whole : OccurrenceTransport profile ready base bindings start incoming (used ++ more) (used ++ more) lhs rhs := by
      simpa only [List.map_nil, List.append_nil] using (CallbackPrefix.transportAppend moved rejectPath).choose_spec.1
    refine ⟨used ++ more, finalSuffix, lhs, rhs, ?_, whole, finalRun, ?_⟩
    · rw [split, rejectSplit, List.append_assoc]
    · rcases rejected with ⟨exhausted, aligned⟩ | ⟨checked, canonical, aligned⟩
      · exact .pending exhausted aligned
      · exact .trapped checked canonical aligned
  obtain ⟨leading, suffix, reached, peer, split, moved, residual, frontier, _, _, retained⟩ :=
    cutObservedArguments (bindings := bindings) callee caller leftFocus rightFocus paired run
  cases frontier with
  | pending _ _ _ _ site boundary => exact ⟨leading, suffix, reached, peer, split, moved, residual,
      .pending (boundary.resolve_right (fun openFrontier => openFrontier.1 trivial)) site⟩
  | trapped left right site => exact ⟨leading, suffix, reached, peer, split, moved, residual, .trapped left right site⟩
  | returned values left right site =>
    have shape := (retained (by rw [left]; simp [PayloadPrefix.Cursor.control])).1 caller
    obtain ⟨_, liveRecord⟩ := lowerRecordOfShape original shape
    by_cases shaped : ∃ argument payload children, values = [argument, payload] ∧ planned = some children
    · obtain ⟨argument, payload, children, rfl, rfl⟩ := shaped
      cases validated : Stored.OwnedMemory.checkValue (sig.payload callee.tag) payload with
      | error issue =>
        exact refuse split moved residual site liveRecord
          (by simpa only [ComponentCall.acceptPayload, validated] using left)
          (by simpa only [ComponentCall.acceptPayload, validated] using right)
      | ok valid =>
        let tree : Stored.OwnedMemory.Tree sig := .node callee.tag valid children
        by_cases bothFresh : ∃ handle, componentRegistration reached.host.writer tree = .fresh handle ∧
            componentRegistration peer.host.writer tree = .fresh handle
        · obtain ⟨handle, leftFresh, rightFresh⟩ := bothFresh
          obtain ⟨_, leftRegistered, leftHandle, room⟩ := registeredHandle _ _ leftFresh
          obtain ⟨_, rightRegistered, rightHandle, _⟩ := registeredHandle _ _ rightFresh
          obtain ⟨more, finalSuffix, lhs, rhs, acceptanceSplit, acceptancePath, finalRun, accepted⟩ :=
            cutSuccessfulPublication (bindings := bindings) callee caller argument payload children validated
              left right site liveRecord guards.1 guards.2 leftRegistered rightRegistered leftHandle rightHandle room residual
          have whole : OccurrenceTransport profile ready base bindings start incoming (leading ++ more) (leading ++ more) lhs rhs := by
            simpa only [List.map_nil, List.append_nil] using (CallbackPrefix.transportAppend moved acceptancePath).choose_spec.1
          refine ⟨leading ++ more, finalSuffix, lhs, rhs, ?_, whole, finalRun, .accepted accepted
            (compareComponentMarkedReply leftInstalled rightInstalled outside whole finalRun (wider := wider) ?_)⟩
          · rw [split, acceptanceSplit, List.append_assoc]
          · intro atReturn
            cases accepted with
            | pending _ exhausted => exact .inl exhausted
            | trapped checked _ _ =>
              rw [checked] at atReturn
              simp [PayloadPrefix.Cursor.control] at atReturn
            | published _ _ pair _ _ => exact .inr pair
        · have leftProbe : reached.ctl = check.control (ComponentCall.resolveTree leftTicket caller tree) := by
            simpa only [ComponentCall.acceptPayload, validated, tree] using left
          have rightProbe : peer.ctl = canon.control (ComponentCall.resolveTree rightTicket caller tree) := by
            simpa only [ComponentCall.acceptPayload, validated, tree] using right
          rcases cutRegistrationProbe (bindings := bindings) caller tree leftProbe rightProbe site residual with
            ⟨empty, _⟩ | ⟨remaining, used, probed, atProbe, afterProbe⟩
          · exact ⟨leading, suffix, reached, peer, split, moved, residual, .pending empty site⟩
          · let lhs := { reached with ctl := check.control (componentRegistrationProgram leftTicket caller tree
                (componentRegistration reached.host.writer tree)) }
            let rhs := { peer with ctl := canon.control (componentRegistrationProgram rightTicket caller tree
                (componentRegistration peer.host.writer tree)) }
            have whole : OccurrenceTransport profile ready base bindings start incoming (leading ++ [.tau]) (leading ++ [.tau]) lhs rhs := by
              simpa only [List.map_nil, List.append_nil] using (CallbackPrefix.transportAppend moved probed).choose_spec.1
            have actual : labels = (leading ++ [.tau]) ++ remaining := by
              rw [split, used, List.append_assoc]
              rfl
            have leftProgram : lhs.ctl = check.control (componentRegistrationProgram leftTicket caller tree
                (componentRegistration reached.host.writer tree)) := rfl
            have rightProgram : rhs.ctl = canon.control (componentRegistrationProgram rightTicket caller tree
                (componentRegistration peer.host.writer tree)) := rfl
            by_cases agrees : componentRegistration reached.host.writer tree = componentRegistration peer.host.writer tree
            · rw [← agrees] at rightProgram
              cases branch : componentRegistration reached.host.writer tree with
              | aliased =>
                exact refuse actual whole afterProbe atProbe liveRecord
                  (by simpa only [branch, componentRegistrationProgram] using leftProgram)
                  (by simpa only [branch, componentRegistrationProgram] using rightProgram)
              | exhausted =>
                exact reject actual whole afterProbe atProbe
                  (by simpa only [branch, componentRegistrationProgram] using leftProgram)
                  (by simpa only [branch, componentRegistrationProgram] using rightProgram)
              | fresh handle => exact (bothFresh ⟨handle, branch, agrees.symm.trans branch⟩).elim
            · exact ⟨leading ++ [.tau], remaining, lhs, rhs, actual, whole, afterProbe,
                .registrationMismatch leftProgram rightProgram atProbe agrees⟩
    · rw [rejectPayloadShape callee caller leftTicket shaped] at left
      rw [rejectPayloadShape callee caller rightTicket shaped] at right
      exact reject split moved residual site left right

open ReturnFrame.Occurrence in
private theorem cutProgramCallInstall {call : Call (core3 grow)} {thread frames rest resume label next}
    (commonFocus : Focus (core3 grow) (HostState sig))
    (focused : start.ctl = ⟨thread, .prog (.op (.call call) resume), frames⟩ :: rest)
    (taken : Step profile ready (specDispatch ready base) start label next)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ peerFrames peerRest,
      let reached := { start with ctl := ⟨thread, .prog (specDispatch ready base call), .prog resume :: frames⟩ :: rest }
      let peer := { incoming with ctl := ⟨thread, .prog (specDispatch ready (LiveDispatch.host bindings base) call),
        .prog resume :: peerFrames⟩ :: peerRest }
      label = .tau ∧ next = reached ∧ HostFrame.Related.Paired older
        { reached with ctl := ⟨thread, commonFocus, .prog resume :: frames⟩ :: rest }
        { peer with ctl := ⟨thread, commonFocus, .prog resume :: peerFrames⟩ :: peerRest } ∧
      OccurrenceTransport profile ready base bindings start incoming [.tau] [.tau] reached peer [some (.active 0 0)] ∧
      segmentAt (segmentStorage reached) (.active 0 0) = some (.prog resume) ∧
      segmentAt (segmentStorage peer) (.active 0 0) = some (.prog resume) ∧
      Outside older (segmentStorage reached) (segmentStorage peer) (some (.active 0 0)) := by
  obtain ⟨peerFrames, peerRest, peerFocus, entered⟩ := ReturnFrame.Related.Paired.push_shared paired focused commonFocus (.prog resume)
  let checked := Step.call (prof := profile) (hr := ready) (dispatch := specDispatch ready base) focused
  let canonical := Step.call (prof := profile) (hr := ready) (dispatch := specDispatch ready (LiveDispatch.host bindings base)) peerFocus
  have leftEdit : transitionEdit start .tau = .push (.prog resume) := by rw [transitionEdit, focused]
  have rightEdit : transitionEdit incoming .tau = .push (.prog resume) := by rw [transitionEdit, peerFocus]
  have shifted (place : Option Location) : place.bind (Edit.push (.prog resume)).follow = place.map Location.pushed := by
    cases place with
    | none => rfl
    | some place =>
      cases place with
      | active activation _ => cases activation <;> rfl
      | saved => rfl
  obtain ⟨labelEq, nextEq⟩ := silentStepUnique checked taken
  refine ⟨peerFrames, peerRest, labelEq, nextEq.symm, entered, ⟨(·.map Location.pushed), ?_, ?_⟩, rfl, rfl, ?_⟩
  · intro place
    exact ⟨.step checked (by rw [leftEdit, shifted]; exact .done _ _), .step canonical (by rw [rightEdit, shifted]; exact .done _ _)⟩
  · intro previous marks outside
    rw [step_edit checked, step_edit canonical, leftEdit, rightEdit]
    exact outside.push _ _
  · rw [step_edit checked, step_edit canonical, leftEdit, rightEdit]
    exact outside_push _ _ (paired_outside (left := HostFrame.replace start incoming.host) paired)

open ReturnFrame.Occurrence in
private theorem cutSharedComponentInstall {callees : List (ComponentCall.Callee sig)}
    {hostId : HostFuncId} {caller : CallerId} {call : Session grow sig (Ret (core3 grow))} {thread frames rest resume label next}
    (resolved : specDispatch ready (ComponentCall.hostWithComponent bindings callees) (.hostFunc hostId caller) = call)
    (focused : start.ctl = ⟨thread, .prog (.op (.call (.hostFunc hostId caller)) resume), frames⟩ :: rest)
    (taken : Step profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start label next)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ peerFrames peerRest,
      let reached := { start with ctl := ⟨thread, .prog call, .prog resume :: frames⟩ :: rest }
      let peer := { incoming with ctl := ⟨thread, .prog call, .prog resume :: peerFrames⟩ :: peerRest }
      label = .tau ∧ next = reached ∧ HostFrame.Related.Paired older reached peer ∧
      OccurrenceTransport profile ready (ComponentCall.hostWithComponent bindings callees) bindings
        start incoming [.tau] [.tau] reached peer [some (.active 0 0)] ∧
      segmentAt (segmentStorage reached) (.active 0 0) = some (.prog resume) ∧
      segmentAt (segmentStorage peer) (.active 0 0) = some (.prog resume) ∧
      Outside older (segmentStorage reached) (segmentStorage peer) (some (.active 0 0)) := by
  have peerResolved : specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees))
      (.hostFunc hostId caller) = call := resolved
  simpa only [resolved, peerResolved] using cutProgramCallInstall (bindings := bindings) (.prog call) focused taken paired

open ReturnFrame.Occurrence in
theorem cutLinkedComponentInstall {callees : List (ComponentCall.Callee sig)}
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
      Outside older (segmentStorage reached) (segmentStorage peer) (some (.active 0 0)) := by
  refine cutSharedComponentInstall ?_ focused taken paired
  simp only [dispatch, ComponentCall.hostWithComponent, linked]

open ReturnFrame.Occurrence in
theorem cutAdmittedComponent (callee : ComponentCall.Callee sig) (caller : CallerId)
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
      ⟨some active, frames, rest⟩ first second start incoming labels finish := by
  classical
  unfold ComponentAdmissionCut
  rcases cutComponentPreflight (bindings := bindings) callee caller focused record liveThread liveTask context admitted run paired with
    ⟨peerFrames, peerRest, suffix, peerFocus, split, moved, site, residual⟩ | early
  · let check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨some active, frames, rest⟩
    let canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨some active, peerFrames, peerRest⟩
    let reached := componentPreflightAt callee caller cx args start check
    let peer := componentPreflightAt callee caller cx args incoming canon
    let leftPlan := callee.childPreflight start.host.writer.accepted start.store cx args
    let rightPlan := callee.childPreflight incoming.host.writer.accepted incoming.store cx args
    refine .inr ⟨peerFrames, peerRest, suffix, split, moved, residual, site, ?_⟩
    change leftPlan ≠ rightPlan ∨ _
    by_cases agrees : leftPlan = rightPlan
    · have leftStorage : segmentStorage reached = segmentStorage start := by
        simp only [reached, componentPreflightAt, segmentStorage, focused, check, PayloadPrefix.Cursor.control]
        rfl
      have rightStorage : segmentStorage peer = segmentStorage incoming := by
        simp only [peer, componentPreflightAt, segmentStorage, peerFocus, PayloadPrefix.Cursor.control]
        rfl
      have atLeft : reached.ctl = check.control (ComponentCall.acceptPlanned callee caller start.host.nextTicket leftPlan) := rfl
      have atRight : peer.ctl = canon.control (ComponentCall.acceptPlanned callee caller incoming.host.nextTicket leftPlan) := by
        rw [agrees]
        rfl
      have leftMark : segmentAt (segmentStorage reached) (.active 0 0) = some (.prog first) := by
        rw [leftStorage, leftInstalled]
      have rightMark : segmentAt (segmentStorage peer) (.active 0 0) = some (.prog second) := by
        rw [rightStorage, rightInstalled]
      have exterior : Outside older (segmentStorage reached) (segmentStorage peer) (some (.active 0 0)) := by
        rwa [leftStorage, rightStorage]
      refine .inr ⟨leftPlan, rfl, agrees.symm, ?_⟩
      cases branch : leftPlan with
      | ok planned =>
        simp only [branch] at atLeft atRight
        exact cutObservedAcceptance callee caller atLeft atRight site record admitted leftMark rightMark exterior residual
      | error issue =>
        simp only [branch] at atLeft atRight
        cases live : start.store.subtask? subtask with
        | none =>
          simp [ComponentCall.Callee.check, live, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at admitted
          split_ifs at admitted
        | some subtaskEntry =>
          rcases cutAdmittedRefusalMarkedReply (bindings := bindings) callee caller issue subtaskEntry atLeft atRight
              record live admitted site leftMark rightMark exterior residual with
            ⟨leading, trailing, lhs, rhs, refusalSplit, _, refusalPath, refusalRun, frontier, reply⟩ | shortRefusal
          · exact .inr ⟨leading, trailing, lhs, rhs, refusalSplit, refusalPath, refusalRun, frontier, reply⟩
          · have unindexed : subtaskEntry.index = none := by
              by_contra different
              have indexed : subtaskEntry.index.isSome = true := Option.isSome_iff_ne_none.mpr different
              simp [ComponentCall.Callee.check, live, indexed, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at admitted
              split_ifs at admitted
            exact .inl (by simpa only [unindexed, Option.isSome, Bool.false_eq_true, ite_false] using shortRefusal)
    · exact .inl agrees
  · exact .inl early

theorem classifyLinkedComponentAdmission {callees : List (ComponentCall.Callee sig)}
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
        ⟨some active, .prog resume :: frames, rest⟩ resume resume next peer labels finish := by
  obtain ⟨peerFrames, peerRest, silent, rfl, aligned, install, leftMark, rightMark, outside⟩ :=
    cutLinkedComponentInstall linked focused taken paired
  exact ⟨peerFrames, peerRest, silent, install,
    cutAdmittedComponent callee caller rfl record liveThread liveTask context admitted aligned leftMark rightMark outside run⟩

open ReturnFrame.Occurrence in
private theorem sharedTopTransport {left right : Config (core3 grow) (HostState sig)} {checkedTrace canonTrace : Trace grow sig}
    {frame : Seg (core3 grow) (HostState sig)}
    (installed : OccurrenceTransport profile ready base bindings start incoming checkedTrace canonTrace left right [some (.active 0 0)])
    (checked : segmentAt (segmentStorage left) (.active 0 0) = some frame)
    (canonical : segmentAt (segmentStorage right) (.active 0 0) = some frame) :
    OccurrenceTransport profile ready base bindings start incoming checkedTrace canonTrace left right := by
  obtain ⟨move, paths, retained⟩ := installed
  refine ⟨move, paths, ?_⟩
  intro older marks outside place off first second leftAt rightAt
  by_cases top : place = .active 0 0
  · subst place
    obtain rfl := Option.some.inj (leftAt.symm.trans checked)
    obtain rfl := Option.some.inj (rightAt.symm.trans canonical)
    exact .same _
  · exact retained older marks outside place (fun member => by
      rcases List.mem_cons.mp member with equal | member
      · exact top (Option.some.inj equal)
      · exact off member) first second leftAt rightAt

private def badComponentLinkProgram (issue : Scheduled.Issue) : Session grow sig (Ret (core3 grow)) := do
  let state ← hostGet
  hostSet (state.enter "component accept" ⟨[], []⟩ [])
  ComponentCall.reject state.nextTicket issue

private def badLinkEntry (state : Config (core3 grow) (HostState sig))
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (issue : Scheduled.Issue) :
    Config (core3 grow) (HostState sig) :=
  { state with
    host := state.host.enter "component accept" ⟨[], []⟩ []
    ctl := cursor.control (ComponentCall.reject state.host.nextTicket issue) }

open ReturnFrame.Occurrence in
private theorem badLinkEntryPath (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (issue : Scheduled.Issue) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (badComponentLinkProgram issue)) :
    ComponentQuietPath profile ready dispatch cursor start [id, id] (badLinkEntry start cursor issue) := by
  cases cursor
  refine .step (.hostGet focused) (by rw [transitionEdit, focused]; rfl) ?_
  exact .step (.hostSet rfl) rfl (.done _)

open ReturnFrame.Occurrence in
private theorem cutComponentBadLink {callees : List (ComponentCall.Callee sig)}
    {hostId : HostFuncId} {caller : CallerId} {thread frames rest resume label next}
    (bad : ¬ ∃ callee, callees.filter (·.hostId == hostId) = [callee])
    (focused : start.ctl = ⟨thread, .prog (.op (.call (.hostFunc hostId caller)) resume), frames⟩ :: rest)
    (step : Step profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start label next)
    (tail : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) next labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ComponentEntryFailure profile ready bindings callees older start incoming finish label labels := by
  let base := ComponentCall.hostWithComponent (grow := grow) bindings callees
  let issue : Scheduled.Issue := if (callees.filter (·.hostId == hostId)).isEmpty then .unlinkedImport else .ambiguousBinding
  have resolved : specDispatch ready base (.hostFunc hostId caller) = badComponentLinkProgram issue := by
    cases linked : callees.filter (·.hostId == hostId) with
    | nil => simp only [dispatch, base, ComponentCall.hostWithComponent, issue, linked, badComponentLinkProgram]
    | cons first others =>
      cases others with
      | nil => exact (bad ⟨first, linked⟩).elim
      | cons second remaining => simp only [dispatch, base, ComponentCall.hostWithComponent, issue, linked, badComponentLinkProgram]
  obtain ⟨peerFrames, peerRest, rfl, rfl, entered, marked, leftMark, rightMark, _⟩ :=
    cutSharedComponentInstall resolved focused step paired
  let check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨thread, .prog resume :: frames, rest⟩
  let canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨thread, .prog resume :: peerFrames, peerRest⟩
  let left := { start with ctl := check.control (badComponentLinkProgram issue) }
  let right := { incoming with ctl := canon.control (badComponentLinkProgram issue) }
  have installed := sharedTopTransport marked leftMark rightMark
  have entry := badLinkEntryPath (start := left) (profile := profile) (ready := ready) (specDispatch ready base) issue check rfl
  have canonEntry := badLinkEntryPath (start := right) (profile := profile) (ready := ready)
    (specDispatch ready (LiveDispatch.host bindings base)) issue canon rfl
  have site (leftHost rightHost : HostState sig) : PairedComponentSite older { left with host := leftHost }
      { right with host := rightHost } check canon := by
    obtain ⟨_, _, focus, retargeted⟩ := HostFrame.Related.Paired.retarget (left := left) (right := right) entered
      rfl (.prog (.pure (.cancel .none))) leftHost rightHost
    simp only [right, check, canon, PayloadPrefix.Cursor.control, List.cons.injEq, Activation.mk.injEq, true_and] at focus
    obtain ⟨rfl, rfl⟩ := focus
    exact retargeted
  rcases splitSilent (count := 2) (entry.track (.active 0 0)).toTrail.steps tail with ⟨remaining, split, residual⟩ | short
  · obtain ⟨leading, suffix, reached, peer, bodySplit, moved, after, outcome⟩ := cutObservedReject (bindings := bindings)
      (leftTicket := left.host.nextTicket) (rightTicket := right.host.nextTicket)
      issue (start := badLinkEntry left check issue) (incoming := badLinkEntry right canon issue)
      rfl rfl (site _ _) residual
    have intoReject := CallbackPrefix.stationaryTransport (bindings := bindings) entry.track canonEntry.track
    have crossed := (CallbackPrefix.transportAppend intoReject moved).choose_spec.1
    refine ⟨([.tau, .tau] : Trace grow sig) ++ leading, suffix, reached, peer, check, canon, rfl, ?_, ?_, after, outcome⟩
    · rw [split, bodySplit, List.append_assoc]
      rfl
    · simpa only [List.map_nil, List.append_nil, List.singleton_append, List.length_cons, List.length_nil,
        List.replicate_succ, List.replicate_zero] using (CallbackPrefix.transportAppend installed crossed).choose_spec.1
  · obtain ⟨_, peer, moved, endpoint, _, _⟩ := compareQuietShort (bindings := bindings) entry canonEntry (site left.host right.host)
      ⟨_, rfl⟩ ⟨_, rfl⟩ tail short
    exact ⟨labels, [], finish, peer, check, canon, rfl, (List.append_nil _).symm,
      (CallbackPrefix.transportAppend installed moved).choose_spec.1, .refl _, .inl ⟨rfl, endpoint⟩⟩

private theorem internalBind {Input Output : Type} (message : String) (next : Input → Session grow sig Output) :
    (internal message : Session grow sig Input).bind next = internal message := by
  simp only [internal, trap]
  apply congrArg (Prog.op (S := Eff (core3 grow) (HostState sig)) (.trap (.internal message)))
  funext impossible
  exact nomatch impossible

private def deniedComponentProgram (issue : Option Scheduled.Issue) (ticket : Nat) :
    Session grow sig (Ret (core3 grow)) :=
  match issue with
  | none => internal "dangling arena id"
  | some denied => ComponentCall.reject ticket denied

private def deniedComponentEntry (callee : ComponentCall.Callee sig) (args : Option (List FlatValue))
    (issue : Option Scheduled.Issue) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (state : Config (core3 grow) (HostState sig)) : Config (core3 grow) (HostState sig) :=
  { state with
    host := args.elim state.host (state.host.enter callee.name callee.coreType)
    ctl := cursor.control (deniedComponentProgram issue state.host.nextTicket) }

open ReturnFrame.Occurrence in
private theorem deniedComponentPath {active : ThreadId} {caller : CallerId} {store : CStore (core3 grow)}
    (callee : ComponentCall.Callee sig)
    (denied : ¬ ∃ subtask cx args pos ft limits results entry task,
      ArenaField.callers.get? store caller = some (.lower subtask cx args pos ft limits results) ∧
      ArenaField.threads.get? store active = some entry ∧ ArenaField.tasks.get? store entry.task = some task ∧
      task.inst = callee.inst ∧ callee.check store subtask cx args pos ft (limits, results) = .ok ()) :
    ∃ (edits : List (ComponentStoreEdit grow)) (args : Option (List FlatValue)) (issue : Option Scheduled.Issue),
      ∀ (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
        (state : Config (core3 grow) (HostState sig)) frames rest,
        state.store = store →
        state.ctl = ⟨some active, .prog (ComponentCall.invoke callee caller), frames⟩ :: rest →
        ComponentQuietPath profile ready dispatch ⟨some active, frames, rest⟩ state edits
          (deniedComponentEntry callee args issue ⟨some active, frames, rest⟩ state) := by
  cases record : ArenaField.callers.get? store caller with
  | none =>
    refine ⟨[id], none, none, ?_⟩
    intro dispatch state frames rest same focus
    have read := Step.get (prof := profile) (hr := ready) (dispatch := dispatch) focus
    have atRecord : ArenaField.callers.get? state.store caller = none := same ▸ record
    simp only [Prog.bind, atRecord, internalBind] at read
    exact .step read (by rw [transitionEdit, focus]; rfl) (.done _)
  | some callerRecord =>
    have wrongCaller (wrong : ∀ subtask cx args pos ft limits results,
        callerRecord ≠ .lower subtask cx args pos ft limits results) :
        ∀ (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
          (state : Config (core3 grow) (HostState sig)) frames rest,
          state.store = store →
          state.ctl = ⟨some active, .prog (ComponentCall.invoke callee caller), frames⟩ :: rest →
          ComponentQuietPath profile ready dispatch ⟨some active, frames, rest⟩ state [id, id, id]
            (deniedComponentEntry callee (some []) (some .wrongContext) ⟨some active, frames, rest⟩ state) := by
      intro dispatch state frames rest same focus
      have read := Step.get (prof := profile) (hr := ready) (dispatch := dispatch) focus
      have atRecord : ArenaField.callers.get? state.store caller = some callerRecord := same ▸ record
      simp only [Prog.bind, atRecord, Prog.pure_eq] at read
      cases callerRecord with
      | lower => exact (wrong _ _ _ _ _ _ _ rfl).elim
      | host | sub =>
        exact .step read (by rw [transitionEdit, focus]; rfl) (.step (.hostGet rfl) rfl (.step (.hostSet rfl) rfl (.done _)))
    cases callerRecord with
    | host | sub => exact ⟨[id, id, id], some [], some .wrongContext, wrongCaller (by intros; nofun)⟩
    | lower subtask cx args pos ft limits results =>
      have lowerGuard : ∃ (updates : List (ComponentStoreEdit grow)) (issue : Option Scheduled.Issue),
          ∀ (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
            (state : Config (core3 grow) (HostState sig)) frames rest,
            state.store = store →
            state.ctl = ⟨some active, .prog (ComponentCall.invoke callee caller), frames⟩ :: rest →
            ComponentQuietPath profile ready dispatch ⟨some active, frames, rest⟩ state
              ([id, id, id, id, id, id] ++ updates)
              (deniedComponentEntry callee (some args) issue ⟨some active, frames, rest⟩ state) := by
        have walk {updates issue} (remaining : ∀ dispatch (state : Config (core3 grow) (HostState sig)) frames rest,
            state.store = store → ComponentQuietPath profile ready dispatch ⟨some active, frames, rest⟩
              { state with
                host := state.host.enter callee.name callee.coreType args
                ctl := ⟨some active, .prog (do
                  if (← currentInst?) != some callee.inst then return ← ComponentCall.reject state.host.nextTicket .wrongContext
                  if let .error error := callee.check state.store subtask cx args pos ft (limits, results) then
                    return ← ComponentCall.reject state.host.nextTicket error
                  ComponentCall.acceptCaller callee caller state.host.nextTicket state.host.writer.accepted state.store cx args),
                  frames⟩ :: rest }
              (id :: id :: updates) (deniedComponentEntry callee (some args) issue ⟨some active, frames, rest⟩ state)) :
            ∀ dispatch (state : Config (core3 grow) (HostState sig)) frames rest,
              state.store = store →
              state.ctl = ⟨some active, .prog (ComponentCall.invoke callee caller), frames⟩ :: rest →
              ComponentQuietPath profile ready dispatch ⟨some active, frames, rest⟩ state
                ([id, id, id, id, id, id] ++ updates)
                (deniedComponentEntry callee (some args) issue ⟨some active, frames, rest⟩ state) := by
          intro dispatch state frames rest same focus
          have read := Step.get (prof := profile) (hr := ready) (dispatch := dispatch) focus
          have atRecord : ArenaField.callers.get? state.store caller = some (.lower subtask cx args pos ft limits results) := same ▸ record
          simp only [Prog.bind, atRecord] at read
          exact .step read (by rw [transitionEdit, focus]; rfl)
            (.step (.hostGet rfl) rfl (.step (.hostSet rfl) rfl
              (.step (.get rfl) rfl (remaining dispatch state frames rest same))))
        cases liveThread : ArenaField.threads.get? store active with
        | none =>
          refine ⟨[], none, walk ?_⟩
          intro dispatch state frames rest same
          refine .step (.currentThread rfl) rfl ?_
          refine .step (.get rfl) rfl ?_
          have atThread : ArenaField.threads.get? state.store active = none := same ▸ liveThread
          simp only [id, Prog.bind, atThread, internalBind]
          exact .done _
        | some thread =>
          cases liveTask : ArenaField.tasks.get? store thread.task with
          | none =>
            refine ⟨[id], none, walk ?_⟩
            intro dispatch state frames rest same
            refine .step (.currentThread rfl) rfl ?_
            refine .step (.get rfl) rfl ?_
            have atThread : ArenaField.threads.get? state.store active = some thread := same ▸ liveThread
            simp only [id, Prog.bind, atThread, Prog.pure_eq]
            refine .step (.get rfl) rfl ?_
            have atTask : ArenaField.tasks.get? state.store thread.task = none := same ▸ liveTask
            simp only [id, Prog.bind, atTask, internalBind]
            exact .done _
          | some task =>
            by_cases context : task.inst = callee.inst
            · cases checked : callee.check store subtask cx args pos ft (limits, results) with
              | ok success => exact (denied ⟨_, _, _, _, _, _, _, thread, task, record, liveThread, liveTask, context,
                  by cases success; exact checked⟩).elim
              | error error =>
                refine ⟨[id], some error, walk ?_⟩
                intro dispatch state frames rest same
                refine .step (.currentThread rfl) rfl ?_
                refine .step (.get rfl) rfl ?_
                have atThread : ArenaField.threads.get? state.store active = some thread := same ▸ liveThread
                simp only [id, Prog.bind, atThread, Prog.pure_eq]
                refine .step (.get rfl) rfl ?_
                have atTask : ArenaField.tasks.get? state.store thread.task = some task := same ▸ liveTask
                have atCheck : callee.check state.store subtask cx args pos ft (limits, results) = .error error := same ▸ checked
                simp only [id, Prog.bind, atTask, Prog.pure_eq, context, bne_self_eq_false, Bool.false_eq_true, ite_false, atCheck]
                exact .done _
            · refine ⟨[id], some .wrongContext, walk ?_⟩
              intro dispatch state frames rest same
              refine .step (.currentThread rfl) rfl ?_
              refine .step (.get rfl) rfl ?_
              have atThread : ArenaField.threads.get? state.store active = some thread := same ▸ liveThread
              simp only [id, Prog.bind, atThread, Prog.pure_eq]
              refine .step (.get rfl) rfl ?_
              have atTask : ArenaField.tasks.get? state.store thread.task = some task := same ▸ liveTask
              simp only [id, Prog.bind, atTask, Prog.pure_eq, bne_iff_ne, ne_eq, Option.some.injEq, context, not_false_eq_true, ite_true]
              exact .done _
      obtain ⟨updates, issue, path⟩ := lowerGuard
      exact ⟨[id, id, id, id, id, id] ++ updates, some args, issue, path⟩

open ReturnFrame.Occurrence in
private theorem cutDeniedComponentProgram (issue : Option Scheduled.Issue) {leftTicket rightTicket : Nat}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : start.ctl = check.control (deniedComponentProgram issue leftTicket))
    (rightFocus : incoming.ctl = canon.control (deniedComponentProgram issue rightTicket))
    (paired : PairedComponentSite older start incoming check canon)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    ∃ leading suffix reached peer, labels = leading ++ suffix ∧
      OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
      Steps profile ready (specDispatch ready base) reached suffix finish ∧
      ((suffix = [] ∧ PairedComponentSite older reached peer check canon) ∨
        (reached.ctl = [] ∧ peer.ctl = [] ∧ HostFrame.Related.Paired older reached peer)) := by
  cases issue with
  | some issue => exact cutObservedReject issue leftFocus rightFocus paired run
  | none =>
    let body : Session grow sig Empty := internal "dangling arena id"
    let next : Empty → Session grow sig (Ret (core3 grow)) := fun denied => nomatch denied
    have focusEq (ticket : Nat) : deniedComponentProgram (grow := grow) (sig := sig) none ticket = body >>= next := by
      exact (internalBind _ next).symm
    rw [focusEq] at leftFocus rightFocus
    obtain ⟨leading, suffix, reached, peer, split, moved, residual, frontier, _, _⟩ :=
      cutComponentStoreBody (closed := True) body next next (fun _ => storeEffectTrap _) leftFocus rightFocus paired run
    refine ⟨leading, suffix, reached, peer, split, moved, residual, ?_⟩
    cases frontier with
    | returned impossible _ _ _ => exact nomatch impossible
    | pending _ _ _ _ site boundary => exact .inl ⟨boundary.resolve_right (fun openFrontier => openFrontier.1 trivial), site⟩
    | trapped checked canonical aligned => exact .inr ⟨checked, canonical, aligned⟩

open ReturnFrame.Occurrence in
private theorem cutComponentDenied {callees : List (ComponentCall.Callee sig)}
    {hostId : HostFuncId} {caller : CallerId} {active : ThreadId} {frames rest resume label next}
    {callee : ComponentCall.Callee sig}
    (linked : callees.filter (·.hostId == hostId) = [callee])
    (denied : ¬ ComponentHostAdmission callees hostId caller active start)
    (focused : start.ctl = ⟨some active, .prog (.op (.call (.hostFunc hostId caller)) resume), frames⟩ :: rest)
    (step : Step profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start label next)
    (tail : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) next labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ComponentEntryFailure profile ready bindings callees older start incoming finish label labels := by
  let base := ComponentCall.hostWithComponent (grow := grow) bindings callees
  obtain ⟨edits, args, issue, path⟩ := deniedComponentPath (profile := profile) (ready := ready) (caller := caller)
    (active := active) (store := start.store) callee (fun ⟨subtask, cx, args, pos, ft, limits, results, entry, task, guards⟩ =>
      denied ⟨callee, subtask, cx, args, pos, ft, limits, results, entry, task, linked, guards⟩)
  obtain ⟨peerFrames, peerRest, rfl, rfl, entered, marked, leftMark, rightMark, _⟩ :=
    cutLinkedComponentInstall linked focused step paired
  let check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨some active, .prog resume :: frames, rest⟩
  let canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨some active, .prog resume :: peerFrames, peerRest⟩
  let left := { start with ctl := check.control (ComponentCall.invoke callee caller) }
  let right := { incoming with ctl := canon.control (ComponentCall.invoke callee caller) }
  have install := sharedTopTransport marked leftMark rightMark
  have entry := path (specDispatch ready base) left check.frames check.rest rfl rfl
  have canonEntry := path (specDispatch ready (LiveDispatch.host bindings base)) right canon.frames canon.rest paired.data.1.symm rfl
  have site (leftHost rightHost : HostState sig) : PairedComponentSite older { left with host := leftHost }
      { right with host := rightHost } check canon := by
    obtain ⟨_, _, focus, retargeted⟩ := HostFrame.Related.Paired.retarget (left := left) (right := right) entered
      rfl (.prog (.pure (.cancel .none))) leftHost rightHost
    simp only [right, check, canon, PayloadPrefix.Cursor.control, List.cons.injEq, Activation.mk.injEq, true_and] at focus
    obtain ⟨rfl, rfl⟩ := focus
    exact retargeted
  rcases splitSilent (entry.track (.active 0 0)).toTrail.steps tail with ⟨remaining, split, residual⟩ | short
  · obtain ⟨leading, suffix, reached, peer, bodySplit, moved, after, outcome⟩ := cutDeniedComponentProgram (bindings := bindings)
      (leftTicket := left.host.nextTicket) (rightTicket := right.host.nextTicket) issue
      (start := deniedComponentEntry callee args issue check left) (incoming := deniedComponentEntry callee args issue canon right)
      rfl rfl (site _ _) residual
    have intoDenied := CallbackPrefix.stationaryTransport (bindings := bindings) entry.track canonEntry.track
    have crossed := (CallbackPrefix.transportAppend intoDenied moved).choose_spec.1
    refine ⟨List.replicate edits.length .tau ++ leading, suffix, reached, peer, check, canon, rfl, ?_, ?_, after, outcome⟩
    · rw [split, bodySplit, List.append_assoc]
    · simpa only [List.map_nil, List.append_nil, List.singleton_append] using
        (CallbackPrefix.transportAppend install crossed).choose_spec.1
  · obtain ⟨_, peer, moved, endpoint, _, _⟩ := compareQuietShort (bindings := bindings) entry canonEntry (site left.host right.host)
      ⟨_, rfl⟩ ⟨_, rfl⟩ tail short
    exact ⟨labels, [], finish, peer, check, canon, rfl, (List.append_nil _).symm,
      (CallbackPrefix.transportAppend install moved).choose_spec.1, .refl _, .inl ⟨rfl, endpoint⟩⟩

private theorem classifyComponentInstallOutcome {callees : List (ComponentCall.Callee sig)} {label next}
    (step : Step profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start label next)
    (tail : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) next labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ComponentInstallOutcome profile ready bindings callees older start incoming next finish label labels := by
  classical
  intro active hostId caller resume frames rest focused
  by_cases admits : ComponentHostAdmission callees hostId caller active start
  · obtain ⟨callee, subtask, cx, args, pos, ft, limits, results, entry, task, linked, record, liveThread, liveTask, context, admitted⟩ := admits
    obtain ⟨peerFrames, peerRest, silent, installed, body⟩ :=
      classifyLinkedComponentAdmission linked focused step tail paired record liveThread liveTask context admitted
    exact .inr (.inr ⟨callee, cx, args, peerFrames, peerRest, linked, silent, installed, body⟩)
  · by_cases linked : ∃ callee, callees.filter (·.hostId == hostId) = [callee]
    · obtain ⟨callee, singleton⟩ := linked
      exact .inl ⟨⟨callee, singleton⟩, admits, cutComponentDenied singleton admits focused step tail paired⟩
    · exact .inr (.inl ⟨linked, cutComponentBadLink linked focused step tail paired⟩)

theorem classifyComponentWorkerPrefix {callees : List (ComponentCall.Callee sig)}
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ComponentWorkerCut profile ready bindings callees older start incoming labels finish := by
  cases cutExecutedCallback run paired (includeComponentCalls := true) with
  | complete segment => exact .complete segment
  | boundary split prefixSegment kind step tail smaller =>
    exact .boundary split prefixSegment kind step tail smaller (classifyComponentInstallOutcome step tail prefixSegment.paired)

open ReturnFrame.Occurrence in
theorem rejoinedAllocatorResidual {callees : List (ComponentCall.Callee sig)}
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
      checkTrace canonTrace labels finish first second := by
  obtain ⟨leading, remaining, lhs, rhs, split, checked, canonical, paired, _, transport, cut⟩ := replay
  obtain ⟨reached, mark⟩ := carryAllocatorTransport tracked transport
  have suffix : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
      lhs remaining finish := by
    rcases cut with ⟨rfl, rfl⟩ | ⟨_, _, _, rfl, step, tail, _, _⟩
    · exact .refl _
    · exact .cons step tail
  exact ⟨leading, remaining, lhs, rhs, reached, split, checked, canonical, suffix, mark,
    fun _ _ focus => alignAllocatorPop mark paired focus installed suffix⟩

open ReturnFrame.Occurrence in
theorem classifyEnclosingAllocatorTail {callees : List (ComponentCall.Callee sig)}
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
          leftStart rightStart (seen ++ PayloadPrefix.visible added) left right offset) := by
  refine mapWorkerTrack (classifyWithOccurrence run paired tracked.outside) ?_
  intro added left right aligned trails
  refine ⟨extendMark tracked trails, ?_⟩
  obtain ⟨checkLeading, canonLeading, front, checkSeen, canonSeen, _⟩ := enclosing
  obtain ⟨_, _, _, _, back⟩ := trails
  refine ⟨checkLeading ++ added, canonLeading ++ added, ?_,
    (visibleAppend ..).trans (congrArg (· ++ PayloadPrefix.visible added) checkSeen),
    (visibleAppend ..).trans (congrArg (· ++ PayloadPrefix.visible added) canonSeen), (HostFrame.Related.Paired.data aligned).1⟩
  intro depth
  obtain ⟨middle, leftFront, rightFront⟩ := front depth
  obtain ⟨reached, leftBack, rightBack⟩ := back middle
  exact ⟨reached, leftFront.append leftBack, rightFront.append rightBack⟩

theorem classifyAfterDelivery {callees : List (ComponentCall.Callee sig)}
    (tail : RejoinedWorkerTail profile ready bindings callees older start incoming)
    (empty : ∀ first second, ¬ older first second) {actions reached outgoing queued done}
    (between : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      start incoming.host actions labels reached outgoing)
    (next : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) reached queued done) :
    Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels reached ∧
    Steps profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
      incoming labels (HostFrame.replace reached outgoing) ∧
    ClassifiedWorkerTail profile ready bindings callees (fun _ _ => False) reached (HostFrame.replace reached outgoing) queued done ∧
    (incoming.host.writer.accepted = start.host.writer.accepted → outgoing.writer.accepted = reached.host.writer.accepted) := by
  obtain ⟨checked, live, roots⟩ := tail.delivery empty between
  have paired := LiveDispatch.paired_replace reached outgoing
  exact ⟨checked, live, classifyReplay (LiveDispatch.paired_replay paired next), roots⟩

theorem alignDeliveryResidual {callees : List (ComponentCall.Callee sig)}
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
      (deliveryLabels ≠ [] → suffix.length < labels.length) := by
  obtain ⟨checked, canonical, _⟩ := tail.delivery empty between
  refine ⟨alignWorkerBody checked actual, fun suffix split => ?_⟩
  have residual := stripExactPrefix checked (split ▸ actual)
  refine ⟨residual, canonical, classifyReplay (LiveDispatch.paired_replay (LiveDispatch.paired_replace reached outgoing) residual), ?_⟩
  intro progress
  rw [split, List.length_append]
  exact Nat.lt_add_of_pos_left (List.length_pos_iff.mpr progress)

open ReturnFrame.Occurrence in
theorem rebaseAllocatorAtRequest {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {entered lhs rhs : Config (core3 grow) (HostState sig)} {checkedEntry canonEntry seen : Trace grow sig}
    (checked : site.EntryPrefix profile ready base checkedEntry site.checked)
    (canonical : ∀ place, Prefix profile ready (specDispatch ready (host bindings base))
      incoming place canonEntry entered (site.entryPlace place))
    (checkSilent : PayloadPrefix.visible checkedEntry = []) (canonSilent : PayloadPrefix.visible canonEntry = [])
    (suspended : ComparedAllocatorPaths profile ready base bindings site.checked entered seen lhs rhs) :
    ComparedAllocatorPaths profile ready base bindings site.start incoming seen lhs rhs := by
  obtain ⟨checkTrace, canonTrace, movement, checkSeen, canonSeen, same⟩ := suspended
  refine ⟨checkedEntry ++ checkTrace, canonEntry ++ canonTrace, ?_, ?_, ?_, same⟩
  · intro depth
    obtain ⟨reached, left, right⟩ := movement (depth + 1)
    exact ⟨reached, (checked (.active 0 depth)).toTrail.append left, (canonical (.active 0 depth)).toTrail.append right⟩
  · rw [visibleAppend, checkSilent, checkSeen, List.nil_append]
  · rw [visibleAppend, canonSilent, canonSeen, List.nil_append]

open ReturnFrame.Occurrence in
theorem pendingCoupledEntry {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {callees : List (ComponentCall.Callee sig)} {checkLabels : Trace grow sig}
    (checked : site.EntryPrefix profile ready (ComponentCall.hostWithComponent bindings callees) checkLabels site.checked)
    (pending : PendingRecursiveRoot profile ready bindings callees older site incoming) :
    ∃ canonLabels entered, PayloadPrefix.visible canonLabels = [] ∧
      CoupledOccurrencePaths profile ready (ComponentCall.hostWithComponent bindings callees) bindings
        site.start incoming checkLabels canonLabels site.checked entered := by
  obtain ⟨canonLabels, entered, silent, canonical, _, _⟩ := pending
  refine ⟨canonLabels, entered, silent, ?_⟩
  intro place
  cases place with
  | none => exact ⟨none, Trail.absent checked.steps, Trail.absent (prefix_survives (canonical (.active 0 0))).1⟩
  | some place => exact ⟨some (site.entryPlace place), (checked place).toTrail, (canonical place).toTrail⟩

open ReturnFrame.Occurrence in
theorem pendingComparedEntry {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {callees : List (ComponentCall.Callee sig)} {checkLabels : Trace grow sig}
    (checked : site.EntryPrefix profile ready (ComponentCall.hostWithComponent bindings callees) checkLabels site.checked)
    (silent : PayloadPrefix.visible checkLabels = [])
    (pending : PendingRecursiveRoot profile ready bindings callees older site incoming) :
    ∃ entered, HostFrame.Related.Paired older (site.reference site.referenceReply) entered ∧ entered.host = incoming.host ∧
      ComparedOccurrencePaths profile ready (ComponentCall.hostWithComponent bindings callees) bindings
        site.start incoming [] site.checked entered := by
  obtain ⟨canonLabels, entered, canonSilent, canonical, paired, hostSame⟩ := pending
  refine ⟨entered, paired, hostSame, checkLabels, canonLabels, ?_, silent, canonSilent,
    (HostFrame.Related.Paired.data paired).1⟩
  intro mark
  cases mark with
  | none => exact ⟨none, Trail.absent checked.steps, Trail.absent (prefix_survives (canonical (.active 0 0))).1⟩
  | some place => exact ⟨some (site.entryPlace place), (checked place).toTrail, (canonical place).toTrail⟩

open ReturnFrame.Occurrence in
private theorem alignRangeTransport {leftEntry rightEntry checked canonical lhs rhs : Config (core3 grow) (HostState sig)}
    {checkTrace canonTrace observed : Trace grow sig}
    (movement : OccurrenceTransport profile ready base bindings leftEntry rightEntry checkTrace canonTrace checked canonical
      [some (.active 0 0)])
    (suffix : CollectionRangeTransport profile ready base bindings checked canonical lhs rhs observed)
    (notBranch : ∀ action ∈ observed, ¬ workerBranchLabel action)
    (actual : Steps profile ready (specDispatch ready base) checked labels finish) :
    AlignedCollectionRange profile ready base bindings leftEntry rightEntry lhs rhs checkTrace canonTrace observed labels finish := by
  obtain ⟨leftTail, rightTail, whole, checkSeen, canonSeen, same⟩ := suffix movement
  obtain ⟨_, before, _⟩ := CallbackPrefix.transportPaths movement none
  obtain ⟨_, after, _⟩ := CallbackPrefix.transportPaths whole none
  exact ⟨leftTail, rightTail, whole, checkSeen, canonSeen, same,
    alignLocalBody (stripExactPrefix before.steps after.steps) actual (noBranchOfVisible checkSeen notBranch)⟩

open ReturnFrame.Occurrence in
private theorem alignCollectionRange {leftEntry rightEntry checked canonical : Config (core3 grow) (HostState sig)}
    {checkTrace canonTrace seen : Trace grow sig} {cursor destination area count pointer plan checkNext canonNext}
    (movement : OccurrenceTransport profile ready base bindings leftEntry rightEntry checkTrace canonTrace checked canonical
      [some (.active 0 0)])
    (range : CollectionRangeOccurrences profile ready base bindings older leftEntry rightEntry checked canonical seen
      cursor destination area count pointer plan checkNext canonNext)
    (actual : Steps profile ready (specDispatch ready base) checked labels finish) :
    CollectionRangeRun profile ready base bindings older leftEntry rightEntry checked canonical checkTrace canonTrace labels finish
      cursor destination area count pointer plan checkNext canonNext := by
  have align {lhs rhs : Config (core3 grow) (HostState sig)} {observed : Trace grow sig}
      (notBranch : ∀ action ∈ observed, ¬ workerBranchLabel action)
      (suffix : CollectionRangeTransport profile ready base bindings checked canonical lhs rhs observed) :
      AlignedCollectionRange profile ready base bindings leftEntry rightEntry lhs rhs checkTrace canonTrace observed labels finish :=
    alignRangeTransport movement suffix notBranch actual
  have trap (reason : TrapReason) : ∀ action ∈ ([.trap reason] : Trace grow sig), ¬ workerBranchLabel action := by
    intro action member
    have same := List.mem_singleton.mp member
    subst action
    exact id
  obtain ⟨bytes, width, sized, verdict⟩ := range
  refine ⟨bytes, width, sized, ?_⟩
  by_cases misaligned : pointer ≠ ABI.alignTo pointer area.alignment
  · simp only [ite_eq_left misaligned] at verdict ⊢
    exact align (trap .unalignedPointer) verdict.2
  · simp only [ite_eq_right misaligned] at verdict ⊢
    by_cases fits : pointer + count * area.size ≤ bytes
    · simp only [ite_eq_left fits] at verdict ⊢
      obtain ⟨canon, frame, _, _, _, suffix⟩ := verdict
      exact ⟨canon, frame, align (by simp) suffix⟩
    · simp only [ite_eq_right fits] at verdict ⊢
      exact align (trap .outOfBounds) verdict.2

open PayloadPrefix ReturnFrame.Occurrence Stored.Endpoints.RecordLower in
theorem driveCollectionSlice {destination : RecordDestination} {inst : InstId} {type element : Stored.TypeOf}
    {entries : List Field} {index budget : Nat} {output : Stored.Lower.Output}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output}
    {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output}
    {check canon : Cursor (E := core3 grow) (HostState sig)}
    {seen : Trace grow sig} {initial reference : Config (core3 grow) (HostState sig)}
    {visit : Nat → Nat → TrailFinish grow sig} {sink : RefusalSink grow sig}
    (body : LiveCollectionOccurrenceEntry profile ready base bindings older destination inst type element entries index output
      checkNext canonNext initial reference start incoming seen check canon visit sink)
    (same : start.store = incoming.store)
    (width : (core3 grow).memAddrType? incoming.store.core destination.memory = some destination.width)
    (actual : Steps profile ready (specDispatch ready base) start labels finish)
    (bounded : labels.length ≤ budget) (compare : ShorterCallbackSlices profile ready base bindings budget) :
    CollectionRunSlice profile ready base bindings older destination inst type element entries index output checkNext canonNext
      start incoming check canon labels finish seen visit := by
  classical
  unfold LiveCollectionOccurrenceEntry at body
  unfold CollectionRunSlice
  cases prepared : Stored.OwnedMemory.Claims.Record.prepare start.store start.host.writer (Field.listObjects entries) with
  | error issue =>
    simp only [prepared] at body ⊢
    obtain ⟨_, transport, _⟩ := body
    obtain ⟨_, checked, _⟩ := CallbackPrefix.transportPaths transport none
    exact ⟨transport, alignLocalBody checked.steps actual (by simp [workerBranchLabel])⟩
  | ok value =>
    cases value
    simp only [prepared] at body ⊢
    obtain ⟨installed, entered⟩ := body width
    rcases sliceInstalledCallback installed (by decide) actual
      (fun smaller run pair => compare (Nat.lt_of_lt_of_le smaller bounded) run pair) with
      short | ⟨checked, canonical, trailing, reached, peer, split, input, boundary⟩
    · exact .inl short
    obtain ⟨actualChecked, actualCanon, actualPeer, mark, tracked, paired, _, movement, exactPath, returns⟩ := entered input
    change (checked, canonical, peer) = (actualChecked, actualCanon, actualPeer) at exactPath
    rcases Prod.mk.inj exactPath with ⟨rfl, paths⟩
    rcases Prod.mk.inj paths with ⟨rfl, rfl⟩
    have compared := show PayloadPrefix.visible canonical = PayloadPrefix.visible checked from by
      cases input with
      | executed segment => exact segment.observed
    have grows : Core3.Grows start.store.core reached.store.core := by
      cases input with
      | executed segment => exact segment.checkedRun.grows
    refine .inr ⟨checked, canonical, trailing, reached, peer, mark, by simpa using split, compared, tracked, paired, movement,
      boundary, ?_⟩
    by_cases active : mark = some (.active 0 0)
    · subst mark
      let area := ABI.layout destination.width element
      let first := checkedCollectionResume destination inst entries area index output checkNext
      by_cases returning : ∃ (pointer : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)),
          reached.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer))
      · obtain ⟨pointer, cursor, focus⟩ := returning
        have actualTail := returningCallbackEndSteps boundary focus
        have history : ComparedOccurrencePaths profile ready base bindings start incoming (PayloadPrefix.visible checked) reached peer := by
          refine ⟨_, _, CallbackPrefix.transportPaths movement, ?_, ?_, paired.data.1⟩
          · exact visibleAppend ([.tau, .tau, .tau] : Trace grow sig) checked
          · exact (visibleAppend ([.tau, .tau] : Trace grow sig) canonical).trans compared
        have range := CallbackRange.collectionRangeOccurrences (profile := profile) (ready := ready)
          destination inst type element entries output index pointer checkNext canonNext tracked paired focus (same ▸ width) grows history
        have aligned := alignCollectionRange movement range actualTail
        cases actualTail with
        | refl => exact .inl (.inl rfl)
        | @cons _ next _ action residual taken suffix =>
          have pop : Step profile ready (specDispatch ready base) reached .tau
              { reached with ctl := cursor.control (first (.nat pointer)) } := .popProg focus
          obtain ⟨rfl, rfl⟩ := silentStepUnique pop taken
          refine .inr ⟨pointer, cursor, residual, rfl, rfl, focus, suffix, aligned, ?_⟩
          intro bytes size aligned fits fresh
          obtain ⟨capacity, sized, range⟩ := returns pointer cursor rfl focus
          cases Option.some.inj (sized.symm.trans size)
          rw [ite_eq_right (not_not_intro aligned), ite_eq_left fits] at range
          obtain ⟨lhs, rhs, peerCursor, _, _, frame, width, sized, growth, checkedAt, canonicalAt, movementLocal, child⟩ := range.2 fresh
          exact ⟨lhs, rhs, peerCursor, frame, width, sized, growth, checkedAt, canonicalAt,
            alignRangeTransport movement movementLocal (by simp) (.cons pop suffix), child⟩
      · exact .inl (.inr (.inr returning))
    · exact .inl (.inr (.inl active))

open PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
private theorem elementHeadFoci (destination : RecordDestination) (inst : InstId) (item : Field) (rest : List Field)
    (stride pointer index : Nat) {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)}
    (checkAt : start.ctl = check.control (Record.Effects.elements recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (item :: rest) stride pointer index >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none
      (destination.context inst) destination.width (item :: rest) .value stride pointer >>= canonNext)) :
    start.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index (.memory pointer) >>=
      checkTail (.elements stride) destination inst rest (index + 1) (pointer + stride) checkNext) ∧
    incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
      destination.width item (.memory pointer) >>=
      canonTail (.elements stride) destination inst rest (pointer + stride) canonNext) := by
  constructor
  · rw [checkAt, Record.Effects.elements]
    congr 1
    simp only [Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext verdict
    cases verdict with
    | error _ => rfl
    | ok value => cases value; rfl
  · rw [canonAt, CanonicalTree.elements]
    congr 1
    exact Prog.bind_assoc _ _ _

open PayloadPrefix ReturnFrame.Occurrence Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims in
theorem driveNominalElements (destination : RecordDestination) (inst : InstId) (entries : List Field) (stride pointer index : Nat)
    (nominal : ∀ item ∈ entries, CanonicalHandle item)
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (checkAt : start.ctl = check.control (Record.Effects.elements recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width entries stride pointer index >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none
      (destination.context inst) destination.width entries .value stride pointer >>= canonNext))
    (actual : Steps profile ready (specDispatch ready base) start labels finish) :
    AllocatedElementRun profile ready base bindings older checkNext canonNext
      (ElementStop destination inst entries stride pointer canonNext) check canon start incoming labels finish := by
  have static (left right : Config (core3 grow) (HostState sig)) :
      OccurrenceTransport profile ready base bindings left right [] [] left right :=
    CallbackPrefix.stationaryTransport (fun place => .done left place) (fun place => .done right place)
  induction entries generalizing pointer index start incoming labels with
  | nil =>
    simp only [Record.Effects.elements, CanonicalTree.elements, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind'] at checkAt canonAt
    exact ⟨[], [], labels, start, incoming, rfl, rfl, frame.store, static .., actual, .returned ⟨(), frame, checkAt, canonAt⟩⟩
  | cons item rest ih =>
    let checkTail := LinkedCallback.MemorySequence.checkTail (.elements stride) destination inst rest (index + 1) (pointer + stride) checkNext
    let canonTail := LinkedCallback.MemorySequence.canonTail (.elements stride) destination inst rest (pointer + stride) canonNext
    obtain ⟨atHead, atCanonHead⟩ := elementHeadFoci destination inst item rest stride pointer index checkAt canonAt
    have leaf := LinkedCallback.ChildFrameOver.handle_field_then_between
      (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
      (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst item (nominal item (by simp))
      index (.memory pointer) checkTail canonTail frame (Core3.Grows.refl _) atHead atCanonHead
      (next := fun _ lhs rhs check canon => LinkedCallback.ChildFrameOver older lhs rhs check canon)
      (fun _ _ _ _ _ frame _ _ _ => frame)
    unfold LinkedCallback.HandleFieldThenBetween at leaf
    cases decision : liveLeafPlan start.store start.host.writer index item with
    | error issue =>
      rw [decision] at leaf
      obtain ⟨guard, tau, tracks⟩ := leaf
      have quiet : visible guard = [] := silentVisible (List.all_eq_true.mpr (fun action member => by rw [tau action member]))
      cases alignLocalBody (prefix_survives (tracks (.active 0 0))).1 actual (noBranchOfVisible quiet (by simp)) with
      | inside _ nonempty tail =>
        exact ⟨[], [], labels, start, incoming, rfl, rfl, frame.store, static .., actual, .inside nonempty tail⟩
      | reached split tail =>
        refine ⟨guard, [], _, _, incoming, split, quiet, ?_,
          CallbackPrefix.stationaryTransport tracks (fun place => .done _ place), tail,
          .refused issue ⟨rfl, _, ⟨[], item :: rest, rfl, by simp, by simp⟩, canonAt⟩⟩
        exact frame.store
    | ok plan =>
      rw [decision] at leaf
      obtain ⟨store, verdict, guard, checkLabels, canonLabels, tau, leftKind, rightKind, checkRun, _, tracks, continued⟩ := leaf
      have quiet : visible guard = [] := silentVisible (List.all_eq_true.mpr (fun action member => by rw [tau action member]))
      have observed : visible (guard ++ checkLabels) = visible canonLabels := by
        rw [visibleAppend, quiet, List.nil_append, CallbackPrefix.visibleLeaf leftKind, CallbackPrefix.visibleLeaf rightKind]
        cases verdict <;> rfl
      have localOnly : ∀ action ∈ visible canonLabels, ¬ workerBranchLabel action := by
        rw [CallbackPrefix.visibleLeaf rightKind]
        cases verdict <;> simp [workerBranchLabel]
      cases alignLocalBody checkRun actual (noBranchOfVisible observed localOnly) with
      | inside _ nonempty tail =>
        exact ⟨[], [], labels, start, incoming, rfl, rfl, frame.store, static .., actual, .inside nonempty tail⟩
      | reached split tail =>
        have movement := CallbackPrefix.localLeafTransport tracks
        cases verdict with
        | error reason =>
          refine ⟨_, _, _, _, _, split, observed, ?_, movement, tail, .trapped rfl rfl⟩
          rfl
        | ok value =>
          cases value
          obtain ⟨_, _, paired⟩ := continued () rfl
          obtain ⟨checked, canonical, residual, lhs, rhs, restSplit, seen, same, restMovement, after, ending⟩ :=
            ih (pointer := pointer + stride) (index := index + 1) (fun child included => nominal child (List.mem_cons_of_mem _ included))
              paired rfl rfl tail
          refine ⟨(guard ++ checkLabels) ++ checked, canonLabels ++ canonical, residual, lhs, rhs,
            by simp only [split, restSplit, List.append_assoc],
            by rw [visibleAppend (guard ++ checkLabels) checked, visibleAppend canonLabels canonical, observed, seen],
            same, (CallbackPrefix.transportAppend movement restMovement).choose_spec.1, after, ?_⟩
          cases ending with
          | returned success => exact .returned success
          | trapped checked canonical => exact .trapped checked canonical
          | inside nonempty tail => exact .inside nonempty tail
          | refused issue stopped =>
            obtain ⟨checkedAt, stop, ⟨preceding, pending, remaining, nonempty, canonStop⟩, canonicalAt⟩ := stopped
            refine .refused issue ⟨checkedAt, stop, ⟨item :: preceding, pending, congrArg (item :: ·) remaining, nonempty, ?_⟩, canonicalAt⟩
            simpa only [List.length_cons, Nat.succ_mul, Nat.add_assoc, Nat.add_comm stride] using canonStop

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
private theorem driveStringElements (destination : RecordDestination) (inst : InstId) (entries : List Field)
    {root : Field} {schema : Stored.TypeOf} {origin : CStore (core3 grow)} {pointer count bytes ordinal index budget : Nat}
    (rootLayout : root.LayoutMatches schema)
    (fits : Stored.Lower.fits Quirks.none destination.encoding destination.width schema root.value = true)
    (allocates : Field.AllocatorFor destination.realloc root)
    (compiled : ∀ item ∈ entries, item.LayoutMatches (.prim .string) ∧ item.Emitted ∧ root.Descendant item)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : pointer = alignTo pointer (layout destination.width (.prim .string : Stored.TypeOf)).alignment)
    (bounds : pointer + count * (layout destination.width (.prim .string : Stored.TypeOf)).size ≤ bytes)
    (remaining : ordinal + entries.length ≤ count)
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (growth : Core3.Grows origin.core start.store.core) :
    let stride := (layout destination.width (.prim .string : Stored.TypeOf)).size
    let address := pointer + ordinal * stride
    start.ctl = check.control (Record.Effects.elements recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width entries stride address index >>= checkNext) →
    incoming.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none
      (destination.context inst) destination.width entries .value stride address >>= canonNext) →
    Steps profile ready (specDispatch ready base) start labels finish → labels.length ≤ budget →
    ShorterCallbackSlices profile ready base bindings budget →
    StringRunSlice profile ready base bindings older
      (fun _ lhs rhs cursor peer => LinkedCallback.ChildFrameOver older lhs rhs cursor peer ∧
        Core3.Grows origin.core lhs.store.core ∧ lhs.ctl = cursor.control (checkNext (.ok ())) ∧ rhs.ctl = peer.control (canonNext ()))
      start incoming labels finish := by
  induction entries generalizing ordinal index start incoming labels check canon with
  | nil =>
    intro stride address checkAt canonAt actual _ _
    simp only [Record.Effects.elements, CanonicalTree.elements, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind'] at checkAt canonAt
    exact ⟨[], [], labels, start, incoming, [], rfl, rfl,
      CallbackPrefix.stationaryTransport (fun place => .done _ place) (fun place => .done _ place), frame.store, actual,
      .descriptor (pointer := address) ⟨frame, growth, checkAt, canonAt⟩⟩
  | cons item rest ih =>
    intro stride address checkAt canonAt actual bounded compare
    obtain ⟨shape, emitted, path⟩ := compiled item (by simp)
    have inRange : ordinal < count := by simp only [List.length_cons] at remaining; omega
    have placement := (list_entry_placement_of_growth destination inst (.prim .string) growth width sized aligned bounds inRange).2
    obtain ⟨headAt, peerAt⟩ := elementHeadFoci destination inst item rest stride address index checkAt canonAt
    obtain ⟨str, field⟩ := CallbackRange.compiledStringCommit destination inst (.memory address) rootLayout fits allocates path
      shape emitted embedder frame (growth.memAddrType width) placement headAt peerAt
    obtain ⟨checked, canonical, trailing, left, right, marks, split, seen, movement, same, tail, ending⟩ :=
      driveStringCommit field actual bounded compare
    have keep (last : StringSliceEnd profile ready base bindings older
         (fun _ lhs rhs cursor peer => LinkedCallback.ChildFrameOver older lhs rhs cursor peer ∧
           Core3.Grows origin.core lhs.store.core ∧ lhs.ctl = cursor.control (checkNext (.ok ())) ∧ rhs.ctl = peer.control (canonNext ()))
         left right trailing finish marks) :
        StringRunSlice profile ready base bindings older
          (fun _ lhs rhs cursor peer => LinkedCallback.ChildFrameOver older lhs rhs cursor peer ∧
            Core3.Grows origin.core lhs.store.core ∧ lhs.ctl = cursor.control (checkNext (.ok ())) ∧ rhs.ctl = peer.control (canonNext ()))
          start incoming labels finish := ⟨checked, canonical, trailing, left, right, marks, split, seen, movement, same, tail, last⟩
    cases ending with
    | trap lhs rhs => exact keep (.trap lhs rhs)
    | localPrefix nonempty residual => exact keep (.localPrefix nonempty residual)
    | localChoice split branch shared step residual => exact keep (.localChoice split branch shared step residual)
    | installPrefix short => exact keep (.installPrefix short)
    | collectionInstall short => exact keep (.collectionInstall short)
    | collectionRange nonempty tail => exact keep (.collectionRange nonempty tail)
    | callback tracked paired boundary noPop => exact keep (.callback tracked paired boundary noPop)
    | descriptor returned =>
      obtain ⟨⟨⟩, paired, grew, leftAt, rightAt⟩ := returned
      have nextBound : ordinal + 1 + rest.length ≤ count := by simp only [List.length_cons] at remaining; omega
      have nextAddress : pointer + (ordinal + 1) * stride = address + stride := by
        simp only [address, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      have nextBudget : trailing.length ≤ budget := by rw [split, List.length_append] at bounded; omega
      obtain ⟨checkedRest, canonRest, residual, reached, peer, laterMarks, used, observed, moved, stores, after, last⟩ :=
        ih (ordinal := ordinal + 1) (index := index + 1) (fun child member => compiled child (List.mem_cons_of_mem _ member))
          nextBound paired (growth.trans grew) (by rw [nextAddress]; exact leftAt) (by rw [nextAddress]; exact rightAt) tail nextBudget compare
      refine ⟨checked ++ checkedRest, canonical ++ canonRest, residual, reached, peer, laterMarks,
        by simp only [split, used, List.append_assoc],
        by rw [visibleAppend canonical canonRest, visibleAppend checked checkedRest, seen, observed],
        ?_, stores, after, last⟩
      simpa only [List.map_nil, List.append_nil] using (CallbackPrefix.transportAppend movement moved).choose_spec.1

open ABI PayloadPrefix Stored.Endpoints.RecordLower LinkedCallback.MemorySequence in
theorem driveStringListBody (destination : RecordDestination) (inst : InstId) (entries : List Field)
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
      start incoming labels finish := by
  intro element area mode aligned bounds checkAt canonAt actual bounded compare
  have compiled : ∀ item ∈ entries, item.LayoutMatches element ∧ item.Emitted ∧ root.Descendant item := by
    have layouts := CallbackRange.listEntries matched
    intro item member
    refine ⟨entries_match_of_mem layouts member, ?_, path.trans (.dynamic member (.self item))⟩
    cases emitted with
    | list children => exact children item member
  obtain ⟨checkAt, canonAt⟩ := CallbackRange.collectionElementFoci destination inst entries area mode output pointer index
    checkNext canonNext checkAt canonAt
  have valueMode : mode = .value := by cases output <;> rfl
  rw [valueMode] at canonAt
  obtain ⟨checked, canonical, trailing, left, right, marks, split, seen, move, same, tail, ending⟩ :=
    driveStringElements destination inst entries (ordinal := 0) (index := 0) rootLayout fits allocates compiled embedder width sized aligned bounds
      (by simp) frame (Core3.Grows.refl _) (by simpa only [Nat.zero_mul, Nat.add_zero] using checkAt)
      (by simpa only [Nat.zero_mul, Nat.add_zero] using canonAt) actual bounded compare
  have keep (last : StringSliceEnd profile ready base bindings older
      (fun _ lhs rhs cursor peer => ∃ value, LinkedCallback.ChildFrameOver older lhs rhs cursor peer ∧
        Core3.Grows start.store.core lhs.store.core ∧ lhs.ctl = cursor.control (checkNext (.ok value)) ∧ rhs.ctl = peer.control (canonNext value))
      left right trailing finish marks) :
    StringRunSlice profile ready base bindings older _ start incoming labels finish :=
    ⟨checked, canonical, trailing, left, right, marks, split, seen, move, same, tail, last⟩
  cases ending with
  | trap lhs rhs => exact keep (.trap lhs rhs)
  | localPrefix nonempty residual => exact keep (.localPrefix nonempty residual)
  | localChoice split branch shared step residual => exact keep (.localChoice split branch shared step residual)
  | installPrefix short => exact keep (.installPrefix short)
  | collectionInstall short => exact keep (.collectionInstall short)
  | collectionRange nonempty tail => exact keep (.collectionRange nonempty tail)
  | callback tracked paired boundary noPop => exact keep (.callback tracked paired boundary noPop)
  | descriptor returned =>
    obtain ⟨paired, grew, leftAt, rightAt⟩ := returned
    have publish := CallbackRange.livePublish (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst pointer entries.length output checkNext canonNext
      (fun value lhs rhs cursor peer => LinkedCallback.ChildFrameOver older lhs rhs cursor peer ∧
        Core3.Grows start.store.core lhs.store.core ∧ lhs.ctl = cursor.control (checkNext (.ok value)) ∧ rhs.ctl = peer.control (canonNext value))
      (fun _ _ _ _ _ frame growth lhs rhs => ⟨frame, growth, lhs, rhs⟩) paired grew leftAt rightAt
    obtain ⟨store, verdict, effects, written, compared, continued⟩ := driveValueCommit publish tail
    cases compared with
    | inside _ nonempty residual => exact keep (.localPrefix nonempty residual)
    | reached used residual =>
      refine ⟨checked ++ effects, canonical ++ effects, _, _, _, [], by simp only [split, used, List.append_assoc],
        by rw [visibleAppend canonical effects, visibleAppend checked effects, seen],
        (CallbackPrefix.transportAppend move written).choose_spec.1, ?_, residual, ?_⟩
      · cases verdict <;> rfl
      · cases verdict with
        | error reason => exact .trap rfl rfl
        | ok value => exact .descriptor (pointer := pointer) ⟨value, continued value rfl⟩

open ABI PayloadPrefix Stored.Endpoints.RecordLower LinkedCallback.MemorySequence in
theorem driveNominalListBody (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
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
        (publishCanonical destination inst pointer entries.length output canonNext)) check canon start incoming labels finish := by
  intro area mode checkAt canonAt actual
  have valueMode : mode = .value := by cases output <;> rfl
  obtain ⟨checkElements, canonElements⟩ := CallbackRange.collectionElementFoci destination inst entries area mode output pointer index
    checkNext canonNext checkAt canonAt
  rw [valueMode] at canonElements
  have shapes := CallbackRange.listEntries matched
  have handles : ∀ item ∈ entries, CanonicalHandle item := by
    intro item member
    cases emitted with
    | list children => exact CallbackRange.nominalEntry nominal (entries_match_of_mem shapes member) (children item member)
  obtain ⟨checked, canonical, trailing, left, right, split, observed, same, movement, rest, ending⟩ :=
    driveNominalElements destination inst entries area.size pointer 0 handles frame checkElements canonElements actual
  have keep (ending : ElementRunEnd profile ready base
      (fun lhs rhs => ∃ value, LinkedCallback.ChildFrameOver older lhs rhs check canon ∧
        lhs.ctl = check.control (checkNext (.ok value)) ∧ rhs.ctl = canon.control (canonNext value))
      (fun issue lhs rhs => lhs.ctl = check.control (checkNext (.error issue)) ∧
        ∃ stop, ElementStop destination inst entries area.size pointer (publishCanonical destination inst pointer entries.length output canonNext) stop ∧
          rhs.ctl = canon.control stop) left right trailing finish) :
      AllocatedElementRun profile ready base bindings older checkNext canonNext
        (ElementStop destination inst entries area.size pointer (publishCanonical destination inst pointer entries.length output canonNext))
        check canon start incoming labels finish :=
    ⟨checked, canonical, trailing, left, right, split, observed, same, movement, rest, ending⟩
  cases ending with
  | inside nonempty tail => exact keep (.inside nonempty tail)
  | trapped checked canonical => exact keep (.trapped checked canonical)
  | refused issue stop => exact keep (.refused (.nested index issue) stop)
  | returned published =>
    obtain ⟨⟨⟩, frame, checkedAt, canonicalAt⟩ := published
    have commit := CallbackRange.livePublish (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst pointer entries.length output checkNext canonNext
      (fun value lhs rhs check canon => LinkedCallback.ChildFrameOver older lhs rhs check canon ∧
        lhs.ctl = check.control (checkNext (.ok value)) ∧ rhs.ctl = canon.control (canonNext value))
      (fun _ _ _ _ _ frame _ lhs rhs => ⟨frame, lhs, rhs⟩) frame (Core3.Grows.refl _) checkedAt canonicalAt
    obtain ⟨store, verdict, effects, written, aligned, continues⟩ := driveValueCommit commit rest
    cases aligned with
    | inside _ nonempty tail => exact keep (.inside nonempty tail)
    | reached used tail =>
      refine ⟨checked ++ effects, canonical ++ effects, _, _, _, by rw [split, used, List.append_assoc],
        by rw [visibleAppend, visibleAppend, observed], ?_, (CallbackPrefix.transportAppend movement written).choose_spec.1, tail, ?_⟩
      · cases verdict <;> rfl
      · cases verdict with
        | error reason => exact .trapped rfl rfl
        | ok value => exact .returned ⟨value, continues value rfl⟩

open PayloadPrefix in
private theorem prependElementSlice
    {success : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop}
    {refusal : Stored.Endpoints.RecordLower.Issue → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop}
    {left right : Config (core3 grow) (HostState sig)} {leading canonical trailing : Trace grow sig}
    (split : labels = leading ++ trailing) (seen : visible leading = visible canonical)
    (prefixTransport : OccurrenceTransport profile ready base bindings start incoming leading canonical left right)
    (body : ElementRunSlice profile ready base bindings success refusal left right trailing finish) :
    ElementRunSlice profile ready base bindings success refusal start incoming labels finish := by
  obtain ⟨checked, peer, residual, lhs, rhs, bodySplit, observed, same, movement, tail, ending⟩ := body
  refine ⟨leading ++ checked, canonical ++ peer, residual, lhs, rhs, ?_, ?_, same,
    (CallbackPrefix.transportAppend prefixTransport movement).choose_spec.1, tail, ending⟩
  · simp only [split, bodySplit, List.append_assoc]
  · rw [visibleAppend leading checked, visibleAppend canonical peer, seen, observed]

open ABI PayloadPrefix Stored.Endpoints.RecordLower LinkedCallback.MemorySequence in
theorem driveNominalListAfterRange (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
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
        (publishCanonical destination inst pointer entries.length output canonNext)) check canon start incoming labels finish := by
  intro area mode checkAt canonAt range
  obtain ⟨leftTail, rightTail, movement, silentLeft, silentRight, _, aligned⟩ := range
  cases aligned with
  | inside _ nonempty tail => exact .inl ⟨_, nonempty, tail⟩
  | reached used suffix =>
    have combined := split.trans (congrArg (checked ++ ·) used)
    have observed : visible (checked ++ leftTail) = visible (canonical ++ rightTail) := by
      rw [visibleAppend checked leftTail, visibleAppend canonical rightTail, seen, silentLeft, silentRight]
    exact .inr (prependElementSlice (combined.trans (List.append_assoc ..).symm) observed movement
      (driveNominalListBody destination inst element entries index pointer output nominal matched emitted
        checkNext canonNext frame checkAt canonAt suffix))

open ABI PayloadPrefix Stored.Endpoints.RecordLower LinkedCallback.MemorySequence in
theorem driveStringListAfterRange (destination : RecordDestination) (inst : InstId) (entries : List Field)
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
      start incoming labels finish := by
  intro element area mode aligned bounds checkAt canonAt range
  obtain ⟨rangeLeft, rangeRight, rangeMovement, silentLeft, silentRight, _, rangeRun⟩ := range
  cases rangeRun with
  | inside _ nonempty tail => exact .inl ⟨_, nonempty, tail⟩
  | @reached suffixLabels used suffix =>
    have shorter : suffixLabels.length ≤ budget := by
      rw [split, used, List.length_append, List.length_append] at bounded
      omega
    obtain ⟨checkBody, canonBody, residual, reached, peer, marks, bodySplit, observed, bodyMovement, same, tail, ending⟩ :=
      driveStringListBody destination inst entries index pointer bytes output rootLayout fits allocates path matched emitted embedder
        width sized checkNext canonNext frame aligned bounds checkAt canonAt suffix shorter compare
    refine .inr ⟨(checked ++ rangeLeft) ++ checkBody, (canonical ++ rangeRight) ++ canonBody, residual, reached, peer, marks,
      by simp only [split, used, bodySplit, List.append_assoc], ?_, ?_, same, tail, ?_⟩
    · simp only [visibleAppend, silentLeft, silentRight, List.append_nil, seen, observed]
    · simpa only [List.map_nil, List.append_nil] using (CallbackPrefix.transportAppend rangeMovement bodyMovement).choose_spec.1
    · cases ending with
      | trap lhs rhs => exact .trap lhs rhs
      | localPrefix nonempty residual => exact .localPrefix nonempty residual
      | localChoice split branch shared step residual => exact .localChoice split branch shared step residual
      | installPrefix short => exact .installPrefix short
      | collectionInstall short => exact .collectionInstall short
      | collectionRange nonempty tail => exact .collectionRange nonempty tail
      | callback tracked paired boundary noPop => exact .callback tracked paired boundary noPop
      | descriptor returned =>
        obtain ⟨value, paired, grew, checkAt, canonAt⟩ := returned
        exact .descriptor (pointer := pointer) ⟨value, paired, grown.trans grew, checkAt, canonAt⟩

open PayloadPrefix LinkedCallback.MemorySequence in
private theorem prependValueVisit {origin : CStore (core3 grow)} {valueType : Type}
    {pending : Config (core3 grow) (HostState sig) → Prop}
    {checkNext : Except Stored.Endpoints.RecordLower.Issue valueType → Session grow sig (Ret (core3 grow))}
    {canonNext : valueType → Session grow sig (Ret (core3 grow))}
    {left right : Config (core3 grow) (HostState sig)} {checked canonical trailing : Trace grow sig}
    (split : labels = checked ++ trailing) (seen : visible checked = visible canonical)
    (prefixPath : OccurrenceTransport profile ready base bindings start incoming checked canonical left right)
    (body : ValueVisitRun profile ready base bindings older origin valueType pending checkNext canonNext left right trailing finish) :
    ValueVisitRun profile ready base bindings older origin valueType pending checkNext canonNext start incoming labels finish := by
  obtain ⟨bodyChecks, bodyCanon, suffix, lhs, rhs, marks, used, observed, same, movement, actual, ending⟩ := body
  refine ⟨checked ++ bodyChecks, canonical ++ bodyCanon, suffix, lhs, rhs, marks, ?_, ?_, same, ?_, actual, ending⟩
  · simp only [split, used, List.append_assoc]
  · rw [visibleAppend checked bodyChecks, visibleAppend canonical bodyCanon, seen, observed]
  · simpa only [List.map_nil, List.append_nil] using (CallbackPrefix.transportAppend prefixPath movement).choose_spec.1

open PayloadPrefix LinkedCallback.MemorySequence in
private theorem prependMemoryVisit {origin : CStore (core3 grow)} {destination : RecordDestination} {inst : InstId}
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig}
    {left right : Config (core3 grow) (HostState sig)} {checked canonical trailing : Trace grow sig}
    (split : labels = checked ++ trailing) (seen : visible checked = visible canonical)
    (prefixPath : OccurrenceTransport profile ready base bindings start incoming checked canonical left right)
    (body : MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext left right trailing finish) :
    MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext start incoming labels finish :=
  prependValueVisit split seen prefixPath body

open PayloadPrefix LinkedCallback.MemorySequence in
private theorem stationaryMemoryVisit {origin : CStore (core3 grow)} {destination : RecordDestination} {inst : InstId}
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig}
    (same : start.store = incoming.store) (actual : Steps profile ready (specDispatch ready base) start labels finish)
    (boundary : StringSliceEnd profile ready base bindings older (fun _ _ _ _ _ => False) start incoming labels finish []) :
    MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext start incoming labels finish :=
  ⟨[], [], labels, start, incoming, [], rfl, rfl, same,
    CallbackPrefix.stationaryTransport (fun place => .done start place) (fun place => .done incoming place), actual, .boundary boundary⟩

open PayloadPrefix ReturnFrame.Occurrence Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
private theorem driveMemoryHandle {origin : CStore (core3 grow)} (destination : RecordDestination) (inst : InstId)
    (item : Field) (handle : CanonicalHandle item) (index address : Nat)
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon) (growth : Core3.Grows origin.core start.store.core)
    (checkAt : start.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
      destination.width item index (.memory address) >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
      destination.width item (.memory address) >>= canonNext))
    (actual : Steps profile ready (specDispatch ready base) start labels finish) :
    MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext start incoming labels finish := by
  have leaf := LinkedCallback.ChildFrameOver.handle_field_then_between
    (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst item handle index (.memory address)
    checkNext canonNext frame growth checkAt canonAt (next := fun value lhs rhs check canon =>
      LinkedCallback.ChildFrameOver older lhs rhs check canon ∧ Core3.Grows origin.core lhs.store.core ∧
        lhs.ctl = check.control (checkNext (.ok value)) ∧ rhs.ctl = canon.control (canonNext value))
    (fun _ _ _ _ _ paired grew left right => ⟨paired, grew, left, right⟩)
  unfold LinkedCallback.HandleFieldThenBetween at leaf
  cases decision : liveLeafPlan start.store start.host.writer index item with
  | error issue =>
    rw [decision] at leaf
    obtain ⟨guard, tau, tracks⟩ := leaf
    have quiet : visible guard = [] := silentVisible (List.all_eq_true.mpr (fun action member => by rw [tau action member]))
    cases alignLocalBody (prefix_survives (tracks (.active 0 0))).1 actual (noBranchOfVisible quiet (by simp)) with
    | inside _ nonempty tail => exact stationaryMemoryVisit frame.store actual (.localPrefix nonempty tail)
    | reached split tail =>
      exact ⟨guard, [], _, { start with ctl := check.control (checkNext (.error issue)) }, incoming, [], split, quiet, frame.store,
        CallbackPrefix.stationaryTransport tracks (fun place => .done incoming place), tail,
        .refused issue check rfl (.field canon item address canonNext canonAt)⟩
  | ok plan =>
    rw [decision] at leaf
    obtain ⟨store, verdict, guard, checkLabels, canonLabels, tau, leftKind, rightKind, checkRun, _, tracks, continued⟩ := leaf
    have quiet : visible guard = [] := silentVisible (List.all_eq_true.mpr (fun action member => by rw [tau action member]))
    have observed : visible (guard ++ checkLabels) = visible canonLabels := by
      rw [visibleAppend, quiet, List.nil_append, CallbackPrefix.visibleLeaf leftKind, CallbackPrefix.visibleLeaf rightKind]
      cases verdict <;> rfl
    have localOnly : ∀ action ∈ visible canonLabels, ¬ workerBranchLabel action := by
      rw [CallbackPrefix.visibleLeaf rightKind]
      cases verdict <;> simp [workerBranchLabel]
    cases alignLocalBody checkRun actual (noBranchOfVisible observed localOnly) with
    | inside _ nonempty tail => exact stationaryMemoryVisit frame.store actual (.localPrefix nonempty tail)
    | reached split tail =>
      refine ⟨guard ++ checkLabels, canonLabels, _, _, _, [], split, observed, ?_,
        CallbackPrefix.localLeafTransport tracks, tail, ?_⟩
      · cases verdict <;> rfl
      · cases verdict with
        | error reason => exact .boundary (.trap rfl rfl)
        | ok value =>
          cases value
          obtain ⟨_, _, paired, grew, checked, canonical⟩ := continued () rfl
          exact .returned check canon paired grew checked canonical

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
private theorem driveMemoryScalar {origin : CStore (core3 grow)} (destination : RecordDestination) (inst : InstId)
    (type : Stored.TypeOf) (data : LocalDataType type) (payload : Stored.Payload type) (index address : Nat)
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon) (growth : Core3.Grows origin.core start.store.core)
    (width : (core3 grow).memAddrType? start.store.core destination.memory = some destination.width)
    (placed : placement destination start.store (layout destination.width type) address = .ok ())
    (checkAt : start.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
      destination.width (.data type payload) index (.memory address) >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
      destination.width (.data type payload) (.memory address) >>= canonNext))
    (actual : Steps profile ready (specDispatch ready base) start labels finish) :
    MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext start incoming labels finish := by
  obtain ⟨store, result, checked, canonical, lhs, _, observed, cut, trails⟩ :=
    local_data_leaf_frame_between (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
      (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst type data payload index
      (.memory address) origin start incoming (frame.store ▸ growth)
      (by simp [ptrTypeIn, CanonOpts.ptrType, RecordDestination.context, width]) placed
      (trackOccurrences := true) frame.store check canon frame.thread checkNext canonNext checkAt canonAt
  cases alignWorkerBody lhs actual with
  | inside _ nonempty tail => exact stationaryMemoryVisit frame.store actual (.localPrefix nonempty tail)
  | departure _ split shared _ branch _ _ step tail =>
    exact stationaryMemoryVisit frame.store actual (.localChoice split branch.2 shared step tail)
  | reached split tail =>
    refine ⟨checked, canonical, _, _, _, [], split, observed, ?_, CallbackPrefix.localLeafTransport trails, tail, ?_⟩
    · cases result <;> rfl
    · cases result with
      | error reason => exact .boundary (.trap rfl rfl)
      | ok value =>
        cases value
        exact .returned check canon
          ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩ cut.1 rfl rfl

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
private theorem driveMemoryString {origin : CStore (core3 grow)} (destination : RecordDestination) (inst : InstId)
    {item root : Field} {schema : Stored.TypeOf} {budget : Nat} (index address : Nat)
    (rootLayout : root.LayoutMatches schema)
    (fits : Stored.Lower.fits Quirks.none destination.encoding destination.width schema root.value = true)
    (allocates : Field.AllocatorFor destination.realloc root) (path : root.Descendant item)
    (matched : item.LayoutMatches (.prim .string)) (emitted : item.Emitted)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon) (growth : Core3.Grows origin.core start.store.core)
    (width : (core3 grow).memAddrType? start.store.core destination.memory = some destination.width)
    (placed : placement destination start.store (layout destination.width (.prim .string : Stored.TypeOf)) address = .ok ())
    (checkAt : start.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
      destination.width item index (.memory address) >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
      destination.width item (.memory address) >>= canonNext))
    (actual : Steps profile ready (specDispatch ready base) start labels finish)
    (bounded : labels.length ≤ budget) (compare : ShorterCallbackSlices profile ready base bindings budget) :
    MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext start incoming labels finish := by
  obtain ⟨str, field⟩ := CallbackRange.compiledStringCommit destination inst (.memory address) rootLayout fits allocates path
    matched emitted embedder frame width placed checkAt canonAt
  obtain ⟨checked, canonical, trailing, lhs, rhs, marks, split, observed, movement, same, rest, ending⟩ :=
    driveStringCommit field actual bounded compare
  refine ⟨checked, canonical, trailing, lhs, rhs, marks, split, observed.symm, same, movement, rest, ?_⟩
  cases ending with
  | trap left right => exact .boundary (.trap left right)
  | localPrefix nonempty tail => exact .boundary (.localPrefix nonempty tail)
  | localChoice split choice shared step tail => exact .boundary (.localChoice split choice shared step tail)
  | installPrefix short => exact .boundary (.installPrefix short)
  | collectionInstall short => exact .collectionInstall short
  | collectionRange nonempty tail => exact .collectionRange nonempty tail
  | callback tracked paired ending noPop => exact .boundary (.callback tracked paired ending noPop)
  | descriptor returned =>
    obtain ⟨⟨⟩, paired, grew, checked, canonical⟩ := returned
    exact .returned _ _ paired (growth.trans grew) checked canonical

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
private theorem driveMemorySequence {origin : CStore (core3 grow)} (mode : Track)
    (destination : RecordDestination) (inst : InstId) (items : List Field) (index cursor : Nat) {budget : Nat}
    (slots : mode.Slots destination.width (MemoryVisitField profile ready base bindings older origin destination inst budget) items cursor)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon) (growth : Core3.Grows origin.core start.store.core)
    (checkAt : start.ctl = check.control (mode.checked destination inst items index cursor >>= checkNext))
    (canonAt : incoming.ctl = canon.control (mode.canonical destination inst items cursor >>= canonNext))
    (actual : Steps profile ready (specDispatch ready base) start labels finish) (bounded : labels.length ≤ budget) :
    MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext start incoming labels finish := by
  induction items generalizing index cursor start incoming check canon labels with
  | nil =>
    have checked : start.ctl = check.control (checkNext (.ok ())) := by
      cases mode <;> simpa only [Track.checked, Record.Effects.memory, Record.Effects.elements, Prog.bind_eq, Prog.pure_eq,
        Prog.pure_bind'] using checkAt
    have canonical : incoming.ctl = canon.control (canonNext ()) := by
      cases mode <;> simpa only [Track.canonical, canonicalPlacedFields, CanonicalTree.memory, CanonicalTree.elements, Prog.bind_eq,
        Prog.pure_eq, Prog.pure_bind'] using canonAt
    exact ⟨[], [], labels, start, incoming, [], rfl, rfl, frame.store,
      CallbackPrefix.stationaryTransport (fun place => .done start place) (fun place => .done incoming place), actual,
      .returned check canon frame growth checked canonical⟩
  | cons item rest ih =>
    let slot := mode.slot destination.width item cursor
    let nextCheck := checkTail mode destination inst rest (index + 1) slot.2 checkNext
    let nextCanon := canonTail mode destination inst rest slot.2 canonNext
    let focused := focus mode destination inst item cursor incoming canon nextCanon
    have headAt : start.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item index (.memory slot.1) >>= nextCheck) := by
      rw [checkAt]
      congr 1
      cases mode <;> simp only [Track.checked, Record.Effects.memory, Record.Effects.elements, Prog.bind_eq, Prog.bind_assoc]
      all_goals
        congr 1
        funext verdict
        cases verdict with
        | error issue => rfl
        | ok result => cases result; rfl
    have canonEntry := Track.focus_prefix (profile := profile) (ready := ready) (dispatch := specDispatch ready (LiveDispatch.host bindings base))
      mode destination inst item rest cursor canonNext incoming canon (frame.store ▸ growth.memAddrType width) canonAt
    have paired : LinkedCallback.ChildFrameOver older start focused check canon :=
      ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
    have leaves : MemoryVisitField profile ready base bindings older origin destination inst budget item slot.1 ∧
        mode.Slots destination.width (MemoryVisitField profile ready base bindings older origin destination inst budget) rest slot.2 := slots
    have body : MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext start focused labels finish := by
      obtain ⟨checked, canonical, trailing, lhs, rhs, marks, split, observed, same, movement, tail, ending⟩ :=
        leaves.1 index nextCheck nextCanon start focused check canon paired growth headAt rfl labels finish actual bounded
      cases ending with
      | refused issue check atRefusal pending =>
        exact ⟨checked, canonical, trailing, lhs, rhs, [], split, observed, same, movement, tail, .refused issue check atRefusal pending⟩
      | boundary stopped =>
        exact ⟨checked, canonical, trailing, lhs, rhs, _, split, observed, same, movement, tail, .boundary stopped⟩
      | collectionInstall short =>
        exact ⟨checked, canonical, trailing, lhs, rhs, [], split, observed, same, movement, tail, .collectionInstall short⟩
      | collectionRange nonempty remainder =>
        exact ⟨checked, canonical, trailing, lhs, rhs, _, split, observed, same, movement, tail, .collectionRange nonempty remainder⟩
      | returned check canon related grew checkedAt canonicalAt =>
        have remaining : trailing.length ≤ budget := by rw [split, List.length_append] at bounded; omega
        exact prependMemoryVisit split observed movement
          (ih (index + 1) slot.2 leaves.2 related grew checkedAt canonicalAt tail remaining)
    exact prependMemoryVisit (checked := []) (canonical := mode.readLabels) rfl (by cases mode <;> rfl)
      (CallbackPrefix.stationaryTransport (fun place => .done start place) canonEntry) body

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
private theorem wrapMemoryVisit {origin : CStore (core3 grow)} {destination : RecordDestination} {inst : InstId}
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} (index : Nat)
    (body : MemoryVisitRun profile ready base bindings older origin destination inst (aggregateNext index checkNext)
      canonNext start incoming labels finish) :
    MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext start incoming labels finish := by
  obtain ⟨checked, canonical, residual, lhs, rhs, marks, split, observed, same, movement, tail, ending⟩ := body
  refine ⟨checked, canonical, residual, lhs, rhs, marks, split, observed, same, movement, tail, ?_⟩
  cases ending with
  | returned check canon frame growth checked canonical => exact .returned check canon frame growth checked canonical
  | refused issue check checked pending => exact .refused (.nested index issue) check checked pending
  | boundary stopped => exact .boundary stopped
  | collectionInstall short => exact .collectionInstall short
  | collectionRange nonempty remainder => exact .collectionRange nonempty remainder

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
theorem compiledSumVisitShape {type : Stored.TypeOf} {arms : List (Option Stored.TypeOf)} {tag : Nat} {selected : Option Field}
    (matched : Field.LayoutMatches (.sum type arms tag selected) type)
    (children : ∀ item, selected = some item → MemoryVisitShape item) : MemoryVisitShape (.sum type arms tag selected) := by
  have member {item : Field} {arm : Option Stored.TypeOf} {arms : List (Option Stored.TypeOf)}
      (matching : Field.ArmMatches (some item) arm) (listed : arm ∈ arms) : some item.type ∈ arms := by
    cases matching with
    | some matching => simpa only [matching.type_eq] using listed
  apply MemoryVisitShape.sum _ _ children
  · intro width
    cases matched with
    | @variant types _ _ _ _ _ =>
      rw [layout, CallbackRange.variantLayouts]
    | optionNone | optionSome => simp only [layout, List.map_cons, List.map_nil, layoutOption]
    | resultOk | resultError => simp only [layout, List.map_cons, List.map_nil]
  · intro item active
    cases matched with
    | variant found matching => exact member (active ▸ matching) (List.mem_of_getElem? found)
    | optionNone => cases active
    | optionSome matching => cases active; simp only [matching.type_eq, List.mem_cons, true_or, or_true]
    | resultOk matching => exact member (active ▸ matching) (by simp)
    | resultError matching => exact member (active ▸ matching) (by simp)

open ABI PayloadPrefix Stored.Endpoints.RecordLower in
private theorem compiledVisitShapes {item : Field} (emitted : item.Emitted) {schema : Stored.TypeOf}
    (matched : item.LayoutMatches schema) : FlatVisitShape item ∧ MemoryVisitShape item := by
  have primitiveShapes {primitive : WIT.Primitive} (payload : Stored.Payload (.prim primitive)) :
      FlatVisitShape (.data (.prim primitive) payload) ∧ MemoryVisitShape (.data (.prim primitive) payload) := by
    by_cases string : primitive = .string
    · subst primitive
      exact ⟨.string _ (.data payload) (.primitive payload), .string (.data payload) (.primitive payload)⟩
    · exact ⟨.scalar _ (.primitive string) payload, .scalar (.primitive string)⟩
  have fieldOfMember {fields : List Field} {types : List Stored.TypeOf} (matching : Field.FieldsMatch fields types)
      {child : Field} (member : child ∈ fields) : ∃ type, child.LayoutMatches type := by
    induction fields generalizing types with
    | nil => simp at member
    | cons field rest ih =>
      cases matching with
      | cons head tail =>
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨_, head⟩
        · exact ih tail later
  have atArm {selected : Option Field} {arm : Option Stored.TypeOf} (matching : Field.ArmMatches selected arm)
      {child : Field} (active : selected = some child) : ∃ type, child.LayoutMatches type := by
    cases active
    cases matching with
    | some layout => exact ⟨_, layout⟩
  induction emitted generalizing schema with
  | primitive payload => exact primitiveShapes payload
  | enum payload schemaOk => exact ⟨.scalar _ (.enum schemaOk) payload, .scalar (.enum schemaOk)⟩
  | flags payload schemaOk => exact ⟨.scalar _ (.flags schemaOk) payload, .scalar (.flags schemaOk)⟩
  | endpoint => exact ⟨.handle _ trivial, .handle trivial⟩
  | context => exact ⟨.handle _ trivial, .handle trivial⟩
  | owner => exact ⟨.handle _ trivial, .handle trivial⟩
  | @aggregate type fields _ ih =>
    have typed : type = schema := matched.type_eq
    subst schema
    have children (child : Field) (member : child ∈ fields) : FlatVisitShape child ∧ MemoryVisitShape child := by
      have occurs : ∃ type, child.LayoutMatches type := by
        cases matched with
        | record fields | tuple fields => exact fieldOfMember fields member
      obtain ⟨_, found⟩ := occurs
      exact ih child member found
    exact ⟨.aggregate type fields (fun child member => (children child member).1),
      .aggregate matched (fun child member => (children child member).2)⟩
  | @fixed element length entries _ ih =>
    cases matched with
    | fixed count matching =>
      exact ⟨.fixed element length entries (fun child member => (ih child member (entries_match_of_mem matching member)).1),
        .fixed count matching (fun child member => (ih child member (entries_match_of_mem matching member)).2)⟩
  | @list element entries _ ih =>
    cases matched with
    | list matching =>
      have children := fun child member => (ih child member (entries_match_of_mem matching member)).2
      exact ⟨.collection (.list element) element entries matching children, .list matching children⟩
  | @map key element entries pairs emittedValues ih =>
    cases matched with
    | map matching =>
      let entryType : Stored.TypeOf := .record (mapEntryFields key element)
      have pairShapes (payload : Stored.Payload (.prim key.toPrimitive)) (value : Field)
          (member : Field.aggregate entryType [.data (.prim key.toPrimitive) payload, value] ∈ entries) :
          ∀ child ∈ [Field.data (.prim key.toPrimitive) payload, value], MemoryVisitShape child := by
        intro child present
        rcases List.mem_cons.mp present with rfl | later
        · exact (primitiveShapes payload).2
        · have same := List.mem_singleton.mp later
          subst child
          have entry : Field.LayoutMatches
              (.aggregate (.record (mapEntryFields key element)) [.data (.prim key.toPrimitive) payload, value])
              (.record (mapEntryFields key element)) := entries_match_of_mem matching member
          cases entry with
          | record fields =>
            obtain ⟨_, valueLayout⟩ := fieldOfMember fields (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            exact (ih payload value member valueLayout).2
      refine ⟨.collection (.map key element) entryType entries matching ?_, .map matching (.map pairs emittedValues) ?_⟩
      · intro entry member
        obtain ⟨payload, value, rfl⟩ := pairs entry member
        exact .aggregate (entries_match_of_mem matching member) (pairShapes payload value member)
      · intro keyField value member
        obtain ⟨payload, compiledValue, equal⟩ := pairs _ member
        have fields := (List.cons.inj (Field.aggregate.inj equal).2)
        have keyEqual := fields.1
        have valueEqual := (List.cons.inj fields.2).1
        subst keyField
        subst value
        exact pairShapes payload compiledValue member
  | @sum type arms tag selected _ ih =>
    have typed : type = schema := matched.type_eq
    subst schema
    have children (child : Field) (active : selected = some child) : FlatVisitShape child ∧ MemoryVisitShape child := by
      have occurs : ∃ type, child.LayoutMatches type := by
        cases matched with
        | variant _ matching => exact atArm matching active
        | optionNone => cases active
        | optionSome matching => cases active; exact ⟨_, matching⟩
        | resultOk matching | resultError matching => exact atArm matching active
      obtain ⟨_, found⟩ := occurs
      exact ih child active found
    exact ⟨.sum type arms tag selected matched (fun child active => (children child active).1),
      compiledSumVisitShape matched (fun child active => (children child active).2)⟩

open Stored.OwnedMemory.Claims in
private theorem siteVisitShapes {giveRoute : GiveEffectRoute} {site : PayloadRoot.Site grow sig giveRoute}
    (linked : site.Linked bindings) : FlatVisitShape site.field ∧ MemoryVisitShape site.field := by
  obtain ⟨_, preflight⟩ := linked.compiled
  exact compiledVisitShapes linked.emitted (Record.preflightValue_layout _ _ _ _ _ _ preflight)

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
private theorem driveCollectionPublish {origin visited : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (index pointer count : Nat) (output : Stored.Lower.Output)
    {checkNext : ValueCheckNext grow sig output} {canonNext : ValueCanonNext grow sig output}
    {pending : Config (core3 grow) (HostState sig) → Prop}
    (atChild : ∀ right, PendingMemoryField destination inst right → pending right)
    (growth : Core3.Grows origin.core visited.core)
    (body : MemoryVisitRun profile ready base bindings older visited destination inst
      (publishChecked destination inst pointer count index output checkNext)
      (publishCanonical destination inst pointer count output canonNext) start incoming labels finish) :
    ValueVisitRun profile ready base bindings older origin output.Result pending checkNext canonNext start incoming labels finish := by
  obtain ⟨checked, canonical, trailing, lhs, rhs, marks, split, seen, movementStore, movement, tail, ending⟩ := body
  cases ending with
  | refused issue check checkedAt pending =>
    exact ⟨checked, canonical, trailing, lhs, rhs, [], split, seen, movementStore, movement, tail,
      .refused (.nested index issue) check checkedAt (atChild _ pending)⟩
  | boundary stopped => exact ⟨checked, canonical, trailing, lhs, rhs, marks, split, seen, movementStore, movement, tail, .boundary stopped⟩
  | collectionInstall short =>
    exact ⟨checked, canonical, trailing, lhs, rhs, [], split, seen, movementStore, movement, tail, .collectionInstall short⟩
  | collectionRange nonempty residual =>
    exact ⟨checked, canonical, trailing, lhs, rhs, _, split, seen, movementStore, movement, tail, .collectionRange nonempty residual⟩
  | returned check canon paired grew checkedAt canonicalAt =>
    have publish := CallbackRange.livePublish (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst pointer count output checkNext canonNext
      (fun value lhs rhs cursor peer => LinkedCallback.ChildFrameOver older lhs rhs cursor peer ∧
        Core3.Grows origin.core lhs.store.core ∧ lhs.ctl = cursor.control (checkNext (.ok value)) ∧ rhs.ctl = peer.control (canonNext value))
      (fun _ _ _ _ _ frame growth lhs rhs => ⟨frame, growth, lhs, rhs⟩) paired (growth.trans grew) checkedAt canonicalAt
    obtain ⟨store, verdict, effects, written, aligned, continued⟩ := driveValueCommit publish tail
    cases aligned with
    | inside _ nonempty residual =>
      exact ⟨checked, canonical, trailing, lhs, rhs, [], split, seen, movementStore, movement, tail, .boundary (.localPrefix nonempty residual)⟩
    | @reached residual used remainder =>
      have exactPublication : ValueVisitRun profile ready base bindings older origin output.Result pending checkNext canonNext lhs rhs trailing finish := by
        let leftEnd := localLeafEnd lhs lhs.host store check.thread check.frames check.rest (fun value => checkNext (.ok value)) verdict
        let rightEnd := localLeafEnd rhs rhs.host store canon.thread canon.frames canon.rest canonNext verdict
        refine ⟨effects, effects, residual, leftEnd, rightEnd, [], used, rfl, ?_, written, remainder, ?_⟩
        · cases verdict <;> rfl
        · cases verdict with
          | error reason => exact .boundary (.trap rfl rfl)
          | ok value =>
            obtain ⟨frame, growth, checkedAt, canonicalAt⟩ := continued value rfl
            exact .returned check canon frame growth checkedAt canonicalAt
      exact prependValueVisit split seen movement exactPublication

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
private theorem driveMemoryPublish {origin visited : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (index pointer address count : Nat)
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} (growth : Core3.Grows origin.core visited.core)
    (body : MemoryVisitRun profile ready base bindings older visited destination inst
      (publishChecked destination inst pointer count index (.memory address) checkNext)
      (publishCanonical destination inst pointer count (.memory address) canonNext) start incoming labels finish) :
    MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext start incoming labels finish :=
  driveCollectionPublish destination inst index pointer count (.memory address) (fun _ evidence => evidence) growth body

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
private theorem driveMemoryElements {origin : CStore (core3 grow)} {budget bytes : Nat}
    (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf) (entries : List Field) (index pointer address : Nat)
    (matching : Field.EntriesMatch entries element)
    (children : ∀ item ∈ entries, ∀ slot, SlotFits destination.width bytes item slot →
      MemoryVisitField profile ready base bindings older start.store destination inst budget item slot)
    (width : (core3 grow).memAddrType? start.store.core destination.memory = some destination.width)
    (aligned : pointer = alignTo pointer (layout destination.width element).alignment)
    (bounds : pointer + entries.length * (layout destination.width element).size ≤ bytes)
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon) (growth : Core3.Grows origin.core start.store.core)
    (checkAt : start.ctl = check.control (checkedCollectionTail destination inst entries (layout destination.width element)
      index (.memory address) pointer (.ok ()) >>= checkNext))
    (canonAt : incoming.ctl = canon.control (canonicalCollectionTail destination inst entries (layout destination.width element)
      (.memory address) pointer .value >>= canonNext))
    (actual : Steps profile ready (specDispatch ready base) start labels finish)
    (bounded : labels.length ≤ budget) :
    MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext start incoming labels finish := by
  let area := layout destination.width element
  have slots := Track.elements_slots destination.width matching aligned bounds
    (MemoryVisitField profile ready base bindings older start.store destination inst budget) children
  obtain ⟨leftAt, rightAt⟩ := CallbackRange.collectionElementFoci destination inst entries area .value (.memory address) pointer index
    checkNext canonNext checkAt canonAt
  exact driveMemoryPublish destination inst index pointer address entries.length growth
    (driveMemorySequence (.elements area.size) destination inst entries 0 pointer slots width frame (Core3.Grows.refl _)
      leftAt rightAt actual bounded)

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
private theorem driveMemoryMapEntries {origin : CStore (core3 grow)} {budget bytes : Nat}
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (items : List Field) (index address : Nat)
    (matching : Field.EntriesMatch items (.record (mapEntryFields key element)))
    (pairs : ∀ item ∈ items, ∃ keyField value, item = .aggregate (.record (mapEntryFields key element)) [keyField, value])
    (children : ∀ keyField value, Field.aggregate (.record (mapEntryFields key element)) [keyField, value] ∈ items →
      ∀ child ∈ [keyField, value], ∀ slot, SlotFits destination.width bytes child slot →
        MemoryVisitField profile ready base bindings older origin destination inst budget child slot)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (slots : (Track.elements (layout destination.width (.record (mapEntryFields key element))).size).Slots destination.width
      (SlotFits destination.width bytes) items address)
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon) (growth : Core3.Grows origin.core start.store.core)
    (checkAt : start.ctl = check.control (Record.Effects.elements recordClaims Limits.spec Quirks.none (destination.context inst)
      destination.width items (layout destination.width (.record (mapEntryFields key element))).size address index >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none (destination.context inst) destination.width
      items (.memoryMap destination.width key element) (layout destination.width (.record (mapEntryFields key element))).size address >>= canonNext))
    (actual : Steps profile ready (specDispatch ready base) start labels finish) (bounded : labels.length ≤ budget) :
    MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext start incoming labels finish := by
  let type : Stored.TypeOf := .record (mapEntryFields key element)
  let stride := (layout destination.width type).size
  induction items generalizing index address start incoming check canon labels with
  | nil =>
    exact ⟨[], [], labels, start, incoming, [], rfl, rfl, frame.store,
      CallbackPrefix.stationaryTransport (fun place => .done start place) (fun place => .done incoming place), actual,
      .returned check canon frame growth
        (by simpa only [Record.Effects.elements, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind'] using checkAt)
        (by simpa only [CanonicalTree.elements, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind'] using canonAt)⟩
  | cons item rest ih =>
    obtain ⟨keyField, value, rfl⟩ := pairs item (.head _)
    cases matching with
    | cons matched restMatch =>
      let afterCheck := checkTail (.elements stride) destination inst rest (index + 1) (address + stride) checkNext
      let afterCanon : CanonNext grow sig := fun () => CanonicalTree.elements Limits.spec Quirks.none (destination.context inst)
        destination.width rest (.memoryMap destination.width key element) stride (address + stride) >>= canonNext
      have headAt : start.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
          destination.width (.aggregate type [keyField, value]) index (.memory address) >>= afterCheck) := by
        rw [checkAt, Record.Effects.elements]
        congr 1
        simp only [Prog.bind_eq, Prog.bind_assoc]
        congr 1
        funext verdict
        cases verdict with
        | error _ => rfl
        | ok result => cases result; rfl
      have fits : SlotFits destination.width bytes (.aggregate type [keyField, value]) address ∧
          (Track.elements stride).Slots destination.width (SlotFits destination.width bytes) rest (address + stride) := slots
      let entered := enterAggregate destination inst [keyField, value] index address start check afterCheck
      have guard := aggregate_entry_prefix (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
        destination inst type [keyField, value] index address start check afterCheck growth sized fits.1.1 fits.1.2 headAt
      cases alignLocalBody (guard (.active 0 0)).toTrail.steps actual (by simp [workerBranchLabel]) with
      | inside _ nonempty tail => exact stationaryMemoryVisit frame.store actual (.localPrefix nonempty tail)
      | @reached remaining guardSplit guardTail =>
        have remainingBudget : remaining.length ≤ budget := by rw [guardSplit, List.length_append] at bounded; omega
        have childSlots := Track.fields_slots destination.width matched fits.1.1 fits.1.2
          (MemoryVisitField profile ready base bindings older origin destination inst budget)
          (children keyField value (.head _))
        have placedSlots : Track.placedFields.Slots destination.width
            (MemoryVisitField profile ready base bindings older origin destination inst budget) [keyField, value] address := childSlots
        have paired : LinkedCallback.ChildFrameOver older entered incoming check canon :=
          ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
        have headCanon : incoming.ctl = canon.control (Track.placedFields.canonical destination inst [keyField, value] address >>= afterCanon) := by
          rw [canonAt]
          congr 1
          simp only [CanonicalTree.elements, Track.canonical, canonicalPlacedFields, Track.slot, Prog.bind_eq, Prog.bind_assoc,
            Prog.pure_eq, Prog.pure_bind', afterCanon, stride, type]
          let keyPtr := alignTo address (layout destination.width keyField.type).alignment
          let valuePtr := alignTo (keyPtr + (layout destination.width keyField.type).size) (layout destination.width value.type).alignment
          let keyProgram : Session grow sig Unit := CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
            destination.width keyField (.memory keyPtr)
          let valueProgram : Session grow sig Unit := CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
            destination.width value (.memory valuePtr)
          let restProgram : Session grow sig Unit := CanonicalTree.elements Limits.spec Quirks.none (destination.context inst)
            destination.width rest (.memoryMap destination.width key element) stride (address + stride)
          change (keyProgram.bind (fun _ => valueProgram.bind (fun _ => restProgram))).bind canonNext =
            keyProgram.bind (fun _ => valueProgram.bind (fun _ => restProgram.bind canonNext))
          simp only [Prog.bind_assoc]
        have body := wrapMemoryVisit index (driveMemorySequence .placedFields destination inst [keyField, value] 0 address
          placedSlots width paired growth rfl headCanon guardTail remainingBudget)
        obtain ⟨checked, canonical, residual, lhs, rhs, marks, split, seen, same, movement, tail, ending⟩ := body
        have next : MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext entered incoming remaining finish := by
          cases ending with
          | refused issue check checkedAt pending =>
            exact ⟨checked, canonical, residual, lhs, rhs, [], split, seen, same, movement, tail, .refused issue check checkedAt pending⟩
          | boundary stopped => exact ⟨checked, canonical, residual, lhs, rhs, marks, split, seen, same, movement, tail, .boundary stopped⟩
          | collectionInstall short =>
            exact ⟨checked, canonical, residual, lhs, rhs, [], split, seen, same, movement, tail, .collectionInstall short⟩
          | collectionRange nonempty suffix =>
            exact ⟨checked, canonical, residual, lhs, rhs, _, split, seen, same, movement, tail, .collectionRange nonempty suffix⟩
          | returned check canon frame grew checkedAt canonicalAt =>
            have budgetAt : residual.length ≤ budget := by rw [split, List.length_append] at remainingBudget; omega
            exact prependMemoryVisit split seen movement
              (ih (index + 1) (address + stride) restMatch (fun item member => pairs item (.tail _ member))
                (fun keyField value member => children keyField value (.tail _ member)) fits.2 frame grew checkedAt canonicalAt tail budgetAt)
        exact prependMemoryVisit (canonical := []) guardSplit rfl
          (CallbackPrefix.stationaryTransport guard (fun place => .done incoming place)) next

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
private theorem driveMemoryMap {origin : CStore (core3 grow)} {budget bytes : Nat}
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf) (entries : List Field)
    (index pointer address : Nat) (matching : Field.EntriesMatch entries (.record (mapEntryFields key element)))
    (pairs : ∀ item ∈ entries, ∃ keyField value, item = .aggregate (.record (mapEntryFields key element)) [keyField, value])
    (children : ∀ keyField value, Field.aggregate (.record (mapEntryFields key element)) [keyField, value] ∈ entries →
      ∀ child ∈ [keyField, value], ∀ slot, SlotFits destination.width bytes child slot →
        MemoryVisitField profile ready base bindings older start.store destination inst budget child slot)
    (width : (core3 grow).memAddrType? start.store.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? start.store.core destination.memory = some bytes)
    (aligned : pointer = alignTo pointer (layout destination.width (.record (mapEntryFields key element))).alignment)
    (bounds : pointer + entries.length * (layout destination.width (.record (mapEntryFields key element))).size ≤ bytes)
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon) (growth : Core3.Grows origin.core start.store.core)
    (checkAt : start.ctl = check.control (checkedCollectionTail destination inst entries (layout destination.width (.record (mapEntryFields key element)))
      index (.memory address) pointer (.ok ()) >>= checkNext))
    (canonAt : incoming.ctl = canon.control (canonicalCollectionTail destination inst entries (layout destination.width (.record (mapEntryFields key element)))
      (.memory address) pointer (.memoryMap destination.width key element) >>= canonNext))
    (actual : Steps profile ready (specDispatch ready base) start labels finish) (bounded : labels.length ≤ budget) :
    MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext start incoming labels finish := by
  let area := layout destination.width (.record (mapEntryFields key element))
  let mode := CanonicalTree.EntryMode.memoryMap destination.width key element
  have slots := Track.elements_slots destination.width matching aligned bounds (SlotFits destination.width bytes) (fun _ _ _ fits => fits)
  obtain ⟨leftAt, rightAt⟩ := CallbackRange.collectionElementFoci destination inst entries area mode (.memory address) pointer index
    checkNext canonNext checkAt canonAt
  exact driveMemoryPublish destination inst index pointer address entries.length growth
    (driveMemoryMapEntries destination inst key element entries 0 pointer matching pairs children width sized slots
      frame (Core3.Grows.refl _) leftAt rightAt actual bounded)

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
private theorem driveCollection {origin : CStore (core3 grow)} {budget : Nat}
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf) (entries : List Field) (index : Nat)
    (output : Stored.Lower.Output)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (width : (core3 grow).memAddrType? start.store.core destination.memory = some destination.width)
    {checkNext : ValueCheckNext grow sig output} {canonNext : ValueCanonNext grow sig output}
    {check canon : Cursor (E := core3 grow) (HostState sig)}
    {pending : Config (core3 grow) (HostState sig) → Prop}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon) (growth : Core3.Grows origin.core start.store.core)
    (checkAt : start.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
      destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
      destination.width (.dynamic type element entries) output >>= canonNext))
    (actual : Steps profile ready (specDispatch ready base) start labels finish)
    (bounded : labels.length ≤ budget) (compare : ShorterCallbackSlices profile ready base bindings budget)
    (atField : pending incoming)
    (atTail : ∀ (right : Config (core3 grow) (HostState sig)) ptr (peer : Cursor (E := core3 grow) (HostState sig)),
      right.ctl = peer.control (canonicalCollectionTail destination inst entries
      (layout destination.width element) output ptr (CanonicalTree.EntryMode.forOutput destination.width type output) >>= canonNext) → pending right)
    (visit : ∀ left right bytes pointer check canon residual,
      LinkedCallback.ChildFrameOver older left right check canon → Core3.Grows origin.core left.store.core →
      (core3 grow).memAddrType? left.store.core destination.memory = some destination.width →
      (core3 grow).memSize? left.store.core destination.memory = some bytes →
      pointer = alignTo pointer (layout destination.width element).alignment →
      pointer + entries.length * (layout destination.width element).size ≤ bytes →
      left.ctl = check.control (checkedCollectionTail destination inst entries (layout destination.width element)
        index output pointer (.ok ()) >>= checkNext) →
      right.ctl = canon.control (canonicalCollectionTail destination inst entries (layout destination.width element)
        output pointer (CanonicalTree.EntryMode.forOutput destination.width type output) >>= canonNext) →
      Steps profile ready (specDispatch ready base) left residual finish → residual.length ≤ budget →
      ValueVisitRun profile ready base bindings older origin output.Result pending checkNext canonNext left right residual finish) :
    ValueVisitRun profile ready base bindings older origin output.Result pending checkNext canonNext start incoming labels finish := by
  let area := layout destination.width element
  let mode := CanonicalTree.EntryMode.forOutput destination.width type output
  have initial : ComparedSlots profile ready base bindings start incoming [] start incoming :=
    ⟨[], [], fun _ => .done _ _, fun _ => .done _ _, rfl, rfl⟩
  have occurrences : ComparedOccurrencePaths profile ready base bindings start incoming [] start incoming :=
    ⟨[], [], fun place => ⟨place, .done _ _, .done _ _⟩, rfl, rfl, frame.store⟩
  have body := CallbackRange.collectionEntryPathsFrom destination inst type element entries index output checkNext canonNext
    frame checkAt canonAt embedder initial
  have entry := RecursiveTrails.collectionEntryOccurrences (sink := RefusalSink.ignore)
    (by unfold RefusalSink.CoversOccurrences; intros; exact True.intro) True.intro occurrences body
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
  have sliced := driveCollectionSlice entry frame.store (frame.store ▸ width) actual bounded compare
  unfold CollectionRunSlice at sliced
  cases prepared : Record.prepare start.store start.host.writer (Field.listObjects entries) with
  | error issue =>
    simp only [prepared] at sliced
    let refusal := match issue with
      | .preflight reason => Issue.field index (.beforeAllocation reason)
      | reason => Issue.nested index reason
    let stopped := { start with ctl := check.control (checkNext (.error refusal)) }
    obtain ⟨movement, aligned⟩ := sliced
    cases aligned with
    | inside _ nonempty remainder =>
      exact ⟨[], [], labels, start, incoming, [], rfl, rfl, frame.store,
        CallbackPrefix.stationaryTransport (fun place => .done start place) (fun place => .done incoming place),
        actual, .boundary (.localPrefix nonempty remainder)⟩
    | reached split tail =>
      exact ⟨[.tau, .tau], [], _, stopped, incoming, [], split, rfl, frame.store, movement, tail,
        .refused refusal check rfl atField⟩
  | ok value =>
    cases value
    simp only [prepared] at sliced
    rcases sliced with short | ⟨checked, canonical, trailing, reached, peer, mark, split, seen, tracked, paired, movement, ending, returned⟩
    · exact ⟨[], [], labels, start, incoming, [], rfl, rfl, frame.store,
        CallbackPrefix.stationaryTransport (fun place => .done start place) (fun place => .done incoming place),
        actual, .collectionInstall short⟩
    let leftTrace : Trace grow sig := [.tau, .tau, .tau] ++ checked
    let rightTrace : Trace grow sig := [.tau, .tau] ++ canonical
    have observed : visible leftTrace = visible rightTrace := seen.symm
    have tail := callbackEndSteps ending
    rcases returned with pending | ⟨pointer, cursor, _, active, _, _, _, range, fresh⟩
    · exact ⟨leftTrace, rightTrace, trailing, reached, peer, [mark], split, observed, paired.data.1, movement, tail,
        .boundary (.callback tracked paired ending pending)⟩
    subst mark
    have advance {lhs rhs : Config (core3 grow) (HostState sig)} {effects : Trace grow sig}
        (cut : AlignedCollectionRange profile ready base bindings start incoming lhs rhs leftTrace rightTrace effects trailing finish)
        (next : ∀ residual, Steps profile ready (specDispatch ready base) lhs residual finish → residual.length ≤ budget →
          ValueVisitRun profile ready base bindings older origin output.Result pending checkNext canonNext lhs rhs residual finish) :
        ValueVisitRun profile ready base bindings older origin output.Result pending checkNext canonNext start incoming labels finish := by
      obtain ⟨checkRange, canonRange, moved, leftSeen, rightSeen, _, aligned⟩ := cut
      cases aligned with
      | inside _ nonempty remainder =>
        exact ⟨leftTrace, rightTrace, trailing, reached, peer, _, split, observed, paired.data.1, movement, tail,
          .collectionRange nonempty remainder⟩
      | @reached residual used suffix =>
        have combined : labels = (leftTrace ++ checkRange) ++ residual := by
          simp only [leftTrace, split, used, List.append_assoc]
        have remaining : residual.length ≤ budget := by rw [combined, List.length_append] at bounded; omega
        exact prependValueVisit combined
          (by rw [visibleAppend leftTrace checkRange, visibleAppend rightTrace canonRange, observed, leftSeen, rightSeen]) moved
          (next residual suffix remaining)
    have trap (reason : TrapReason)
        (cut : AlignedCollectionRange profile ready base bindings start incoming (StepDefs.trapCfg reached) (StepDefs.trapCfg peer)
          leftTrace rightTrace [.trap reason] trailing finish) :
        ValueVisitRun profile ready base bindings older origin output.Result pending checkNext canonNext start incoming labels finish :=
      advance cut (fun residual suffix _ => ⟨[], [], residual, StepDefs.trapCfg reached, StepDefs.trapCfg peer, [], rfl, rfl,
        congrArg StepDefs.lockdownSt paired.data.1,
        CallbackPrefix.stationaryTransport (fun place => .done _ place) (fun place => .done _ place), suffix, .boundary (.trap rfl rfl)⟩)
    obtain ⟨bytes, _, sized, range⟩ := range
    by_cases misaligned : pointer ≠ alignTo pointer (layout destination.width element).alignment
    · exact trap .unalignedPointer (by simpa only [ite_eq_left misaligned] using range)
    simp only [ite_eq_right misaligned] at range
    by_cases bounds : pointer + entries.length * (layout destination.width element).size ≤ bytes
    · have aligned : pointer = alignTo pointer area.alignment := Classical.not_not.mp misaligned
      rw [ite_eq_left bounds] at range
      cases prepared : Record.prepare reached.store reached.host.writer (Field.listObjects entries) with
      | error issue =>
        simp only [prepared] at range
        obtain ⟨peerCursor, paired, cut⟩ := range
        refine advance cut (fun residual suffix _ => ?_)
        let refused := LinkedCallback.CollectionVisit.afterAllocation index issue
        let lhs := { reached with ctl := cursor.control (checkedCollectionTail destination inst entries area index output pointer (.error issue) >>= checkNext) }
        let rhs := { peer with ctl := peerCursor.control (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) }
        have checkedAt : lhs.ctl = cursor.control (checkNext (.error refused)) := by cases issue <;> rfl
        refine ⟨[], [], residual, lhs, rhs, [], rfl, rfl, paired.store,
          CallbackPrefix.stationaryTransport (fun place => .done _ place) (fun place => .done _ place), suffix,
          .refused refused cursor checkedAt (atTail rhs pointer peerCursor rfl)⟩
      | ok value =>
        cases value
        obtain ⟨lhs, rhs, peerCursor, related, liveWidth, liveSize, grew, checkedAt, canonicalAt, cut, _⟩ :=
          fresh bytes sized aligned bounds prepared
        exact advance cut (fun residual suffix remaining => visit lhs rhs bytes pointer cursor peerCursor residual related
          (growth.trans grew) liveWidth liveSize aligned bounds checkedAt canonicalAt suffix remaining)
    · exact trap .outOfBounds (by simpa only [ite_eq_right bounds] using range)

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
theorem driveCompiledMemory {origin : CStore (core3 grow)} {root item : Field} {schema : Stored.TypeOf} {budget bytes : Nat}
    (destination : RecordDestination) (inst : InstId) (address : Nat) (shape : MemoryVisitShape item)
    (rootLayout : root.LayoutMatches schema)
    (fits : Stored.Lower.fits Quirks.none destination.encoding destination.width schema root.value = true)
    (allocates : Field.AllocatorFor destination.realloc root) (path : root.Descendant item)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (placed : SlotFits destination.width bytes item address)
    (compare : ShorterCallbackSlices profile ready base bindings budget) :
    MemoryVisitField profile ready base bindings older origin destination inst budget item address := by
  have placedAt (left : Config (core3 grow) (HostState sig)) {initial : CStore (core3 grow)}
      {capacity : Nat} {type : Stored.TypeOf} {slot : Nat}
      (growth : Core3.Grows initial.core left.store.core)
      (sized : (core3 grow).memSize? initial.core destination.memory = some capacity)
      (aligned : slot % (layout destination.width type).alignment.bytes = 0)
      (bounds : slot + (layout destination.width type).size ≤ capacity) :
      placement destination left.store (layout destination.width type) slot = .ok () := by
    obtain ⟨reached, sizeAt, wider⟩ := growth.memSize sized
    change (core3 grow).memSize? left.store.core destination.memory = some reached at sizeAt
    simp [placement, aligned, sizeAt, Nat.not_lt.mpr (bounds.trans wider)]
    rfl
  induction shape generalizing address origin bytes with
  | @handle item handle =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt actual finish run bounded
    exact driveMemoryHandle destination inst item handle index address frame growth checkAt canonAt run
  | @scalar type payload data =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt actual finish run bounded
    exact driveMemoryScalar destination inst type data payload index address frame growth (growth.memAddrType width)
      (placedAt left growth sized placed.1 placed.2) checkAt canonAt run
  | @string item matched emitted =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt actual finish run bounded
    have aligned := placed.1
    have bounds := placed.2
    rw [matched.type_eq] at aligned bounds
    exact driveMemoryString destination inst index address rootLayout fits allocates path matched emitted embedder frame growth
      (growth.memAddrType width) (placedAt left growth sized aligned bounds) checkAt canonAt run bounded compare
  | @aggregate type items matched children ih =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt actual finish run bounded
    let entered := enterAggregate destination inst items index address left check checkNext
    have guard := aggregate_entry_prefix (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
      destination inst type items index address left check checkNext growth sized placed.1 placed.2 checkAt
    cases alignLocalBody (guard (.active 0 0)).toTrail.steps run (by simp [workerBranchLabel]) with
    | inside _ nonempty tail => exact stationaryMemoryVisit frame.store run (.localPrefix nonempty tail)
    | @reached trailing split tail =>
      have remaining : trailing.length ≤ budget := by rw [split, List.length_append] at bounded; omega
      have slots := Track.fields_slots destination.width matched placed.1 placed.2
        (MemoryVisitField profile ready base bindings older origin destination inst budget)
        (fun item member slot fits => ih item member slot (path.trans (.aggregate member (.self item))) width sized fits)
      have paired : LinkedCallback.ChildFrameOver older entered right check canon :=
        ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
      rw [CanonicalTree.field] at canonAt
      exact prependMemoryVisit (canonical := []) split rfl (CallbackPrefix.stationaryTransport guard (fun place => .done right place))
        (wrapMemoryVisit index (driveMemorySequence .fields destination inst items 0 address slots width paired growth rfl canonAt tail remaining))
  | @fixed element length entries count matching children ih =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt actual finish run bounded
    let area := layout destination.width element
    let reference := { right with ctl := canon.control (Track.canonical (.elements area.size) destination inst entries address >>= canonNext) }
    have widthAt : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width :=
      frame.store ▸ growth.memAddrType width
    obtain ⟨focused, checkedAt⟩ := CallbackRange.fixedEntryFoci (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst element length entries index address left right check canon checkNext canonNext widthAt checkAt canonAt
    have modulo : address % (layout destination.width (.fixedList element length)).alignment.bytes = 0 := placed.1
    have fits : address + (layout destination.width (.fixedList element length)).size ≤ bytes := placed.2
    rw [layout] at modulo fits
    have aligned : address = alignTo address area.alignment := by
      change address % area.alignment.bytes = 0 at modulo
      cases reached : area.alignment <;> simp only [alignTo, reached, Alignment.bytes] at modulo ⊢ <;> omega
    have bounds : address + entries.length * area.size ≤ bytes := by
      rw [count]
      simpa only [area, Layout.size, Nat.mul_assoc] using fits
    have slots := Track.elements_slots destination.width matching aligned bounds
      (MemoryVisitField profile ready base bindings older origin destination inst budget)
      (fun child member slot placed => ih child member slot (path.trans (.fixed member (.self child))) width sized placed)
    have paired : LinkedCallback.ChildFrameOver older left reference check canon :=
      ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
    exact prependMemoryVisit (checked := []) (canonical := [.tau]) rfl rfl
      (CallbackPrefix.stationaryTransport (fun place => .done left place) focused)
      (wrapMemoryVisit index (driveMemorySequence (.elements area.size) destination inst entries 0 address slots width
        paired growth checkedAt rfl run bounded))
  | @sum type arms tag selected layoutAt member _ ih =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt actual finish run bounded
    have widthAt : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width :=
      frame.store ▸ growth.memAddrType width
    obtain ⟨store, result, checked, canonical, lhs, _, observed, cut, occurrences⟩ :=
      memory_sum_tag_between (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
        (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst type arms tag index address selected
        left.store left right check canon checkNext canonNext frame.store frame.thread
        (by simp [ptrTypeIn, CanonOpts.ptrType, RecordDestination.context, widthAt])
        (frame.store ▸ Core3.Grows.refl left.store.core) checkAt canonAt true
    cases alignWorkerBody lhs run with
    | inside _ nonempty tail => exact stationaryMemoryVisit frame.store run (.localPrefix nonempty tail)
    | departure _ split shared _ branch _ _ step tail =>
      exact stationaryMemoryVisit frame.store run (.localChoice split branch.2 shared step tail)
    | @reached trailing split tail =>
      let reached := localLeafEnd left left.host store check.thread check.frames check.rest
        (sumCheckedNext destination inst selected index (sumPayloadAddress destination.width arms address) checkNext) result
      let peer := localLeafEnd right right.host store canon.thread canon.frames canon.rest
        (sumCanonicalNext destination inst selected (sumPayloadAddress destination.width arms address) canonNext) result
      cases result with
      | error reason =>
        exact ⟨checked, canonical, _, reached, peer, [], split, observed, rfl, CallbackPrefix.localLeafTransport occurrences, tail,
          .boundary (.trap rfl rfl)⟩
      | ok value =>
        cases value
        cases selected with
        | none =>
          exact ⟨checked, canonical, _, reached, peer, [], split, observed, rfl, CallbackPrefix.localLeafTransport occurrences, tail,
            .returned check canon
              ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
              (growth.trans cut.1) rfl rfl⟩
        | some child =>
          let slot := sumPayloadAddress destination.width arms address
          have aligned := placed.1
          have bounds := placed.2
          change address % (layout destination.width type).alignment.bytes = 0 at aligned
          change address + (layout destination.width type).size ≤ bytes at bounds
          rw [layoutAt destination.width] at aligned bounds
          have listed : some (layout destination.width child.type) ∈ arms.map (layoutOption destination.width) :=
            List.mem_map.mpr ⟨some child.type, member child rfl, by rw [layoutOption]⟩
          obtain ⟨modulo, within⟩ := variantLayout_payload_fits _ address (layout destination.width child.type)
            (Nat.dvd_of_mod_eq_zero aligned) listed
          rw [List.length_map] at modulo within
          have childFits : SlotFits destination.width bytes child slot := ⟨modulo, within.trans bounds⟩
          have remaining : trailing.length ≤ budget := by rw [split, List.length_append] at bounded; omega
          exact prependMemoryVisit split observed (CallbackPrefix.localLeafTransport occurrences)
            (wrapMemoryVisit index (ih child rfl slot (path.trans (.sum (.self child))) width sized childFits 0
              (aggregateNext index checkNext) canonNext reached peer check canon
              ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
              (growth.trans cut.1) rfl rfl _ finish tail remaining))
  | @list element entries matching _ ih =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt actual finish run bounded
    refine driveCollection destination inst (.list element) element entries index (.memory address) embedder
      (growth.memAddrType width) frame growth checkAt canonAt run bounded compare
      (.field canon (.dynamic (.list element) element entries) address canonNext canonAt)
      (fun _ pointer peer atTail => .collection peer entries (layout destination.width element) pointer address .value canonNext atTail) ?_
    intro reached peer capacity pointer cursor peerCursor residual related grew liveWidth liveSize aligned bounds checkedAt canonicalAt suffix remaining
    exact driveMemoryElements destination inst element entries index pointer address matching
      (fun item member slot fits => ih item member slot (path.trans (.dynamic member (.self item))) liveWidth liveSize fits)
      liveWidth aligned bounds related grew checkedAt canonicalAt suffix remaining
  | @map key element entries matching emitted _ ih =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt actual finish run bounded
    let entryType : Stored.TypeOf := .record (mapEntryFields key element)
    have pairs : ∀ item ∈ entries, ∃ keyField value, item = .aggregate entryType [keyField, value] := by
      cases emitted with
      | map shapes _ =>
        intro item member
        obtain ⟨payload, value, shape⟩ := shapes item member
        exact ⟨.data (.prim key.toPrimitive) payload, value, shape⟩
    refine driveCollection destination inst (.map key element) entryType entries index (.memory address) embedder
      (growth.memAddrType width) frame growth checkAt canonAt run bounded compare
      (.field canon (.dynamic (.map key element) entryType entries) address canonNext canonAt)
      (fun _ pointer peer atTail => .collection peer entries (layout destination.width entryType) pointer address
        (.memoryMap destination.width key element) canonNext atTail) ?_
    intro reached peer capacity pointer cursor peerCursor residual related grew liveWidth liveSize aligned bounds checkedAt canonicalAt suffix remaining
    exact driveMemoryMap destination inst key element entries index pointer address matching pairs
      (fun keyField value member child fieldMember slot fits =>
        ih keyField value member child fieldMember slot (path.trans (.dynamic member (.aggregate fieldMember (.self child))))
          liveWidth liveSize fits) liveWidth liveSize aligned bounds related grew checkedAt canonicalAt suffix remaining

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback LinkedCallback.MemorySequence in
theorem driveCompiledFlat {origin : CStore (core3 grow)} {root item : Field} {schema : Stored.TypeOf} {budget : Nat}
    (destination : RecordDestination) (inst : InstId) (shape : FlatVisitShape item)
    (rootLayout : root.LayoutMatches schema)
    (fits : Stored.Lower.fits Quirks.none destination.encoding destination.width schema root.value = true)
    (allocates : Field.AllocatorFor destination.realloc root) (path : root.Descendant item)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (compare : ShorterCallbackSlices profile ready base bindings budget) :
    FlatVisitField profile ready base bindings older origin destination inst budget item := by
  induction shape with
  | handle item nominal => exact driveFlatHandle destination inst budget item nominal
  | scalar type localType payload => exact driveFlatScalar destination inst budget type localType payload width
  | sum type arms tag selected matched child ih =>
    exact driveFlatSum destination inst matched (fun item active => ih item active (path.trans (active ▸ .sum (.self item))))
  | string item matched emitted =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt actual finish run bounded
    obtain ⟨str, field⟩ := CallbackRange.compiledStringCommit destination inst .flat rootLayout fits allocates path
      matched emitted embedder frame (growth.memAddrType width) rfl checkAt canonAt
    obtain ⟨checked, canonical, trailing, lhs, rhs, marks, split, observed, movement, same, rest, ending⟩ :=
      driveStringCommit field run bounded compare
    exact ⟨checked, canonical, trailing, lhs, rhs, marks, split, observed, movement, same, rest,
      mapStringEnd (fun _ _ _ ⟨words, paired, grew, checked, canonical⟩ => .returned words paired (growth.trans grew) checked canonical) ending⟩
  | collection type element entries matching children =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt actual finish run bounded
    let area := layout destination.width element
    let mode := CanonicalTree.EntryMode.forOutput destination.width type .flat
    have valueMode : mode = .value := by cases type <;> rfl
    let pending (peer : Config (core3 grow) (HostState sig)) : Prop :=
      peer = right ∨ PendingMemoryField destination inst peer ∨
      ∃ (pointer : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)),
        peer.ctl = cursor.control (canonicalCollectionTail destination inst entries area .flat pointer mode >>= canonNext)
    have driven := driveCollection (pending := pending) destination inst type element entries index .flat embedder
      (growth.memAddrType width) frame growth checkAt canonAt run bounded compare (.inl rfl)
      (fun _ pointer cursor live => .inr (.inr ⟨pointer, cursor, live⟩)) (by
        intro reached peer bytes pointer cursor peerCursor residual related grew liveWidth liveSize aligned bounds checkedAt canonicalAt suffix remaining
        have slots := Track.elements_slots destination.width matching aligned bounds
          (MemoryVisitField profile ready base bindings older reached.store destination inst budget)
          (fun child member slot placed => driveCompiledMemory destination inst slot (children child member) rootLayout fits allocates
            (path.trans (.dynamic member (.self child))) embedder liveWidth liveSize placed compare)
        obtain ⟨checkElements, canonElements⟩ := CallbackRange.collectionElementFoci destination inst entries area mode .flat pointer index
          checkNext canonNext checkedAt canonicalAt
        rw [valueMode] at canonElements
        exact driveCollectionPublish destination inst index pointer entries.length .flat (fun _ proof => .inr (.inl proof)) grew
          (driveMemorySequence (.elements area.size) destination inst entries 0 pointer slots liveWidth related (Core3.Grows.refl _)
            checkElements canonElements suffix remaining))
    obtain ⟨checked, canonical, trailing, lhs, rhs, marks, split, observed, same, movement, tail, ending⟩ := driven
    refine ⟨checked, canonical, trailing, lhs, rhs, marks, split, observed.symm, movement, same, tail, ?_⟩
    cases ending with
    | @returned cursor peer words paired grew checkedAt canonicalAt =>
      exact .descriptor (pointer := 0) (.returned words paired grew checkedAt canonicalAt)
    | refused issue cursor atRefusal _ => exact .descriptor (pointer := 0) (peer := cursor) (.refused issue atRefusal)
    | boundary reached => exact mapStringEnd (fun _ _ _ impossible => impossible.elim) reached
    | collectionInstall short => exact .collectionInstall short
    | collectionRange nonempty remainder => exact .collectionRange nonempty remainder
  | aggregate type fields children ih =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt actual finish run bounded
    have noLeading (verdict : Except Stored.Endpoints.RecordLower.Issue (List FlatValue)) : verdict.map ([] ++ ·) = verdict := by
      cases verdict <;> rfl
    rw [Record.Effects.field] at checkAt
    rw [CanonicalTree.field] at canonAt
    obtain ⟨checked, canonical, trailing, lhs, rhs, marks, split, seen, movement, same, tail, ending⟩ :=
      driveFlatSequence destination inst fields 0 []
        (fun item member => ih item member (path.trans (.aggregate member (.self item))))
        (fun verdict => checkNext (verdict.mapError (.nested index))) canonNext frame growth
        (by
          let body : Session grow sig (Except Stored.Endpoints.RecordLower.Issue (List FlatValue)) :=
            Record.Effects.flat recordClaims Limits.spec Quirks.none (destination.context inst) destination.width fields 0
          change left.ctl = check.control ((body.bind fun verdict => .pure (verdict.mapError (.nested index))).bind checkNext) at checkAt
          rw [Prog.bind_assoc] at checkAt
          change left.ctl = check.control (body.bind fun verdict => checkNext (verdict.mapError (.nested index))) at checkAt
          simpa only [flatSequenceChecked, noLeading, Prog.bind_eq] using checkAt)
        (by simpa only [flatSequenceCanonical, List.nil_append] using! canonAt) run bounded
    exact ⟨checked, canonical, trailing, lhs, rhs, marks, split, seen, movement, same, tail,
      mapStringEnd (fun _ _ _ result => by
        cases result with
        | returned words paired grew checked canonical => exact .returned words paired grew checked canonical
        | refused issue checked => exact .refused (.nested index issue) checked) ending⟩
  | fixed element length items children ih =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt actual finish run bounded
    have noLeading (verdict : Except Stored.Endpoints.RecordLower.Issue (List FlatValue)) : verdict.map ([] ++ ·) = verdict := by
      cases verdict <;> rfl
    rw [Record.Effects.field] at checkAt
    rw [CanonicalTree.field] at canonAt
    obtain ⟨checked, canonical, trailing, lhs, rhs, marks, split, seen, movement, same, tail, ending⟩ :=
      driveFlatSequence destination inst items 0 []
        (fun item member => ih item member (path.trans (.fixed member (.self item))))
        (fun verdict => checkNext (verdict.mapError (.nested index))) canonNext frame growth
        (by
          let body : Session grow sig (Except Stored.Endpoints.RecordLower.Issue (List FlatValue)) :=
            Record.Effects.flat recordClaims Limits.spec Quirks.none (destination.context inst) destination.width items 0
          change left.ctl = check.control ((body.bind fun verdict => .pure (verdict.mapError (.nested index))).bind checkNext) at checkAt
          rw [Prog.bind_assoc] at checkAt
          change left.ctl = check.control (body.bind fun verdict => checkNext (verdict.mapError (.nested index))) at checkAt
          simpa only [flatSequenceChecked, noLeading, Prog.bind_eq] using checkAt)
        (by simpa only [flatSequenceCanonical, List.nil_append] using! canonAt) run bounded
    exact ⟨checked, canonical, trailing, lhs, rhs, marks, split, seen, movement, same, tail,
      mapStringEnd (fun _ _ _ result => by
        cases result with
        | returned words paired grew checked canonical => exact .returned words paired grew checked canonical
        | refused issue checked => exact .refused (.nested index issue) checked) ending⟩

open ABI PayloadPrefix Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
theorem driveCompiledMemoryElements {origin : CStore (core3 grow)} {root : Field} {schema : Stored.TypeOf} {budget bytes : Nat}
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
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon) (growth : Core3.Grows origin.core start.store.core)
    (checkAt : start.ctl = check.control (checkedCollectionTail destination inst entries (layout destination.width element)
      index (.memory address) pointer (.ok ()) >>= checkNext))
    (canonAt : incoming.ctl = canon.control (canonicalCollectionTail destination inst entries (layout destination.width element)
      (.memory address) pointer .value >>= canonNext))
    (actual : Steps profile ready (specDispatch ready base) start labels finish)
    (bounded : labels.length ≤ budget) (compare : ShorterCallbackSlices profile ready base bindings budget) :
    MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext start incoming labels finish := by
  exact driveMemoryElements destination inst element entries index pointer address matching
    (fun item member slot placed => driveCompiledMemory destination inst slot (shapes item member) rootLayout fits allocates
      (paths item member) embedder width sized placed compare) width aligned bounds frame growth checkAt canonAt actual bounded

private theorem rebaseRange {leftStart rightStart leftEntry rightEntry checked canonical : Config (core3 grow) (HostState sig)}
    {seen : Trace grow sig} {cursor destination area count pointer plan checkNext canonNext}
    (entry : ComparedOccurrencePaths profile ready base bindings leftStart rightStart [] leftEntry rightEntry)
    (localRange : CollectionRangeOccurrences profile ready base bindings older leftEntry rightEntry checked canonical seen
      cursor destination area count pointer plan checkNext canonNext) :
    CollectionRangeOccurrences profile ready base bindings older leftStart rightStart checked canonical seen
      cursor destination area count pointer plan checkNext canonNext := by
  obtain ⟨bytes, width, sized, verdict⟩ := localRange
  refine ⟨bytes, width, sized, ?_⟩
  by_cases misaligned : pointer ≠ ABI.alignTo pointer area.alignment
  · simp only [ite_eq_left misaligned] at verdict ⊢
    exact ⟨by simpa only [List.nil_append] using CallbackPrefix.appendComparedOccurrences entry verdict.1, verdict.2⟩
  · simp only [ite_eq_right misaligned] at verdict ⊢
    by_cases fits : pointer + count * area.size ≤ bytes
    · simp only [ite_eq_left fits] at verdict ⊢
      obtain ⟨canon, frame, returned, peer, paths, transport⟩ := verdict
      exact ⟨canon, frame, returned, peer,
        by simpa only [List.nil_append] using CallbackPrefix.appendComparedOccurrences entry paths, transport⟩
    · simp only [ite_eq_right fits] at verdict ⊢
      exact ⟨by simpa only [List.nil_append] using CallbackPrefix.appendComparedOccurrences entry verdict.1, verdict.2⟩

open Stored.Endpoints.RecordLower ABI PayloadPrefix ReturnFrame.Occurrence in
private theorem finishCollectionRefusal {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (type element : Stored.TypeOf) (entries : List Field) (pointer : Nat)
    {checked canonical : Config (core3 grow) (HostState sig)} {seen : Trace grow sig}
    {cursor : Cursor (E := core3 grow) (HostState sig)} {leading : Trace grow sig}
    (caller : Prefix profile ready (specDispatch ready base) site.checked (.active 0 0) leading checked (.active 0 1)) :
    let area := layout site.destination.width element
    let mode := CanonicalTree.EntryMode.forOutput site.destination.width type route.output
    CollectionRangeOccurrences profile ready base bindings older site.start incoming checked canonical seen
      cursor site.destination area entries.length pointer (Field.listObjects entries)
      (fun addr verdict => checkedCollectionTail site.destination site.inst entries area 0 route.output addr verdict >>= site.reply)
      (fun addr => canonicalCollectionTail site.destination site.inst entries area route.output addr mode >>= site.referenceReply) →
    PublicCollectionRefusalOccurrences profile ready base bindings site incoming checked canonical seen cursor type element entries pointer := by
  intro area mode range
  unfold PublicCollectionRefusalOccurrences
  dsimp only
  intro bytes sized aligned bounds issue failed
  obtain ⟨capacity, _, atCapacity, verdict⟩ := range
  have sameCapacity := Option.some.inj (atCapacity.symm.trans sized)
  have fits : pointer + entries.length * area.size ≤ capacity := by simpa only [sameCapacity] using bounds
  by_cases misaligned : pointer ≠ alignTo pointer area.alignment
  · exact False.elim (misaligned aligned)
  simp only [ite_eq_right misaligned, ite_eq_left fits] at verdict
  obtain ⟨canon, _, ⟨localLabels, _, tracks⟩, _, paths, _⟩ := verdict
  let refused := LinkedCallback.CollectionVisit.afterAllocation 0 issue
  let reply := route.reply site.destination site.start.host.nextTicket (.error refused)
  have stop : (checkedCollectionTail site.destination site.inst entries area 0 route.output pointer (.error issue) >>= site.reply) =
      site.reply (.error refused) := by cases issue <;> rfl
  rw [failed, stop] at tracks paths
  let reached := { checked with ctl := cursor.control (site.reply (.error refused)) }
  obtain ⟨segments, atCaller⟩ := site.reached_caller (reached := reached) (body := site.reply (.error refused))
    rfl (caller.append (tracks.retains 0))
  have atReply : reached.ctl = ⟨cursor.thread, .prog (do return .flat (← writeCompletion reply)),
      .core site.core site.resume :: segments⟩ :: cursor.rest := by
    simp only [reached, Cursor.control, atCaller, PayloadRoot.Site.reply, reply]
  obtain ⟨leftLabels, rightLabels, paths, leftSeen, rightSeen, store⟩ := paths
  refine ⟨canon, segments, leftLabels ++ [.tau, .tau, .tau], rightLabels, ?_, rightSeen, store, ?_⟩
  · rw [visibleAppend, leftSeen]
    exact List.append_nil _
  · intro mark
    obtain ⟨next, left, right⟩ := paths mark
    refine ⟨next, left.append ?_, right⟩
    cases next with
    | none => exact Trail.absent (Plain.give_completion_steps reply atReply)
    | some place => exact Plain.give_completion_trail reply place atReply

theorem publicCollectionOccurrences {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} {checkLabels : Trace grow sig}
    {type element : Stored.TypeOf} {entries : List Stored.Endpoints.RecordLower.Field}
    (field : site.field = .dynamic type element entries)
    (checked : site.EntryPrefix profile ready (ComponentCall.hostWithComponent bindings callees) checkLabels site.checked)
    (silent : PayloadPrefix.visible checkLabels = [])
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (prepared : Stored.OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ()) :
    PublicCollectionOccurrences profile ready bindings callees older site incoming type element entries := by
  unfold PublicCollectionOccurrences
  obtain ⟨entered, aligned, _, entry⟩ := pendingComparedEntry site checked silent (pendingRecursiveRoot site linked paired selected)
  have bodyAt := site.reference_at linked site.referenceReply
  rw [field] at bodyAt
  obtain ⟨canon, frame, canonAt⟩ := CallbackRange.referenceFrame site bodyAt aligned
  have checkAt : site.checked.ctl = site.cursor.control
      (Stored.OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none (site.destination.context site.inst)
        site.destination.width (.dynamic type element entries) 0 route.output >>= site.reply) := by
    simp only [PayloadRoot.Site.checked, PayloadRoot.Site.withBody, field]
  have live : Stored.OwnedMemory.Claims.Record.prepare site.checked.store site.checked.host.writer
      (Stored.Endpoints.RecordLower.Field.listObjects entries) = .ok () := by
    change Stored.OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer _ = .ok ()
    simpa only [field, Stored.Endpoints.RecordLower.Field.objects] using prepared
  have width := site.destination.check_width site.start.store linked.destination
  refine ⟨entered, canon, entry, ?_⟩
  intro seen finish callback
  obtain ⟨leftLabels, rightLabels, reached, mark, installed, paths, returns⟩ :=
    CallbackRange.collectionOccurrences (base := ComponentCall.hostWithComponent bindings callees)
      site.destination site.inst type element entries route.output 0 site.reply site.referenceReply
      frame (frame.store ▸ width) live checkAt canonAt rfl callback
  refine ⟨leftLabels, rightLabels, reached, mark, installed, ?_, ?_⟩
  · simpa only [List.nil_append] using CallbackPrefix.appendComparedOccurrences entry paths
  · intro pointer cursor active returning
    have range := rebaseRange entry (returns pointer cursor active returning)
    have allocator := installed.checkedTrail
    rw [active] at allocator
    obtain ⟨_, caller⟩ := CallbackRange.collectionCaller site linked type element entries field live allocator
    exact ⟨range, finishCollectionRefusal site type element entries pointer caller range⟩

open ReturnFrame.Occurrence PayloadPrefix in
private theorem consumeGiveCommonReply {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (value : route.output.Result)
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    {actual checkEntry canonLeading checkBody trailing : Trace grow sig} {budget : Nat}
    (split : actual = checkBody ++ trailing)
    (residual : Steps profile ready (specDispatch ready base) left trailing finish)
    (combined : OccurrenceTransport profile ready base bindings site.start incoming (checkEntry ++ checkBody)
      canonLeading left right [some (.active 0 0)])
    (original : Prefix profile ready (specDispatch ready base) site.checked (.active 0 0) checkBody left (.active 0 0))
    (frame : LinkedCallback.ChildFrameOver older left right check canon)
    (checkAt : left.ctl = check.control (site.reply (.ok value)))
    (canonAt : right.ctl = canon.control (site.referenceReply value))
    (seen : visible (checkEntry ++ checkBody) = visible canonLeading) (bounded : actual.length ≤ budget)
    (compare : ShorterCallbackSlices profile ready base bindings budget) :
    GiveVisitCommonReply profile ready base bindings older site value incoming left right checkEntry checkBody canonLeading actual trailing finish := by
  obtain ⟨checked, canonical, recorded, unchanged, paired, transport⟩ :=
    CallbackRange.completePublicTransport site value combined original frame checkAt canonAt
  obtain ⟨move, returned, outside⟩ := transport
  obtain ⟨_, lead, _⟩ := combined
  have popped := stripExactPrefix (lead none).1.steps (returned none).1.steps
  rcases splitSilent (count := 3) popped residual with ⟨suffix, divided, tail⟩ | short
  · have smaller : suffix.length < actual.length := by
      simp only [split, divided, List.length_append, List.length_replicate]; omega
    have paths : OccurrenceTransport profile ready base bindings site.start incoming ((checkEntry ++ checkBody) ++ [.tau, .tau, .tau])
        (canonLeading ++ [.tau]) checked canonical := ⟨move, returned, outside⟩
    refine .inr ⟨suffix, checked, canonical, divided, smaller, tail, recorded, unchanged, ?_⟩
    rcases classifyReachedGrowth (returned none).1.steps with certified | openUpdate
    · have segment : ExecutedCallbackSegment profile ready base bindings older site.start incoming
          ((checkEntry ++ checkBody) ++ [.tau, .tau, .tau]) (canonLeading ++ [.tau]) checked canonical :=
        ⟨certified, by rw [visibleAppend, visibleAppend, seen]; rfl, paired, paths⟩
      obtain ⟨continued, reference, remaining, reached, peer, division, suffixSegment, ending⟩ :=
        compare (Nat.lt_of_lt_of_le smaller bounded) tail paired
      exact .inl ⟨segment, _, _, remaining, reached, peer,
        by rw [split, divided, division]; simp only [List.append_assoc, List.replicate_succ, List.replicate_zero],
        CallbackPrefix.appendExecutedCallbacks segment suffixSegment, ending⟩
    · exact .inr ⟨openUpdate, paired, paths⟩
  · exact .inl short

open ReturnFrame.Occurrence in
private def LinkedMemoryResidualBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) (incoming : Config (core3 grow) (HostState sig)) (budget : Nat) : Prop :=
  ∃ canonEntry entered, PayloadPrefix.visible canonEntry = [] ∧
    (∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place canonEntry entered (site.entryPlace place)) ∧ entered.host = incoming.host ∧
    ∀ checkEntry, site.EntryPrefix profile ready base checkEntry site.checked → PayloadPrefix.visible checkEntry = [] →
      ∀ actual finish, Steps profile ready (specDispatch ready base) site.checked actual finish → actual.length ≤ budget →
        MemoryVisitWithReply profile ready base bindings older site incoming entered checkEntry canonEntry actual finish

open ABI PayloadPrefix ReturnFrame.Occurrence Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims LinkedCallback.MemorySequence in
private theorem linkedMemoryResidualBody {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (linked : site.Linked bindings) (shape : MemoryVisitShape site.field)
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {budget : Nat} (compare : ShorterCallbackSlices profile ready base bindings budget) :
    PayloadRoot.Cut site profile ready bindings (LinkedMemoryResidualBody profile ready base bindings older site incoming budget) base := by
  refine site.parked_after_admission linked _ (fun fits placed _ => ?_) base embedder
  obtain ⟨plan, compiled⟩ := linked.compiled
  have matched := Record.preflightValue_layout _ _ _ _ _ plan compiled
  have fit := Record.preflightValue_value _ _ _ _ _ plan compiled ▸ fits
  have width := site.destination.check_width site.start.store linked.destination
  have position : placement site.destination site.checked.store (layout site.destination.width site.field.type) (flatNat pointer) = .ok () :=
    matched.type_eq.symm ▸ placed
  obtain ⟨aligned, bytes, sized, bounds⟩ := CallbackRange.placementInterval site.destination site.checked.store _ _ position
  obtain ⟨entry, entered, quiet, installed, related, hostSame, storage⟩ :=
    LiveDispatch.entry_paired_storage (profile := profile) (ready := ready) (base := base) site linked paired selected
  obtain ⟨peer, frame, canonAt⟩ := CallbackRange.referenceFrame site (site.reference_at linked site.referenceReply) related
  refine ⟨entry, entered, silentVisible quiet, installed, hostSame, fun checkEntry checkTrack checkQuiet actual finish run bounded => ?_⟩
  have visit := driveCompiledMemory (origin := site.checked.store) site.destination site.inst (flatNat pointer) shape
      matched fit (CallbackRange.preflightAllocator site linked) (.self _) embedder width sized ⟨aligned, bounds⟩ compare
      0 site.reply site.referenceReply site.checked entered site.cursor peer frame (Core3.Grows.refl _) rfl canonAt actual finish run bounded
  obtain ⟨checked, canonical, trailing, left, right, marks, split, seen, store, ⟨move, paths, outside⟩, residual, endpoint⟩ := visit
  obtain ⟨atEntry, track, frameEntry⟩ := CallbackRange.publicEntryTransport site linked checkTrack installed storage
  have leading (place : Option Location) :
      Trail profile ready (specDispatch ready base) site.start place (checkEntry ++ checked) left (move (atEntry place)) ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place
        (entry ++ canonical) right (move (atEntry place)) :=
    ⟨(track place).1.append (paths (atEntry place)).1, (track place).2.append (paths (atEntry place)).2⟩
  let callerMark := move (some (.active 0 0))
  have rebased : OccurrenceTransport profile ready base bindings site.start incoming
      (checkEntry ++ checked) (entry ++ canonical) left right (marks ++ [callerMark]) := by
    refine ⟨move ∘ atEntry, leading, fun changes retained prior => ?_⟩
    simpa only [List.append_assoc, List.map_append, List.map_cons, List.map_map, List.map_nil, callerMark]
      using outside changes _ (frameEntry changes retained prior)
  have observed : visible (checkEntry ++ checked) = visible (entry ++ canonical) := by
    rw [visibleAppend, visibleAppend, checkQuiet, silentVisible quiet, seen]
  have common (active : callerMark = some (.active 0 0)) (empty : marks = [])
      (check canon : Cursor (E := core3 grow) (HostState sig)) (returned : LinkedCallback.ChildFrameOver older left right check canon)
      (checkAt : left.ctl = check.control (site.reply (.ok ()))) (canonAt : right.ctl = canon.control (site.referenceReply ())) :
      MemoryVisitCommonReply profile ready base bindings older site incoming left right checkEntry checked
        (entry ++ canonical) actual trailing finish := by
    rw [empty, List.nil_append, active] at rebased
    have marked := (paths (some (.active 0 0))).1
    change move (some (.active 0 0)) = some (.active 0 0) at active
    rw [active] at marked
    obtain ⟨_, equal, caller⟩ := marked.survives
    cases equal
    exact consumeGiveCommonReply site () split residual rebased caller returned checkAt canonAt observed bounded compare
  have refusedReply (active : callerMark = some (.active 0 0)) (issue : Stored.Endpoints.RecordLower.Issue)
      (check : Cursor (E := core3 grow) (HostState sig)) (checkAt : left.ctl = check.control (site.reply (.error issue))) :
      MemoryVisitRefusedReply profile ready base bindings older site incoming left right issue (checkEntry ++ checked)
        (entry ++ canonical) (checkEntry ++ actual) trailing finish := by
    have marked := (paths (some (.active 0 0))).1
    change move (some (.active 0 0)) = some (.active 0 0) at active
    rw [active] at marked
    obtain ⟨_, equal, caller⟩ := marked.survives
    cases equal
    obtain ⟨segments, frames⟩ := site.reached_caller checkAt caller
    let reply := (GiveEffectRoute.memory pointer).reply site.destination site.start.host.nextTicket (.error issue)
    have atReply : left.ctl = ⟨check.thread, .prog (do return .flat (← writeCompletion reply)),
        .core site.core site.resume :: segments⟩ :: check.rest := by
      simpa only [Cursor.control, frames, PayloadRoot.Site.reply, reply] using checkAt
    have completed := Plain.give_completion_steps (profile := profile) (ready := ready)
      (dispatch := specDispatch ready base) reply atReply
    rcases splitSilent (count := 3) completed residual with ⟨suffix, divided, tail⟩ | short
    · have refused : CheckedOnlyGiveReply profile ready base bindings (.memory pointer) site.destination site.start.host.nextTicket
          issue site.start incoming left right (checkEntry ++ checked) (entry ++ canonical) trailing finish := by
        refine ⟨suffix, _, divided, (leading none).1.steps, completed, tail, rfl, rfl, fun place => ?_⟩
        obtain ⟨checkedLead, canonicalLead⟩ := leading place
        cases reached : move (atEntry place) with
        | none =>
          rw [reached] at checkedLead canonicalLead
          exact ⟨none, none, checkedLead.append (.absent completed), canonicalLead⟩
        | some prior =>
          rw [reached] at checkedLead canonicalLead
          exact ⟨_, some prior, checkedLead.append (Plain.give_completion_trail reply prior atReply), canonicalLead⟩
      refine .inr ⟨refused, fun install => ?_⟩
      rw [split, ← List.append_assoc]
      exact callbackTerminalSlice paired (.refused install observed.symm refused)
    · exact .inl short
  refine ⟨checked, canonical, trailing, left, right, marks, move, split, seen, store, paths, outside, residual, endpoint,
    fun active => ⟨fun empty ⟨check, canon, returned, checkAt, canonAt⟩ => common active empty check canon returned checkAt canonAt,
      refusedReply active⟩, fun install => ?_⟩
  have total : checkEntry ++ actual = (checkEntry ++ checked) ++ trailing := by rw [split, List.append_assoc]
  have cut : GiveBodyCut profile ready base bindings site.start incoming left right (checkEntry ++ checked)
      (entry ++ canonical) trailing finish (marks ++ [callerMark]) := ⟨observed, store, rebased, residual⟩
  have stop (why : GiveBodyStop profile ready base left right trailing finish callerMark) :
      CallbackSlice profile ready base bindings older site.start incoming (checkEntry ++ actual) finish :=
    total ▸ callbackTerminalSlice paired (.body install cut why)
  cases endpoint with
  | returned check canon frame _ checkAt canonAt =>
    by_cases active : callerMark = some (.active 0 0)
    · rcases common active rfl check canon frame checkAt canonAt with short | ⟨suffix, replied, peer, divided, _, tail, _, _, result⟩
      · exact stop (.replyPrefix none short)
      rcases result with ⟨_, compared⟩ | ⟨update, aligned, trails⟩
      · exact compared
      · rw [total, divided, ← List.append_assoc]
        exact callbackTerminalSlice paired (.uncertified install update aligned trails tail)
    · exact stop (.callerNotTop none active)
  | refused issue check checkAt _ =>
    by_cases active : callerMark = some (.active 0 0)
    · rcases refusedReply active issue check checkAt with short | ⟨_, compared⟩
      · exact stop (.replyPrefix (some issue) short)
      · exact compared install
    · exact stop (.callerNotTop (some issue) active)
  | boundary ending =>
    cases ending with
    | descriptor impossible => exact impossible.elim
    | trap left right => exact stop (.trap left right)
    | localPrefix nonempty tail => exact stop (.localPrefix nonempty tail)
    | localChoice split choice shared step tail => exact stop (.localChoice split choice shared step tail)
    | installPrefix short => exact stop (.allocatorInstall short)
    | collectionInstall short => exact stop (.allocatorInstall short)
    | collectionRange nonempty tail => exact stop (.localPrefix nonempty tail)
    | callback tracked aligned ending notPopped =>
      rw [total]
      exact callbackTerminalSlice paired (.allocator install cut tracked aligned ending notPopped)
  | collectionInstall short => exact stop (.allocatorInstall short)
  | collectionRange nonempty tail => exact stop (.localPrefix nonempty tail)

theorem actualMemoryRequest {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (linked : site.Linked bindings) (shape : MemoryVisitShape site.field)
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (run : Steps profile ready (specDispatch ready base) site.start labels finish)
    (compare : ShorterCallbackSlices profile ready base bindings labels.length) :
    PayloadRoot.Cut site profile ready bindings (ActualMemoryRequestRun profile ready base bindings older site incoming labels finish) base := by
  cases linkedMemoryResidualBody site linked shape paired selected embedder compare with
  | refused issue quiet entered => exact .refused issue quiet entered
  | placementTrap reason count verdict entered => exact .placementTrap reason count verdict entered
  | @placed entry quiet verdict prepared entered body =>
    refine .placed quiet verdict prepared entered ⟨entry, entered, quiet, ?_⟩
    cases alignLocalBody (entered (.active 0 0)).toTrail.steps run (noBranchOfVisible quiet (by simp)) with
    | inside split nonempty tail =>
      exact ⟨.inl ⟨_, split, nonempty, tail⟩, fun install => callbackTerminalSlice paired (.entryPrefix install run nonempty tail)⟩
    | @reached residual split tail =>
      obtain ⟨canonEntry, canon, silent, tracks, host, visit⟩ := body
      have bounded : residual.length ≤ labels.length := by rw [split, List.length_append]; omega
      have visited := visit entry entered quiet residual finish tail bounded
      refine ⟨.inr ⟨canonEntry, canon, residual, split, silent, tracks, host, visited⟩, fun install => ?_⟩
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, cut⟩ := visited
      exact split ▸ cut install

theorem actualSelectedMemoryRequest {pointer : FlatValue} {request : CoreGiveRequest bindings start}
    (selection : request.Selected (.memory pointer)) {field : Stored.Endpoints.RecordLower.Field} {plan label}
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
        (ActualMemoryRequestRun profile ready base bindings older site incoming (label :: labels) finish) base := by
  obtain ⟨tag, payload, arity, children, root, linked⟩ := selection.compiler_success compiled
  exact ⟨tag, payload, arity, children, root, linked, actualMemoryRequest _ linked (siteVisitShapes linked).2 paired
    (selected.trans (congrArg some root)) embedder (.cons install.step tail) compare⟩

private theorem compilerRefusedCallback {route : GiveEffectRoute} {request : CoreGiveRequest bindings start}
    (selection : request.Selected route) {issue label next} (refused : selection.preflight = .error issue)
    (install : GiveInstall bindings (specDispatch ready base) start label next)
    (run : Steps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle = some selection.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    CallbackSlice profile ready base bindings older start incoming labels finish := by
  have reads handle (demand : request.lookupDemand = some handle) :
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted handle := by
    rw [selection.lookup_demand] at demand
    cases demand
    exact selection.selected.trans selected.symm
  obtain ⟨count, checked⟩ := selection.compiler_refusal_tracks (profile := profile) (ready := ready) refused base embedder
  cases alignLocalBody (checked (.active 0 0)).steps run (noBranchOfVisible (visibleTaus count) (by simp)) with
  | inside _ nonempty tail => exact callbackTerminalSlice paired (.entryPrefix install run nonempty tail)
  | reached split tail =>
    obtain ⟨_, _, quiet, canonical, host, pending⟩ := selection.paired_canonical_pending_tracks
      (profile := profile) (ready := ready) (base := base) paired reads
    rw [split]
    exact callbackTerminalSlice paired (.compilerRefused selection install refused checked canonical (silentVisible quiet) pending host tail)

private theorem rootRefusedCallback {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) {issue checkLeading label next}
    (install : GiveInstall bindings (specDispatch ready base) site.start label next)
    (quiet : PayloadPrefix.visible checkLeading = [])
    (checked : site.EntryPrefix profile ready base checkLeading (site.withBody (site.reply (.error issue))))
    (run : Steps profile ready (specDispatch ready base) site.start labels finish)
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree) :
    CallbackSlice profile ready base bindings older site.start incoming labels finish := by
  let reply := route.reply site.destination site.start.host.nextTicket (.error issue)
  let stopped := site.withBody (site.reply (.error issue))
  have completed := Plain.give_completion_steps (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    (start := stopped) reply rfl
  have front := (checked (.active 0 0)).toTrail.steps
  have silent : PayloadPrefix.visible (checkLeading ++ ([.tau, .tau, .tau] : Trace grow sig)) = [] := by
    rw [visibleAppend, quiet]
    rfl
  cases alignLocalBody (append front completed) run (noBranchOfVisible silent (by simp)) with
  | inside _ nonempty tail => exact callbackTerminalSlice paired (.entryPrefix install run nonempty tail)
  | @reached suffix split tail =>
    obtain ⟨_, entered, canonQuiet, canonical, _, _⟩ := LiveDispatch.entry_paired_tracks
      (profile := profile) (ready := ready) (base := base) site linked paired selected
    rw [split, List.append_assoc]
    refine callbackTerminalSlice paired (.refused (route := route) (destination := site.destination)
      (ticket := site.start.host.nextTicket) (issue := issue) (left := stopped) (right := entered)
      install ((silentVisible canonQuiet).trans quiet.symm) ?_)
    refine ⟨suffix, _, rfl, front, completed, tail, rfl, rfl, fun place => ?_⟩
    cases place with
    | none => exact ⟨none, none, .absent (append front completed), .absent (canonical (.active 0 0)).toTrail.steps⟩
    | some place =>
      exact ⟨_, _, (checked place).toTrail.append (Plain.give_completion_trail (start := stopped) reply (site.entryPlace place) rfl),
        (canonical place).toTrail⟩

theorem actualSelectedMemoryCallback {pointer : FlatValue} {request : CoreGiveRequest bindings start}
    (selection : request.Selected (.memory pointer)) {label next}
    (install : GiveInstall bindings (specDispatch ready base) start label next)
    (tail : Steps profile ready (specDispatch ready base) next labels finish)
    (paired : HostFrame.Related.Paired older start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle = some selection.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (compare : ShorterCallbackSlices profile ready base bindings (label :: labels).length) :
    CallbackSlice profile ready base bindings older start incoming (label :: labels) finish := by
  have run := Steps.cons install.step tail
  cases compiled : selection.preflight with
  | error issue => exact compilerRefusedCallback selection compiled install run paired selected embedder
  | ok result =>
    obtain ⟨field, plan⟩ := result
    obtain ⟨tag, payload, arity, children, root, linked, cut⟩ :=
      actualSelectedMemoryRequest selection compiled install tail paired selected embedder compare
    let site := selection.site tag payload arity children field
    have chosen : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree :=
      selected.trans (congrArg some root)
    cases cut with
    | refused issue quiet entered => exact rootRefusedCallback site linked install quiet entered run paired chosen
    | placementTrap reason count verdict entered =>
      have quiet : PayloadPrefix.visible (List.replicate count .tau ++ ([.trap reason] : Trace grow sig)) = [.trap reason] := by
        rw [visibleAppend, visibleTaus]
        rfl
      cases alignLocalBody (entered (.active 0 0)).steps run (noBranchOfVisible quiet (by simp [workerBranchLabel])) with
      | inside _ nonempty tail => exact callbackTerminalSlice paired (.entryPrefix install run nonempty tail)
      | reached split tail =>
        obtain ⟨_, _, canonQuiet, canonical, pending, host⟩ := LiveDispatch.entry_paired_tracks
          (profile := profile) (ready := ready) (base := base) site linked paired chosen
        rw [split]
        exact callbackTerminalSlice paired (.placementTrap site install verdict entered canonical (silentVisible canonQuiet) pending host tail)
    | placed _ _ _ _ body =>
      obtain ⟨_, _, _, _, compare⟩ := body
      exact compare install

open ABI PayloadPrefix ReturnFrame.Occurrence Stored.Endpoints.RecordLower Stored.OwnedMemory.Claims in
private theorem driveFlatGiveBody {schema : Stored.TypeOf} (site : PayloadRoot.Site grow sig (.flat schema))
    (linked : site.Linked bindings) (shape : FlatVisitShape site.field)
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (fits : Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
    {label next} (install : GiveInstall bindings (specDispatch ready base) site.start label next)
    {checkEntry actual : Trace grow sig} {budget : Nat}
    (entered : site.EntryPrefix profile ready base checkEntry site.checked) (silent : visible checkEntry = [])
    (run : Steps profile ready (specDispatch ready base) site.checked actual finish) (bounded : actual.length ≤ budget)
    (compare : ShorterCallbackSlices profile ready base bindings budget) :
    CallbackSlice profile ready base bindings older site.start incoming (checkEntry ++ actual) finish := by
  obtain ⟨plan, compiled⟩ := linked.compiled
  have matched := Record.preflightValue_layout _ _ _ _ _ plan compiled
  have fit := Record.preflightValue_value _ _ _ _ _ plan compiled ▸ fits
  have width := site.destination.check_width site.start.store linked.destination
  obtain ⟨entry, peerEntry, quiet, installed, related, _, storage⟩ :=
    LiveDispatch.entry_paired_storage (profile := profile) (ready := ready) (base := base) site linked paired selected
  obtain ⟨peer, frame, canonAt⟩ := CallbackRange.referenceFrame site (site.reference_at linked site.referenceReply) related
  obtain ⟨checked, canonical, trailing, left, right, marks, split, seen, storePaths, store, residual, endpoint⟩ :=
    driveCompiledFlat (origin := site.checked.store) site.destination site.inst shape matched fit
      (CallbackRange.preflightAllocator site linked) (.self _) embedder width compare
      0 site.reply site.referenceReply site.checked peerEntry site.cursor peer frame (Core3.Grows.refl _) rfl canonAt actual finish run bounded
  obtain ⟨move, paths, outside⟩ := storePaths
  obtain ⟨atEntry, track, frameEntry⟩ := CallbackRange.publicEntryTransport site linked entered installed storage
  let caller := move (some (.active 0 0))
  have leading (place : Option Location) :
      Trail profile ready (specDispatch ready base) site.start place (checkEntry ++ checked) left (move (atEntry place)) ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming place
        (entry ++ canonical) right (move (atEntry place)) :=
    ⟨(track place).1.append (paths (atEntry place)).1, (track place).2.append (paths (atEntry place)).2⟩
  have rebased : OccurrenceTransport profile ready base bindings site.start incoming
      (checkEntry ++ checked) (entry ++ canonical) left right (marks ++ [caller]) := by
    refine ⟨move ∘ atEntry, leading, fun changes retained prior => ?_⟩
    simpa only [List.append_assoc, List.map_append, List.map_cons, List.map_map, List.map_nil, caller]
      using outside changes _ (frameEntry changes retained prior)
  have observed : visible (checkEntry ++ checked) = visible (entry ++ canonical) := by
    rw [visibleAppend, visibleAppend, silent, silentVisible quiet, seen]
  have total : checkEntry ++ actual = (checkEntry ++ checked) ++ trailing := by rw [split, List.append_assoc]
  have cut : GiveBodyCut profile ready base bindings site.start incoming left right (checkEntry ++ checked)
      (entry ++ canonical) trailing finish (marks ++ [caller]) := ⟨observed, store, rebased, residual⟩
  have stop (why : GiveBodyStop profile ready base left right trailing finish caller) :
      CallbackSlice profile ready base bindings older site.start incoming (checkEntry ++ actual) finish :=
    total ▸ callbackTerminalSlice paired (.body install cut why)
  cases endpoint with
  | trap lhs rhs => exact stop (.trap lhs rhs)
  | localPrefix nonempty tail => exact stop (.localPrefix nonempty tail)
  | localChoice divided choice shared step tail => exact stop (.localChoice divided choice shared step tail)
  | installPrefix short => exact stop (.allocatorInstall short)
  | collectionInstall short => exact stop (.allocatorInstall short)
  | collectionRange nonempty tail => exact stop (.localPrefix nonempty tail)
  | callback tracked aligned ending notPopped =>
    rw [total]
    exact callbackTerminalSlice paired (.allocator install cut tracked aligned ending notPopped)
  | @descriptor pointer check canon arrived =>
    by_cases active : caller = some (.active 0 0)
    · have marked := (paths (some (.active 0 0))).1
      change move (some (.active 0 0)) = some (.active 0 0) at active
      rw [active] at marked
      obtain ⟨_, equal, original⟩ := marked.survives
      cases equal
      cases arrived with
      | returned words returned _ checkAt canonAt =>
        rw [List.nil_append, show caller = some (.active 0 0) from active] at rebased
        rcases consumeGiveCommonReply site words split residual rebased original returned checkAt canonAt observed bounded compare with
          short | ⟨suffix, replied, peer, divided, _, tail, _, _, result⟩
        · exact stop (.replyPrefix none short)
        rcases result with ⟨_, compared⟩ | ⟨update, aligned, trails⟩
        · exact compared
        · rw [total, divided, ← List.append_assoc]
          exact callbackTerminalSlice paired (.uncertified install update aligned trails tail)
      | refused issue checkAt =>
        obtain ⟨segments, frames⟩ := site.reached_caller checkAt original
        let reply := (GiveEffectRoute.flat schema).reply site.destination site.start.host.nextTicket (.error issue)
        have atReply : left.ctl = ⟨check.thread, .prog (do return .flat (← writeCompletion reply)),
            .core site.core site.resume :: segments⟩ :: check.rest := by
          simpa only [Cursor.control, frames, PayloadRoot.Site.reply, reply] using! checkAt
        have completed := Plain.give_completion_steps (profile := profile) (ready := ready)
          (dispatch := specDispatch ready base) reply atReply
        rcases splitSilent (count := 3) completed residual with ⟨suffix, divided, tail⟩ | short
        · have stopped : CheckedOnlyGiveReply profile ready base bindings (.flat schema) site.destination site.start.host.nextTicket
              issue site.start incoming left right (checkEntry ++ checked) (entry ++ canonical) trailing finish := by
            refine ⟨suffix, _, divided, (leading none).1.steps, completed, tail, rfl, rfl, fun place => ?_⟩
            obtain ⟨checkedLead, canonicalLead⟩ := leading place
            cases reached : move (atEntry place) with
            | none =>
              rw [reached] at checkedLead canonicalLead
              exact ⟨none, none, checkedLead.append (.absent completed), canonicalLead⟩
            | some prior =>
              rw [reached] at checkedLead canonicalLead
              exact ⟨_, some prior, checkedLead.append (Plain.give_completion_trail reply prior atReply), canonicalLead⟩
          rw [total]
          exact callbackTerminalSlice paired (.refused install observed.symm stopped)
        · exact stop (.replyPrefix (some issue) short)
    · cases arrived with
      | returned => exact stop (.callerNotTop none active)
      | refused issue _ => exact stop (.callerNotTop (some issue) active)

private theorem actualSelectedFlatCallback {schema : Stored.TypeOf} {request : CoreGiveRequest bindings start}
    (selection : request.Selected (.flat schema)) {label next}
    (install : GiveInstall bindings (specDispatch ready base) start label next)
    (tail : Steps profile ready (specDispatch ready base) next labels finish)
    (paired : HostFrame.Related.Paired older start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle = some selection.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (compare : ShorterCallbackSlices profile ready base bindings (label :: labels).length) :
    CallbackSlice profile ready base bindings older start incoming (label :: labels) finish := by
  have run := Steps.cons install.step tail
  cases compiled : selection.preflight with
  | error issue => exact compilerRefusedCallback selection compiled install run paired selected embedder
  | ok result =>
    obtain ⟨field, plan⟩ := result
    obtain ⟨tag, payload, arity, children, root, linked⟩ := selection.compiler_success compiled
    let site := selection.site tag payload arity children field
    have chosen : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree :=
      selected.trans (congrArg some root)
    have cut := site.parked_after_admission (profile := profile) (ready := ready) linked
      (Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
      (fun fits _ _ => fits) base embedder
    cases cut with
    | refused issue quiet entered => exact rootRefusedCallback site linked install quiet entered run paired chosen
    | placementTrap reason count verdict entered => cases verdict
    | @placed entry quiet verdict prepared entered fits =>
      cases alignLocalBody (entered (.active 0 0)).toTrail.steps run (noBranchOfVisible quiet (by simp)) with
      | inside _ nonempty tail => exact callbackTerminalSlice paired (.entryPrefix install run nonempty tail)
      | @reached remaining split tail =>
        have bounded : remaining.length ≤ (label :: labels).length := by rw [split, List.length_append]; omega
        exact split ▸ driveFlatGiveBody site linked (siteVisitShapes linked).1 paired chosen embedder fits install entered quiet tail bounded compare

private theorem admissionRefusalCallback (request : CoreGiveRequest bindings start) {issue label next}
    (refused : Plain.runBody request.selectionProgram start.store start.host (some request.thread) =
      (start.store, start.host, .ok (.error issue)))
    (install : GiveInstall bindings (specDispatch ready base) start label next)
    (actual : Steps profile ready (specDispatch ready base) next labels finish)
    (paired : HostFrame.Related.Paired older start incoming)
    (reads : ∀ handle, request.lookupDemand = some handle →
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted handle)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (compare : ShorterCallbackSlices profile ready base bindings (label :: labels).length) :
    CallbackSlice profile ready base bindings older start incoming (label :: labels) finish := by
  obtain ⟨leftCount, _, _, _, positive, checked, canonical, after, _, _⟩ := request.paired_admission_refusal_tracks
    (profile := profile) (ready := ready) (base := base) base embedder paired refused reads
  have run := Steps.cons install.step actual
  have transport := CallbackPrefix.stationaryTransport checked canonical
  have front := (checked (.active 0 0)).toTrail.steps
  cases alignLocalBody front run (noBranchOfVisible (visibleTaus leftCount) (by simp)) with
  | inside _ nonempty tail => exact callbackTerminalSlice paired (.entryPrefix install run nonempty tail)
  | @reached suffix split residual =>
    have smaller : suffix.length < (label :: labels).length := by
      rw [split, List.length_append, List.length_replicate]
      omega
    rcases classifyReachedGrowth front with certified | uncertified
    · obtain ⟨checked, canonical, trailing, reached, peer, divided, segment, ending⟩ := compare smaller residual after
      have leading : ExecutedCallbackSegment profile ready base bindings older start incoming _ _ _ _ :=
        ⟨certified, (visibleTaus _).trans (visibleTaus _).symm, after, transport⟩
      exact ⟨_, _, trailing, reached, peer, by rw [split, divided, List.append_assoc],
        CallbackPrefix.appendExecutedCallbacks leading segment, ending⟩
    · rw [split]
      exact callbackTerminalSlice paired (.uncertified install uncertified after transport residual)

open ReturnFrame.Occurrence in
private theorem directGivePreludePath (impl : HostImpl (core3 grow) (HostState sig))
    (name : String) (kind : V1.FuncType) (args : List FlatValue)
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = check.control (specDispatch ready impl (.hostCallout (.embedder name kind) args))) :
    ComponentQuietPath profile ready (specDispatch ready impl) check start [id, id]
      { start with ctl := check.control (calloutBody Limits.spec Quirks.none ready impl start.store
        check.thread (.embedder name kind) args) } := by
  cases check with
  | mk thread frames rest =>
    refine .step (.currentThread focused) (by rw [transitionEdit, focused]; rfl) ?_
    exact .step (.get rfl) rfl (.done _)

open ReturnFrame.Occurrence in
private theorem quietCheckedShort {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {updates : List (ComponentStoreEdit grow)} {target : Config (core3 grow) (HostState sig)}
    (path : ComponentQuietPath profile ready (specDispatch ready base) check start updates target)
    (run : Steps profile ready (specDispatch ready base) start labels finish) (short : labels.length < updates.length) :
    PayloadPrefix.visible labels = [] ∧
      ∀ place, Prefix profile ready (specDispatch ready base) start place labels finish place := by
  induction path generalizing labels with
  | done => simp at short
  | step planned stationary _ ih =>
    cases run with
    | refl => exact ⟨rfl, fun _ => .done _ _⟩
    | cons actual tail =>
      obtain ⟨rfl, rfl⟩ := silentStepUnique planned actual
      obtain ⟨seen, tracks⟩ := ih tail (by simpa using short)
      exact ⟨(visibleTauCons _).trans seen, fun place => .step planned
        (by rw [stationary]; rfl) (tracks place)⟩

open ReturnFrame.Occurrence in
private theorem directHostCheckedPath (name : String) (kind : V1.FuncType) (args : List FlatValue)
    (destination : RecordDestination) (schema : Option Stored.TypeOf) (inst : InstId)
    (linked : resolveBinding bindings name kind = .ok ⟨name, inst, Option.elim schema (.givePayload destination) (.giveFlat destination)⟩)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (hostFrame : check.thread = none)
    (focused : start.ctl = check.control (calloutBody Limits.spec Quirks.none ready base start.store check.thread (.embedder name kind) args)) :
    let reply := giveAdmissionReply start.host.nextTicket destination schema .wrongContext
    ComponentQuietPath profile ready (specDispatch ready base) check start [id, id, id, id, id, id]
      { start with host := (start.host.enter name kind args).record reply.1, ctl := check.control (.pure (.flat reply.2)) } := by
  cases check with
  | mk thread frames rest =>
    change thread = none at hostFrame
    subst thread
    cases schema <;>
      simp only [calloutBody, PayloadPrefix.Cursor.control, threadMayLeave, instOfThread?, embedder,
        Scheduled.host, dispatchImport, route, linked, Option.elim, invoke, giveFlat, currentInst?, currentTask?,
        Prog.bind_eq, Prog.bind_assoc] at focused
    all_goals
      refine .step (.hostGet focused) (by rw [transitionEdit, focused]; rfl) ?_
      refine .step (.hostSet rfl) rfl (.step (.currentThread rfl) rfl (.step (.get rfl) rfl ?_))
      exact .step (.hostGet rfl) rfl (.step (.hostSet rfl) rfl (.done _))

open ReturnFrame.Occurrence in
private theorem directHostCanonicalPath (name : String) (kind : V1.FuncType) (args : List FlatValue)
    (destination : RecordDestination) (schema : Option Stored.TypeOf) (inst : InstId) (ticket : Nat)
    (linked : resolveBinding bindings name kind = .ok ⟨name, inst, Option.elim schema (.givePayload destination) (.giveFlat destination)⟩)
    (canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (hostFrame : canon.thread = none)
    (focused : start.ctl = canon.control (calloutBody Limits.spec Quirks.none ready (LiveDispatch.host bindings base)
      start.store canon.thread (.embedder name kind) args)) :
    let reply := giveAdmissionReply ticket destination schema .wrongContext
    ComponentQuietPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) canon start [id, id]
      { start with ctl := canon.control (.pure (.flat reply.2)) } := by
  cases canon with
  | mk thread frames rest =>
    change thread = none at hostFrame
    subst thread
    cases schema <;>
      simp only [calloutBody, PayloadPrefix.Cursor.control, threadMayLeave, instOfThread?,
        LiveDispatch.host, selectBinding, linked, Option.elim, memoryWords, flatWords, admit, currentInst?, currentTask?,
        Prog.bind_eq, Prog.bind_assoc] at focused
    all_goals exact .step (.currentThread focused) (by rw [transitionEdit, focused]; rfl) (.step (.get rfl) rfl (.done _))

open ReturnFrame.Occurrence in
private theorem cutDirectHostRefusal (name : String) (kind : V1.FuncType) (args : List FlatValue)
    (destination : RecordDestination) (schema : Option Stored.TypeOf) (inst : InstId)
    (linked : resolveBinding bindings name kind = .ok ⟨name, inst, Option.elim schema (.givePayload destination) (.giveFlat destination)⟩)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFrame : check.thread = none) (rightFrame : canon.thread = none)
    (leftFocus : left.ctl = check.control (calloutBody Limits.spec Quirks.none ready base left.store check.thread (.embedder name kind) args))
    (rightFocus : right.ctl = canon.control (calloutBody Limits.spec Quirks.none ready (LiveDispatch.host bindings base)
      right.store canon.thread (.embedder name kind) args))
    (site : PairedComponentSite older left right check canon)
    (prelude : OccurrenceTransport profile ready base bindings start incoming [.tau, .tau, .tau] [.tau, .tau, .tau]
      left right [some (.active 0 0)])
    (run : Steps profile ready (specDispatch ready base) left labels finish) :
    DirectHostRefusalCut profile ready base bindings older name kind args destination schema check canon start incoming left right labels finish := by
  have checked := directHostCheckedPath (profile := profile) name kind args destination schema inst linked embedder check leftFrame leftFocus
  have canonical := directHostCanonicalPath (profile := profile) name kind args destination schema inst left.host.nextTicket linked canon rightFrame rightFocus
  rcases splitSilent (count := 6) (checked.track (.active 0 0)).toTrail.steps run with ⟨trailing, split, residual⟩ | short
  · let reply := giveAdmissionReply left.host.nextTicket destination schema .wrongContext
    let leftReply := { left with host := (left.host.enter name kind args).record reply.1, ctl := check.control (.pure (.flat reply.2)) }
    let rightReply := { right with ctl := canon.control (.pure (.flat reply.2)) }
    have pairedReply : PairedComponentSite older leftReply rightReply check canon := by
      simpa only [PairedComponentSite, HostFrame.Related.Paired, HostFrame.replace, leftReply, rightReply] using site
    exact .inr ⟨trailing, leftReply, rightReply, split,
      retainComparedOccurrences prelude (fun place => ⟨checked.track place, canonical.track place⟩),
      rfl, rfl, rfl, rfl, pairedReply, residual⟩
  · obtain ⟨seen, tracks⟩ := quietCheckedShort checked run short
    exact .inl ⟨short, seen, retainComparedOccurrences prelude (fun place => ⟨tracks place, .done _ place⟩)⟩

open ReturnFrame.Occurrence in
private theorem cutDirectGivePrelude (name : String) (kind : V1.FuncType) (args : List FlatValue)
    (destination : RecordDestination) (schema : Option Stored.TypeOf) (inst : InstId)
    (linked : resolveBinding bindings name kind = .ok ⟨name, inst, Option.elim schema (.givePayload destination) (.giveFlat destination)⟩)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftFocus : left.ctl = check.control (specDispatch ready base (.hostCallout (.embedder name kind) args)))
    (rightFocus : right.ctl = canon.control (specDispatch ready (LiveDispatch.host bindings base) (.hostCallout (.embedder name kind) args)))
    (site : PairedComponentSite older left right check canon)
    (installed : OccurrenceTransport profile ready base bindings start incoming [.tau] [.tau] left right [some (.active 0 0)])
    (run : Steps profile ready (specDispatch ready base) left labels finish) :
    DirectGivePreludeCut profile ready base bindings older name kind args destination schema check canon start incoming left right labels finish := by
  have checked := directGivePreludePath (profile := profile) base name kind args check leftFocus
  have canonical := directGivePreludePath (profile := profile) (LiveDispatch.host bindings base) name kind args canon rightFocus
  rcases splitSilent (count := 2) (checked.track (.active 0 0)).toTrail.steps run with ⟨trailing, split, residual⟩ | short
  · let leftBody := { left with ctl := check.control (calloutBody Limits.spec Quirks.none ready base
        left.store check.thread (.embedder name kind) args) }
    let rightBody := { right with ctl := canon.control (calloutBody Limits.spec Quirks.none ready (LiveDispatch.host bindings base)
        right.store canon.thread (.embedder name kind) args) }
    have paths : OccurrenceTransport profile ready base bindings start incoming [.tau, .tau, .tau] [.tau, .tau, .tau]
        leftBody rightBody [some (.active 0 0)] :=
      retainComparedOccurrences installed (fun place => ⟨checked.track place, canonical.track place⟩)
    exact .inr ⟨trailing, leftBody, rightBody, split, rfl, rfl, rfl, rfl, rfl, rfl, site, paths, residual,
      fun leftFrame rightFrame => cutDirectHostRefusal name kind args destination schema inst linked embedder
        leftFrame rightFrame rfl rfl site paths residual⟩
  · exact .inl (compareQuietShort checked canonical site ⟨_, leftFocus⟩ ⟨_, rightFocus⟩ run short)

private theorem pairComponentFocus {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {program}
    (left : start.ctl = check.control program) (right : incoming.ctl = canon.control program)
    (paired : PairedComponentSite older start incoming check canon) :
    HostFrame.Related.Paired older start incoming := by
  obtain ⟨frames, rest, shape, retargeted⟩ := paired.retarget
    (thread := check.thread) (frames := check.frames) (rest := check.rest) rfl (.prog program) start.host incoming.host
  simp only [PayloadPrefix.Cursor.control, List.cons.injEq, Activation.mk.injEq, true_and] at shape
  obtain ⟨⟨thread, rfl⟩, rfl⟩ := shape
  have leftExact : { start with ctl := check.control program } = start := by rw [← left]
  have rightExact : { incoming with ctl := canon.control program } = incoming := by rw [← right]
  rw [← leftExact, ← rightExact]
  simpa only [PayloadPrefix.Cursor.control, thread] using retargeted

private theorem pairAfterComponentPop {left right : Config (core3 grow) (HostState sig)}
    {after canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {program : Session grow sig (Ret (core3 grow))}
    (frame : LinkedCallback.ChildFrameOver older left right after canon) :
    HostFrame.Related.Paired older { left with ctl := after.control program } { right with ctl := canon.control program } := by
  have control : List.Forall₂ (ReturnFrame.Related.Active older) (after.control program) (canon.control program) := by
    unfold PayloadPrefix.Cursor.control
    rw [← frame.thread]
    exact .cons (.mk frame.frames) frame.rest
  have result := ReturnFrame.Related.Paired.mk (left := { left with host := right.host, ctl := after.control program }) control frame.blocked
  have sameStore := frame.store
  have samePending := frame.pending
  have sameResults := frame.results
  have sameCancels := frame.cancels
  unfold HostFrame.Related.Paired HostFrame.replace
  cases left
  cases right
  dsimp only at sameStore samePending sameResults sameCancels
  rw [← sameStore, ← samePending, ← sameResults, ← sameCancels]
  exact result

open ReturnFrame.Occurrence in
private theorem crossDirectGiveRefusal {left right : Config (core3 grow) (HostState sig)}
    {after canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {resume : ReturnFrame.Continuation (core3 grow) (HostState sig)} {words : List FlatValue}
    {used live suffix : Trace grow sig}
    (split : labels = used ++ suffix)
    (paths : OccurrenceTransport profile ready base bindings start incoming (.tau :: used) live left right [some (.active 0 0)])
    (observed : PayloadPrefix.visible live = PayloadPrefix.visible (.tau :: used))
    (startPair : HostFrame.Related.Paired older start incoming)
    (site : PairedComponentSite older left right { after with frames := .prog resume :: after.frames }
      { canon with frames := .prog resume :: canon.frames })
    (leftAt : left.ctl = { after with frames := .prog resume :: after.frames }.control (.pure (.flat words)))
    (rightAt : right.ctl = { canon with frames := .prog resume :: canon.frames }.control (.pure (.flat words)))
    (run : Steps profile ready (specDispatch ready base) left suffix finish)
    (boundary : CallbackSlice profile ready base bindings older start incoming (.tau :: labels) finish) :
    CallbackCrossingAt profile ready base bindings older start incoming .tau labels finish := by
  cases run with
  | refl => exact .inr boundary
  | @cons _ _ _ _ remaining step tail =>
    have paired := pairComponentFocus leftAt rightAt site
    have unmarked : OutsideMarks older (segmentStorage start) (segmentStorage incoming) [] :=
      fun place _ => paired_outside (left := HostFrame.replace start incoming.host) startPair place (by simp)
    have outside : Outside older (segmentStorage left) (segmentStorage right) (some (.active 0 0)) :=
      outsideMarks_singleton.mp (paths.choose_spec.2 older [] unmarked)
    have rightTop : segmentAt (segmentStorage right) (.active 0 0) = some (.prog resume) := by
      rw [segmentStorage, rightAt]
      rfl
    obtain ⟨peerCursor, frame, peerAt⟩ := LinkedCallback.marked_pop_frame paired outside leftAt rightTop
    have pop : Step profile ready (specDispatch ready base) left .tau { left with ctl := after.control (resume (.flat words)) } :=
      .popProg leftAt
    obtain ⟨rfl, rfl⟩ := silentStepUnique pop step
    have whole := CallbackPrefix.transportAllocatorPop leftAt peerAt paths
    rcases classifyReachedGrowth (CallbackPrefix.transportPaths whole none).choose_spec.1.steps with growing | _
    · refine .inl ⟨used ++ [.tau], live ++ [.tau], remaining,
        { left with ctl := after.control (resume (.flat words)) },
        { right with ctl := peerCursor.control (resume (.flat words)) }, ?_, ?_, tail⟩
      · rw [split, List.append_assoc]
        rfl
      · exact ⟨by simpa only [List.cons_append] using growing,
          by rw [← List.cons_append, visibleAppend, visibleAppend, observed],
          pairAfterComponentPop frame, by simpa only [List.cons_append, List.map_nil] using whole⟩
    · exact .inr boundary

open ReturnFrame.Occurrence in
private theorem directRefusalBodyTracks (impl : HostImpl (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (body : Session grow sig (Ret (core3 grow)))
    {journal : HostState sig} {words : List FlatValue}
    (focus : start.ctl = check.control body)
    (evaluated : Plain.runBody body start.store start.host (some check.thread) = (start.store, journal, .ok (.flat words))) :
    ∃ count, ∀ place, Prefix profile ready (specDispatch ready impl) start place (List.replicate count .tau)
      { start with host := journal, ctl := check.control (.pure (.flat words)) } place := by
  have focused : start.ctl = check.control (body >>= Prog.pure) := by
    simpa only [Prog.bind_eq, Prog.bind_pure] using focus
  obtain ⟨labels, silent, paths⟩ := Plain.runBody_thread_tracks_all body start start.store journal (.flat words) Prog.pure
    check.thread check.frames check.rest profile ready (specDispatch ready impl) focused evaluated
  have replicated : labels = List.replicate labels.length .tau := List.eq_replicate_length.mpr (fun label member => by
    have tau := List.all_eq_true.mp silent label member
    cases label <;> first | rfl | contradiction)
  exact ⟨labels.length, replicated ▸ paths⟩

open ReturnFrame.Occurrence in
private theorem crossActiveDirectGiveRefusal (request : GiveSelector bindings) (worker : ThreadId)
    {left right : Config (core3 grow) (HostState sig)} {resume frames rest peerFrames peerRest} {bodyLabels}
    (entered : labels = [.tau, .tau] ++ bodyLabels)
    (leftAt : left.ctl = (PayloadPrefix.Cursor.mk (some worker) (.prog resume :: frames) rest).control
      (calloutBody Limits.spec Quirks.none ready base left.store (some worker) (.embedder request.name request.kind) request.args))
    (rightAt : right.ctl = (PayloadPrefix.Cursor.mk (some worker) (.prog resume :: peerFrames) peerRest).control
      (calloutBody Limits.spec Quirks.none ready (LiveDispatch.host bindings base) right.store (some worker)
        (.embedder request.name request.kind) request.args))
    (site : PairedComponentSite older left right ⟨some worker, .prog resume :: frames, rest⟩
      ⟨some worker, .prog resume :: peerFrames, peerRest⟩)
    (paths : OccurrenceTransport profile ready base bindings start incoming [.tau, .tau, .tau] [.tau, .tau, .tau]
      left right [some (.active 0 0)])
    (run : Steps profile ready (specDispatch ready base) left bodyLabels finish)
    (paired : HostFrame.Related.Paired older start incoming)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (boundary : CallbackSlice profile ready base bindings older start incoming (.tau :: labels) finish) :
    CallbackCrossingAt profile ready base bindings older start incoming .tau labels finish := by
  classical
  rcases request.result left (some worker) with trapped | ⟨verdict, selected⟩
  · exact .inr boundary
  cases verdict with
  | ok => exact .inr boundary
  | error issue =>
    by_cases reads : ∀ handle, request.lookupDemand left.store (some worker) = some handle →
      Stored.Endpoints.Core.childFromHistory left.host.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory right.host.writer.accepted handle
    · obtain ⟨checked, canonical⟩ := request.refusal_bodies (ready := ready) (base := base) left (some worker) right.host base embedder selected reads
      have sameStore := site.data.1
      obtain ⟨checkCount, leftPath⟩ := directRefusalBodyTracks (profile := profile) (ready := ready) base _ _ leftAt checked
      obtain ⟨canonCount, rightPath⟩ := directRefusalBodyTracks (profile := profile) (ready := ready) (LiveDispatch.host bindings base)
        _ _ rightAt (sameStore ▸ canonical)
      rcases splitSilent (count := checkCount) (leftPath (.active 0 0)).toTrail.steps run with ⟨remaining, split, residual⟩ | short
      · have moved := retainComparedOccurrences paths (fun place => ⟨leftPath place, rightPath place⟩)
        have whole : labels = ([.tau, .tau] ++ List.replicate checkCount .tau) ++ remaining := by rw [entered, split, List.append_assoc]
        have seen : PayloadPrefix.visible ([.tau, .tau, .tau] ++ List.replicate canonCount .tau : Trace grow sig) =
            PayloadPrefix.visible (.tau :: ([.tau, .tau] ++ List.replicate checkCount .tau)) := by
          simp only [List.cons_append, List.nil_append, visibleTauCons, visibleTaus]
        exact crossDirectGiveRefusal (after := ⟨some worker, frames, rest⟩) (canon := ⟨some worker, peerFrames, peerRest⟩)
          whole moved seen paired (by simpa only [PairedComponentSite, HostFrame.Related.Paired, HostFrame.replace] using site)
          rfl rfl residual boundary
      · exact .inr boundary
    · exact .inr boundary

private theorem classifiedGiveCrossing
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    CallbackGiveCrossing profile ready base bindings := by
  classical
  intro changes checked canonical next finish label trailing install actual paired compare
  have run := Steps.cons install.step actual
  rcases install.request with ⟨⟨request⟩⟩ | direct
  · apply Or.inr
    by_cases reads : ∀ handle, request.lookupDemand = some handle →
        Stored.Endpoints.Core.childFromHistory checked.host.writer.accepted handle =
          Stored.Endpoints.Core.childFromHistory canonical.host.writer.accepted handle
    · rcases request.selector_result with ⟨reason, trap⟩ | ⟨verdict, evaluated⟩
      · obtain ⟨leftCount, _, left, right⟩ := request.paired_admission_trap
          (profile := profile) (ready := ready) (base := base) base embedder paired trap
        have seen : PayloadPrefix.visible (List.replicate leftCount .tau ++ ([.trap reason] : Trace grow sig)) = [.trap reason] := by
          rw [visibleAppend, visibleTaus]
          rfl
        cases alignLocalBody left run (noBranchOfVisible seen (by simp [workerBranchLabel])) with
        | inside _ nonempty tail => exact callbackTerminalSlice paired (.entryPrefix install run nonempty tail)
        | reached split residual =>
          rw [split]
          exact callbackTerminalSlice paired (.admissionTrap request install trap left right residual)
      · cases verdict with
        | error issue => exact admissionRefusalCallback request evaluated install actual paired reads embedder compare
        | ok result =>
          obtain ⟨route, ⟨selection⟩⟩ := request.selected_of_return evaluated
          have selected := (reads selection.handle selection.lookup_demand).symm.trans selection.selected
          cases route with
          | flat schema =>
            exact actualSelectedFlatCallback selection install actual paired selected embedder compare
          | memory pointer =>
            exact actualSelectedMemoryCallback selection install actual paired selected embedder compare
    · push Not at reads
      obtain ⟨handle, demand, different⟩ := reads
      exact callbackTerminalSlice paired (.lookup request install demand different actual)
  · obtain ⟨name, kind, args, thread, resume, frames, rest, inst, destination, schema, focused, linked⟩ := direct
    obtain ⟨peerFrames, peerRest, rfl, rfl, site, paths, leftMark, rightMark, _⟩ :=
      cutProgramCallInstall (bindings := bindings) (.prog (.pure (.cancel .none))) focused install.step paired
    let check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨thread, .prog resume :: frames, rest⟩
    let canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) := ⟨thread, .prog resume :: peerFrames, peerRest⟩
    have prelude := cutDirectGivePrelude name kind args destination schema inst linked embedder
      (check := check) (canon := canon) rfl rfl site paths actual
    have boundary := callbackTerminalSlice paired (.directGiveEntry (check := check) (canon := canon)
      linked rfl rfl site paths leftMark rightMark prelude actual)
    rcases prelude with _ | ⟨_, body, peerBody, entered, _, _, _, _, bodyAt, peerAt, bodySite, bodyPaths, bodyRun, refuse⟩
    · exact .inr boundary
    cases thread with
    | some worker =>
      exact crossActiveDirectGiveRefusal ⟨name, kind, args, inst, destination, schema, linked⟩ worker
        entered bodyAt peerAt bodySite bodyPaths bodyRun paired embedder boundary
    | none =>
      rcases refuse rfl rfl with _ | ⟨suffix, left, right, replySplit, moved, _, _, leftAt, rightAt, replyPair, residual⟩
      · exact .inr boundary
      have split : trailing = List.replicate 8 .tau ++ suffix := by rw [entered, replySplit]; rfl
      exact crossDirectGiveRefusal (after := ⟨none, frames, rest⟩) (canon := ⟨none, peerFrames, peerRest⟩)
        split moved rfl paired replyPair leftAt rightAt residual boundary

theorem classifyGiveCallbacks
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (run : Steps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    CallbackSlice profile ready base bindings older start incoming labels finish :=
  foldCallbackSlices (classifiedGiveCrossing embedder) run paired

open ReturnFrame.Occurrence in
private theorem markTransport {leading : Trace grow sig} {peer : Config (core3 grow) (HostState sig)}
    (moved : OccurrenceTransport profile ready base bindings start incoming leading leading finish peer) :
    OccurrenceTransport profile ready base bindings start incoming leading leading finish peer [some (.active 0 0)] := by
  obtain ⟨move, paths, retained⟩ := moved
  refine ⟨move, paths, ?_⟩
  intro older marks outside place off first second left right
  exact retained older marks outside place (fun member => off (List.mem_cons_of_mem _ member)) first second left right

open ReturnFrame.Occurrence in
private theorem crossComponentReply {origin reference reached peer : Config (core3 grow) (HostState sig)}
    {used leading suffix : Trace grow sig} {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {resume : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (split : labels = used ++ suffix)
    (moved : OccurrenceTransport profile ready base bindings start incoming (.tau :: used) (.tau :: used) reached peer)
    (reply : ComponentMarkedReplyTail profile ready base bindings older origin reference reached peer leading
      check resume resume suffix finish)
    (boundary : CallbackSlice profile ready base bindings older start incoming (.tau :: labels) finish) :
    CallbackCrossingAt profile ready base bindings older start incoming .tau labels finish := by
  classical
  by_cases focus : reached.ctl = check.control (.pure (.cancel .none))
  · obtain ⟨_, _, actual⟩ := reply
    rcases actual focus with _ | ⟨after, _, pop⟩
    · exact .inr boundary
    rcases pop with _ | _ | ⟨remaining, canon, _, popped, _, residual, _, frame, _, transport⟩
    · exact .inr boundary
    · exact .inr boundary
    have whole := transport (markTransport moved)
    rcases classifyReachedGrowth (CallbackPrefix.transportPaths whole none).choose_spec.1.steps with growing | _
    · refine .inl ⟨used ++ [.tau], .tau :: (used ++ [.tau]), remaining, { reached with ctl := after.control (resume (.cancel .none)) },
        { peer with ctl := canon.control (resume (.cancel .none)) }, ?_, ?_, residual⟩
      · rw [split, popped, List.append_assoc]
        rfl
      · exact ⟨by simpa only [List.cons_append] using growing, rfl, pairAfterComponentPop frame,
          by simpa only [List.cons_append, List.map_nil] using whole⟩
    · exact .inr boundary
  · exact .inr boundary

private theorem crossComponentBodyReply
    {left right startBody peerBody reached peer : Config (core3 grow) (HostState sig)}
    {entry suffix leading remainder : Trace grow sig} {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {resume : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (installed : OccurrenceTransport profile ready base bindings start incoming [.tau] [.tau] left right)
    (entrySplit : labels = entry ++ suffix)
    (entryPath : OccurrenceTransport profile ready base bindings left right entry entry startBody peerBody)
    (bodySplit : suffix = leading ++ remainder)
    (bodyPath : OccurrenceTransport profile ready base bindings startBody peerBody leading leading reached peer)
    (reply : ComponentMarkedReplyTail profile ready base bindings older startBody peerBody reached peer leading
      check resume resume remainder finish)
    (boundary : CallbackSlice profile ready base bindings older start incoming (.tau :: labels) finish) :
    CallbackCrossingAt profile ready base bindings older start incoming .tau labels finish := by
  have prefixPath := (CallbackPrefix.transportAppend entryPath bodyPath).choose_spec.1
  have whole := (CallbackPrefix.transportAppend installed prefixPath).choose_spec.1
  have split : labels = (entry ++ leading) ++ remainder := by rw [entrySplit, bodySplit, List.append_assoc]
  have full : OccurrenceTransport profile ready base bindings start incoming (.tau :: (entry ++ leading))
      (.tau :: (entry ++ leading)) reached peer := whole
  exact crossComponentReply split full reply boundary

set_option maxHeartbeats 800000 in
private theorem classifiedComponentCrossing {callees : List (ComponentCall.Callee sig)} :
    CallbackComponentCrossing profile ready (ComponentCall.hostWithComponent (grow := grow) bindings callees) bindings := by
  classical
  intro older start incoming next finish label labels active hostId caller resume frames rest focus step tail paired
  have boundary := callbackTerminalSlice (bindings := bindings) paired (.boundary (.componentInstall focus) step tail)
  by_cases admits : ComponentHostAdmission callees hostId caller active start
  · obtain ⟨callee, subtask, cx, args, pos, ft, limits, results, entry, task, linked, record, liveThread, liveTask, context, admitted⟩ := admits
    obtain ⟨peerFrames, peerRest, rfl, rfl, entered, install, leftMark, rightMark, outside⟩ :=
      cutLinkedComponentInstall linked focus step paired
    have installed := sharedTopTransport install leftMark rightMark
    rcases cutAdmittedComponent (bindings := bindings)
        (start := { start with ctl := ⟨some active, .prog (ComponentCall.invoke callee caller), .prog resume :: frames⟩ :: rest })
        (incoming := { incoming with ctl := ⟨some active, .prog (ComponentCall.invoke callee caller), .prog resume :: peerFrames⟩ :: peerRest })
        callee caller rfl record liveThread liveTask context admitted
        entered leftMark rightMark outside tail with _ | ⟨_, _, suffix, entrySplit, moved, _, _, classified⟩
    · exact .inr boundary
    rcases classified with _ | ⟨plan, _, _, body⟩
    · exact .inr boundary
    cases plan with
    | error issue =>
      rcases body with _ | ⟨leading, remainder, reached, peer, split, path, _, _, reply⟩
      · exact .inr boundary
      · exact crossComponentBodyReply installed entrySplit moved split path reply boundary
    | ok planned =>
      obtain ⟨leading, remainder, reached, peer, split, path, _, observed⟩ := body
      cases observed with
      | pending | trapped | registrationMismatch => exact .inr boundary
      | refused _ reply | accepted _ reply => exact crossComponentBodyReply installed entrySplit moved split path reply boundary
  · exact .inr boundary

open ReturnFrame.Occurrence in
private theorem crossAsymmetricFlatCalloutExit {Observation : Type} {code : Observation → Nat} {leading canonLeading suffix reached peer}
    (used : labels = leading ++ suffix)
    (observed : PayloadPrefix.visible canonLeading = PayloadPrefix.visible leading)
    (exit : FlatCalloutExit code profile ready base bindings older reached peer suffix finish)
    (live : ∀ {thread core resume frames rest peerFrames peerRest} {observation : Observation},
      reached.ctl = ⟨thread, .prog (.pure (.flat [i32Flat (code observation)])), .core core resume :: frames⟩ :: rest →
      peer.ctl = ⟨thread, .prog (.pure (.flat [i32Flat (code observation)])), .core core resume :: peerFrames⟩ :: peerRest →
      OccurrenceTransport profile ready base bindings start incoming (.tau :: leading) (.tau :: canonLeading) reached peer)
    (terminal : suffix = [] ∨ (reached.ctl = [] ∧ peer.ctl = []) →
      CallbackSlice profile ready base bindings older start incoming (.tau :: labels) finish)
    (boundary : CallbackSlice profile ready base bindings older start incoming (.tau :: labels) finish) :
    CallbackCrossingAt profile ready base bindings older start incoming .tau labels finish := by
  cases exit with
  | exhausted empty _ => exact .inr (terminal (.inl empty))
  | trapped left right _ => exact .inr (terminal (.inr ⟨left, right⟩))
  | @rejoined observation active state resume frames rest peerFrames peerRest remaining checked canonical split residual returned pop =>
    have whole := (CallbackPrefix.transportAppend (live checked canonical) pop).choose_spec.1
    rcases classifyReachedGrowth (CallbackPrefix.transportPaths whole none).choose_spec.1.steps with growing | _
    · let replied := { reached with ctl := ⟨active,
          .core ((core3 grow).resume reached.store.core state (.values [i32Flat (code observation)])) resume, frames⟩ :: rest }
      let peerReply := { peer with ctl := ⟨active,
          .core ((core3 grow).resume peer.store.core state (.values [i32Flat (code observation)])) resume, peerFrames⟩ :: peerRest }
      refine .inl ⟨leading ++ [.tau], .tau :: (canonLeading ++ [.tau]), remaining, replied, peerReply, ?_, ?_, residual⟩
      · rw [used, split, List.append_assoc]
        rfl
      · exact ⟨by simpa only [List.cons_append] using growing,
          by simp only [visibleTauCons, visibleAppend, observed], returned,
          by simpa only [List.cons_append, List.map_nil, List.append_nil] using whole⟩
    · exact .inr boundary

open ReturnFrame.Occurrence in
private theorem crossFlatCalloutExit {Observation : Type} {code : Observation → Nat} {leading suffix reached peer}
    (used : labels = leading ++ suffix)
    (exit : FlatCalloutExit code profile ready base bindings older reached peer suffix finish)
    (live : ∀ {thread core resume frames rest peerFrames peerRest} {observation : Observation},
      reached.ctl = ⟨thread, .prog (.pure (.flat [i32Flat (code observation)])), .core core resume :: frames⟩ :: rest →
      peer.ctl = ⟨thread, .prog (.pure (.flat [i32Flat (code observation)])), .core core resume :: peerFrames⟩ :: peerRest →
      OccurrenceTransport profile ready base bindings start incoming (.tau :: leading) (.tau :: leading) reached peer)
    (terminal : suffix = [] ∨ (reached.ctl = [] ∧ peer.ctl = []) →
      CallbackSlice profile ready base bindings older start incoming (.tau :: labels) finish)
    (boundary : CallbackSlice profile ready base bindings older start incoming (.tau :: labels) finish) :
    CallbackCrossingAt profile ready base bindings older start incoming .tau labels finish :=
  crossAsymmetricFlatCalloutExit used rfl exit live terminal boundary

open ReturnFrame.Occurrence in
private theorem classifiedPollCrossing : CallbackWaitableCrossing profile ready base bindings true := by
  intro changes start incoming installed finish label labels thread core resume frames rest mem inst args focused calling step tail paired
  have boundary := callbackTerminalSlice (bindings := bindings) paired (.boundary (.pollInstall focused calling) step tail)
  obtain ⟨_, _, leading, suffix, reached, peer, split, ⟨mark, paths⟩, live, actual, frontier, exit⟩ :=
    cutPublicPoll (bindings := bindings) mem inst args focused calling step tail paired
  obtain ⟨rfl, used⟩ := List.cons.inj split
  refine crossFlatCalloutExit used exit ?_ (fun stop => callbackTerminalSlice paired ?_) boundary
  · intro _ core resume _ _ _ _ _ checked canonical
    exact sharedTopTransport (live (by rw [checked]; exact List.cons_ne_nil _ _))
      (frame := .core core resume)
      (by rw [segmentStorage, checked]; rfl) (by rw [segmentStorage, canonical]; rfl)
  · rw [used]
    exact .pollTerminal paths frontier stop actual

private theorem classifiedWaitResumeCrossing : CallbackWaitResumeCrossing profile ready base bindings := by
  intro changes start incoming next finish label labels waiter resumer afterResume frames rest core resume savedFrames mem entry
    scheduled found step tail paired
  have boundary := callbackTerminalSlice (bindings := bindings) paired (.boundary (.waitResume scheduled found) step tail)
  obtain ⟨leading, suffix, reached, peer, check, canon, split, paths, actual, frontier, exit, _⟩ :=
    cutResumedWaitDelivery (bindings := bindings) mem entry scheduled found step tail paired
  obtain ⟨rfl, used⟩ := List.cons.inj split
  refine crossFlatCalloutExit used exit (fun _ _ => paths) (fun stop => callbackTerminalSlice paired ?_) boundary
  rw [used]
  exact .waitTerminal paths frontier stop actual

private theorem classifiedCancelResumeCrossing : CallbackCancelResumeCrossing profile ready base bindings := by
  intro changes start incoming next finish label labels waiter resumer afterResume frames rest core resume savedFrames subtask
    scheduled found step tail paired
  have boundary := callbackTerminalSlice (bindings := bindings) paired (.boundary (.cancelResume scheduled found) step tail)
  obtain ⟨leading, suffix, reached, peer, split, paths, actual, exit, _⟩ :=
    cutResumedCancelFinish (bindings := bindings) subtask scheduled found step tail paired
  obtain ⟨rfl, used⟩ := List.cons.inj split
  refine crossFlatCalloutExit used exit (fun _ _ => paths) (fun stop => callbackTerminalSlice paired ?_) boundary
  rw [used]
  exact .cancelTerminal paths rfl exit stop actual

open ReturnFrame.Occurrence in
theorem cutCancelHookInstall (async : Bool) (subtask : SubtaskId) (hook : CancelRef)
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
      OccurrenceTransport profile ready base bindings start incoming [.tau] [.tau] reached peer [some (.active 0 0)] := by
  cases run with
  | refl => exact .inl ⟨rfl, rfl⟩
  | cons first tail =>
    let resume := cancelHookReturn (grow := grow) (sig := sig) async subtask
    let body := specDispatch ready base (.onCancel hook)
    let reached := { start with ctl := ⟨thread, .prog body, .prog resume :: frames⟩ :: rest }
    let peer := { incoming with ctl := ⟨thread, .prog body, .prog resume :: peerFrames⟩ :: peerRest }
    have sameDispatch : specDispatch ready (LiveDispatch.host bindings base) (.onCancel hook) = body := by cases hook <;> rfl
    have checked : Step profile ready (specDispatch ready base) start .tau reached := .call leftFocus
    have canonical : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau peer := by
      simpa only [peer, ← sameDispatch] using (Step.call rightFocus : Step profile ready
        (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau _)
    obtain ⟨rfl, rfl⟩ := silentStepUnique checked first
    have focused := pairComponentFocus leftFocus rightFocus paired
    obtain ⟨otherFrames, otherRest, shape, aligned⟩ :=
      focused.push leftFocus body resume resume
    rw [rightFocus, List.cons.injEq, Activation.mk.injEq] at shape
    obtain ⟨⟨_, _, rfl⟩, rfl⟩ := shape
    have leftEdit : transitionEdit start .tau = .push (.prog resume) := by rw [transitionEdit, leftFocus]; rfl
    have rightEdit : transitionEdit incoming .tau = .push (.prog resume) := by rw [transitionEdit, rightFocus]; rfl
    exact .inr ⟨_, rfl, tail, aligned, sharedPushTransport checked canonical leftEdit rightEdit⟩

open ReturnFrame.Occurrence in
private theorem classifiedWaitCrossing : CallbackWaitableCrossing profile ready base bindings false := by
  intro changes start incoming next finish label labels thread core resume frames rest mem inst args focused calling step tail paired
  have boundary := callbackTerminalSlice (bindings := bindings) paired (.boundary (.waitInstall focused calling) step tail)
  obtain ⟨peerFrames, peerRest, leading, suffix, reached, peer, split, ⟨mark, paths⟩, live, residual, frontier⟩ :=
    cutPublicWaitDecision (bindings := bindings) mem inst args focused calling step tail paired
  obtain ⟨rfl, used⟩ := List.cons.inj split
  have terminal (stop : suffix = [] ∨ (reached.ctl = [] ∧ peer.ctl = [])) :
      CallbackCrossingAt profile ready base bindings changes start incoming .tau labels finish := by
    refine .inr (callbackTerminalSlice paired ?_)
    rw [used]
    exact .waitTerminal paths frontier stop residual
  cases frontier with
  | trapped checked canonical _ => exact terminal (.inr ⟨checked, canonical⟩)
  | pending op resume checked canonical site stop => exact terminal (.inl (stop.resolve_right (fun impossible => impossible.1 trivial)))
  | returned result checked canonical site =>
    have original := live (by rw [checked]; exact List.cons_ne_nil _ _)
    have decision := sharedTopTransport original (frame := .core core resume)
      (by rw [segmentStorage, checked]; rfl) (by rw [segmentStorage, canonical]; rfl)
    rcases result with ⟨entry, choice⟩
    cases choice with
    | none =>
      obtain ⟨body, remaining, delivered, peerDelivery, consumed, path, actual, outcome, exit, _⟩ :=
        cutWaitableWaitDelivery (bindings := bindings) mem entry checked canonical site residual
      have whole := (CallbackPrefix.transportAppend decision path).choose_spec.1
      have compared : OccurrenceTransport profile ready base bindings start incoming (.tau :: (leading ++ body))
          (.tau :: (leading ++ body)) delivered peerDelivery := by
        simpa only [List.nil_append, List.map_nil, List.cons_append] using whole
      have useAll : labels = (leading ++ body) ++ remaining :=
        used.trans ((congrArg (leading ++ ·) consumed).trans (List.append_assoc ..).symm)
      refine crossFlatCalloutExit useAll exit (fun _ _ => compared)
        (fun stop => callbackTerminalSlice paired ?_) boundary
      rw [useAll]
      exact .waitTerminal compared outcome stop actual
    | some waiter =>
      have aligned := pairComponentFocus checked canonical site
      rcases classifyReachedGrowth (CallbackPrefix.transportPaths decision none).choose_spec.1.steps with growing | _
      · exact .inl ⟨leading, .tau :: leading, suffix, reached, peer, used, ⟨growing, rfl, aligned, decision⟩, residual⟩
      · exact .inr boundary

open ReturnFrame.Occurrence in
private theorem classifyCancelHookWith (async : Bool) (subtask : SubtaskId) (hook : CancelRef)
    {thread frames rest peerFrames peerRest} {budget : Nat}
    (leftFocus : start.ctl = ⟨thread, .prog (cancelAfterRequestWrite async subtask hook), frames⟩ :: rest)
    (rightFocus : incoming.ctl = ⟨thread, .prog (cancelAfterRequestWrite async subtask hook), peerFrames⟩ :: peerRest)
    (paired : PairedComponentSite older start incoming ⟨thread, frames, rest⟩ ⟨thread, peerFrames, peerRest⟩)
    (run : Steps profile ready (specDispatch ready base) start labels finish)
    (bounded : labels.length ≤ budget) (compare : ShorterCallbackSlices profile ready base bindings budget) :
    CancelHookCallbackSlice profile ready base bindings older (cancelHookReturn async subtask) start incoming labels finish := by
  rcases cutCancelHookInstall (bindings := bindings) async subtask hook leftFocus rightFocus paired run with empty | installed
  · exact .inl empty
  obtain ⟨suffix, split, residual, related, install⟩ := installed
  have shorter : suffix.length < budget := by rw [split, List.length_cons] at bounded; omega
  obtain ⟨checked, canonical, trailing, reached, peer, used, compared, ending⟩ := compare shorter residual related
  obtain ⟨move, whole, tracks⟩ := CallbackPrefix.transportAppend install compared.occurrences
  let mark := move (some (.active 0 0))
  have aligned := pairComponentFocus (check := ⟨thread, frames, rest⟩) (canon := ⟨thread, peerFrames, peerRest⟩)
    leftFocus rightFocus paired
  have outside : OutsideMarks older (segmentStorage start) (segmentStorage incoming) [] :=
    fun place _ => paired_outside (left := HostFrame.replace start incoming.host) aligned place (by simp)
  have kept : Outside older (segmentStorage reached) (segmentStorage peer) mark := by
    apply outsideMarks_singleton.mp
    obtain ⟨_, _, retained⟩ := whole
    exact retained older [] outside
  obtain ⟨checkMark, canonMark⟩ := tracks (some (.active 0 0))
  have tracked : AllocatorMark profile ready base bindings older _ _ checked canonical reached peer mark :=
    ⟨kept, checkMark, canonMark, CallbackPrefix.transportPaths compared.occurrences⟩
  refine .inr ⟨_, _, checked, canonical, trailing, reached, peer, mark, by rw [split, used], install, whole,
    compared.observed.symm, tracked, ending, ?_⟩
  intro value cursor returning
  exact alignAllocatorPop tracked compared.paired returning rfl (callbackEndSteps ending)

open ReturnFrame.Occurrence in
private theorem oneStepLocation {left right : Config (core3 grow) (HostState sig)} {place first second : Option Location}
    {label : Label (core3 grow) (HostState sig)}
    (leftTrail : Trail profile ready (specDispatch ready base) left place [label] right first)
    (rightTrail : Trail profile ready (specDispatch ready base) left place [label] right second) : first = second := by
  cases leftTrail with
  | step _ leftTail =>
    cases leftTail
    cases rightTrail with
    | step _ rightTail => cases rightTail; rfl

open ReturnFrame.Occurrence in
private theorem crossReadyCancelCore {decision peerDecision : Config (core3 grow) (HostState sig)}
    {checked canonical trailing : Trace grow sig} {thread core resume frames rest peerFrames peerRest}
    (subtask : SubtaskId) (choice : Option ThreadId)
    (split : labels = checked ++ trailing)
    (observed : PayloadPrefix.visible canonical = PayloadPrefix.visible checked)
    (caller : OccurrenceTransport profile ready base bindings start incoming (.tau :: checked) (.tau :: canonical)
      decision peerDecision [some (.active 0 0)])
    (leftFocus : decision.ctl = ⟨thread, .prog (cancelAfterHookDecision subtask choice), .core core resume :: frames⟩ :: rest)
    (rightFocus : peerDecision.ctl = ⟨thread, .prog (cancelAfterHookDecision subtask choice), .core core resume :: peerFrames⟩ :: peerRest)
    (site : PairedComponentSite older decision peerDecision ⟨thread, .core core resume :: frames, rest⟩
      ⟨thread, .core core resume :: peerFrames, peerRest⟩)
    (actual : Steps profile ready (specDispatch ready base) decision trailing finish)
    (paired : HostFrame.Related.Paired older start incoming)
    (compare : ShorterCallbackSlices profile ready base bindings (.tau :: labels).length)
    (fallback : CallbackCrossingAt profile ready base bindings older start incoming .tau labels finish)
    (boundary : CallbackSlice profile ready base bindings older start incoming (.tau :: labels) finish) :
    CallbackCrossingAt profile ready base bindings older start incoming .tau labels finish := by
  cases choice with
  | none =>
    obtain ⟨body, remaining, reached, peer, used, paths, residual, exit, stationary⟩ :=
      cutCancelFinish (bindings := bindings) subtask leftFocus rightFocus site actual
    have consumed : labels = (checked ++ body) ++ remaining := by rw [split, used, List.append_assoc]
    have seen : PayloadPrefix.visible (canonical ++ body) = PayloadPrefix.visible (checked ++ body) := by
      simp only [visibleAppend, observed]
    refine crossAsymmetricFlatCalloutExit consumed seen exit ?_ ?_ boundary
    · intro _ finalCore finalResume _ _ _ _ _ left right
      have live := retainComparedOccurrences caller (stationary (by rw [left]; exact List.cons_ne_nil _ _))
      exact sharedTopTransport live (frame := .core finalCore finalResume)
        (by rw [segmentStorage, left]; rfl) (by rw [segmentStorage, right]; rfl)
    · intro terminal
      have throughFinish := (CallbackPrefix.transportAppend caller paths).choose_spec.1
      refine callbackTerminalSlice paired ?_
      rw [consumed]
      exact .cancelTerminal throughFinish (by simpa only [List.cons_append, visibleTauCons] using seen) exit terminal residual
  | some waiter =>
    cases thread with
    | none => exact fallback
    | some active =>
      rcases cutCoreCalloutPark (bindings := bindings) (cancelFinish subtask) leftFocus rightFocus site actual with _ | parked
      · exact fallback
      obtain ⟨remaining, used, residual, aligned, path, saved, _⟩ := parked
      have shorter : remaining.length < (.tau :: labels).length := by
        rw [split, used, List.length_cons, List.length_append, List.length_cons]
        omega
      obtain ⟨parkMove, throughPark, parkTrails⟩ := CallbackPrefix.transportAppend caller path
      have atSaved := oneStepLocation (parkTrails (some (.active 0 0))).1 saved
      let parked := { (decision.setCont active (some ⟨some active, .prog (cancelFinish subtask), .core core resume :: frames⟩)) with
        store := StepDefs.threadStatusSt active .blocked decision.store, ctl := rest }
      let peerParked := { (peerDecision.setCont active (some ⟨some active, .prog (cancelFinish subtask), .core core resume :: peerFrames⟩)) with
        store := StepDefs.threadStatusSt active .blocked peerDecision.store, ctl := peerRest }
      have markedPark : OccurrenceTransport profile ready base bindings start incoming
          (.tau :: (checked ++ [.tau])) (.tau :: (canonical ++ [.tau])) parked peerParked [some (.saved active.idx 0)] :=
        by simpa only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, atSaved] using throughPark
      obtain ⟨ran, ranCanon, restLabels, reached, peer, continued, compared, ending⟩ := compare shorter residual aligned
      obtain ⟨_, whole, _⟩ := CallbackPrefix.transportAppend markedPark compared.occurrences
      have full : labels = ((checked ++ [.tau]) ++ ran) ++ restLabels := by
        rw [split, used, continued]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      refine .inr (callbackTerminalSlice paired ?_)
      rw [full]
      exact .cancelParked whole (by simp only [List.cons_append, visibleTauCons, visibleAppend, observed, compared.observed]) ending

private theorem pairedCoreTop {frames peerFrames : List (Seg (core3 grow) (HostState sig))} {core resume below}
    (related : List.Forall₂ (ReturnFrame.Related.Segment older) frames peerFrames)
    (top : frames = .core core resume :: below) :
    ∃ peerBelow, peerFrames = .core core resume :: peerBelow := by
  rw [top] at related
  cases related with
  | cons first _ => cases first; exact ⟨_, rfl⟩

private theorem cursorShape (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) {thread frames}
    (threadAt : cursor.thread = thread) (framesAt : cursor.frames = frames) : cursor = ⟨thread, frames, cursor.rest⟩ := by
  cases cursor
  cases threadAt
  cases framesAt
  rfl

open ReturnFrame.Occurrence in
private theorem crossCancelAfterHook {resumed peerResume : Config (core3 grow) (HostState sig)}
    {checked canonical remaining : Trace grow sig} {mark : Option Location}
    (async : Bool) (subtask : SubtaskId) (value : Ret (core3 grow))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (split : labels = checked ++ remaining)
    (observed : PayloadPrefix.visible canonical = PayloadPrefix.visible checked)
    (path : OccurrenceTransport profile ready base bindings start incoming (.tau :: checked) (.tau :: canonical) resumed peerResume)
    (caller : OccurrenceTransport profile ready base bindings start incoming (.tau :: checked) (.tau :: canonical) resumed peerResume [mark])
    (leftFocus : resumed.ctl = check.control (cancelHookReturn async subtask value))
    (rightFocus : peerResume.ctl = canon.control (cancelHookReturn async subtask value))
    (site : PairedComponentSite older resumed peerResume check canon)
    (threadAligned : check.thread = canon.thread)
    (framesAligned : List.Forall₂ (ReturnFrame.Related.Segment older) check.frames canon.frames)
    (actual : Steps profile ready (specDispatch ready base) resumed remaining finish)
    (paired : HostFrame.Related.Paired older start incoming)
    (compare : ShorterCallbackSlices profile ready base bindings (.tau :: labels).length)
    (boundary : CallbackSlice profile ready base bindings older start incoming (.tau :: labels) finish) :
    CallbackCrossingAt profile ready base bindings older start incoming .tau labels finish := by
  obtain ⟨decision, residual, reached, peer, used, pathDecision, run, frontier⟩ :=
    cutCancelHookDecision (bindings := bindings) async subtask value leftFocus rightFocus site actual
  have consumed : labels = (checked ++ decision) ++ residual := by rw [split, used, List.append_assoc]
  have seen : PayloadPrefix.visible (.tau :: (canonical ++ decision)) = PayloadPrefix.visible (.tau :: (checked ++ decision)) := by
    simp only [visibleTauCons, visibleAppend, observed]
  have terminal (stop : residual = [] ∨ (reached.ctl = [] ∧ peer.ctl = [])) :
      CallbackCrossingAt profile ready base bindings older start incoming .tau labels finish := by
    obtain ⟨_, throughDecision, _⟩ := CallbackPrefix.transportAppend caller pathDecision
    refine .inr (callbackTerminalSlice paired ?_)
    rw [consumed]
    exact .cancelDecisionTerminal throughDecision seen frontier stop run
  cases frontier with
  | trapped left right _ => exact terminal (.inr ⟨left, right⟩)
  | pending _ _ _ _ _ stop => exact terminal (.inl (stop.resolve_right (fun impossible => impossible.1 trivial)))
  | returned choice left right finalSite =>
    have throughDecision := (CallbackPrefix.transportAppend path pathDecision).choose_spec.1
    have fallback : CallbackCrossingAt profile ready base bindings older start incoming .tau labels finish := by
      rcases classifyReachedGrowth (CallbackPrefix.transportPaths throughDecision none).choose_spec.1.steps with growing | _
      · exact .inl ⟨checked ++ decision, .tau :: (canonical ++ decision), residual, reached, peer, consumed,
          ⟨growing, seen, pairComponentFocus left right finalSite, throughDecision⟩, run⟩
      · exact .inr boundary
    obtain ⟨move, marked, _⟩ := CallbackPrefix.transportAppend caller pathDecision
    classical
    by_cases active : move mark = some (.active 0 0)
    · by_cases coreTop : ∃ core resume frames, check.frames = .core core resume :: frames
      · obtain ⟨core, resume, frames, leftTop⟩ := coreTop
        obtain ⟨peerFrames, rightTop⟩ := pairedCoreTop framesAligned leftTop
        have checkAt := cursorShape check rfl leftTop
        have canonAt := cursorShape canon threadAligned.symm rightTop
        exact crossReadyCancelCore (thread := check.thread) (core := core) (resume := resume)
          (frames := frames) (rest := check.rest) (peerFrames := peerFrames) (peerRest := canon.rest)
          subtask choice consumed (by simpa only [visibleTauCons] using seen)
          (by simpa only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, active] using marked)
          (left.trans (congrArg (fun cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) =>
            cursor.control (cancelAfterHookDecision subtask choice)) checkAt))
          (right.trans (congrArg (fun cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig) =>
            cursor.control (cancelAfterHookDecision subtask choice)) canonAt))
          ((congrArg₂ (PairedComponentSite older reached peer) checkAt canonAt).mp finalSite) run paired compare fallback boundary
      · exact fallback
    · exact fallback

open ReturnFrame.Occurrence in
private theorem classifiedCancelCrossing : CallbackCancelCrossing profile ready base bindings := by
  intro changes start incoming next finish label labels thread core resume frames rest async inst args focused calling step tail paired compare
  have boundary := callbackTerminalSlice (bindings := bindings) paired (.boundary (.cancelInstall focused calling) step tail)
  obtain ⟨peerFrames, peerRest, leading, suffix, reached, peer, split, ⟨mark, paths⟩, live, residual, frontier⟩ :=
    cutPublicCancelEntry (bindings := bindings) async inst args focused calling step tail paired
  obtain ⟨rfl, used⟩ := List.cons.inj split
  have terminal (stop : suffix = [] ∨ (reached.ctl = [] ∧ peer.ctl = [])) :
      CallbackCrossingAt profile ready base bindings changes start incoming .tau labels finish := by
    refine .inr (callbackTerminalSlice paired ?_)
    rw [used]
    exact .waitTerminal paths frontier stop residual
  cases frontier with
  | trapped checked canonical _ => exact terminal (.inr ⟨checked, canonical⟩)
  | pending _ _ _ _ _ stop => exact terminal (.inl (stop.resolve_right (fun impossible => impossible.1 trivial)))
  | returned result checked canonical site =>
    rcases result with ⟨subtask, hook⟩
    cases hook with
    | none =>
      have entry := sharedTopTransport (live (by rw [checked]; exact List.cons_ne_nil _ _)) (frame := .core core resume)
        (by rw [segmentStorage, checked]; rfl) (by rw [segmentStorage, canonical]; rfl)
      obtain ⟨body, remaining, delivered, peerDelivery, consumed, path, actual, outcome, exit, _⟩ :=
        cutCancelDelivery (bindings := bindings) async subtask checked canonical site residual
      have whole : OccurrenceTransport profile ready base bindings start incoming (.tau :: (leading ++ body))
          (.tau :: (leading ++ body)) delivered peerDelivery :=
        by simpa only [List.nil_append, List.map_nil, List.cons_append] using (CallbackPrefix.transportAppend entry path).choose_spec.1
      have useAll : labels = (leading ++ body) ++ remaining :=
        used.trans ((congrArg (leading ++ ·) consumed).trans (List.append_assoc ..).symm)
      refine crossFlatCalloutExit useAll exit (fun _ _ => whole) (fun stop => callbackTerminalSlice paired ?_) boundary
      rw [useAll]
      exact .waitTerminal whole outcome stop actual
    | some hook =>
      have entry := live (by rw [checked]; exact List.cons_ne_nil _ _)
      obtain ⟨write, remainder, written, peerWritten, consumed, writePaths, actual, outcome⟩ :=
        cutCancelRequestWrite (bindings := bindings) async subtask hook checked canonical site residual
      obtain ⟨_, prefixPath, _⟩ := CallbackPrefix.transportAppend entry writePaths
      have useAll : labels = (leading ++ write) ++ remainder :=
        used.trans ((congrArg (leading ++ ·) consumed).trans (List.append_assoc ..).symm)
      have terminalWrite (stop : remainder = [] ∨ (written.ctl = [] ∧ peerWritten.ctl = [])) :
          CallbackCrossingAt profile ready base bindings changes start incoming .tau labels finish := by
        refine .inr (callbackTerminalSlice paired ?_)
        rw [useAll]
        exact .waitTerminal prefixPath outcome stop actual
      cases outcome with
      | trapped left right _ => exact terminalWrite (.inr ⟨left, right⟩)
      | pending _ _ _ _ _ stop => exact terminalWrite (.inl (stop.resolve_right (fun impossible => impossible.1 trivial)))
      | returned _ left right afterWrite =>
        have bounded : remainder.length ≤ (Label.tau :: labels).length := by
          rw [useAll, List.length_cons, List.length_append]
          omega
        rcases classifyCancelHookWith (bindings := bindings) async subtask hook left right afterWrite actual bounded compare with empty | body
        · exact terminalWrite (.inl empty.1)
        obtain ⟨entryHook, peerHook, ran, ranCanon, trailing, atHook, peerAtHook, hookMark, hookUsed, _, hookPaths,
          observed, tracked, ending, pop⟩ := body
        obtain ⟨_, whole, _⟩ := CallbackPrefix.transportAppend prefixPath hookPaths
        have full : labels = ((leading ++ write) ++ .tau :: ran) ++ trailing := by
          rw [useAll, hookUsed]
          simp only [List.append_assoc, List.cons_append]
        have stopped : CallbackSlice profile ready base bindings changes start incoming (.tau :: labels) finish := by
          refine callbackTerminalSlice paired ?_
          rw [full]
          refine .cancelHookBody whole ?_ tracked ending
          simp only [List.cons_append, visibleTauCons, visibleAppend, observed]
        classical
        by_cases returns : ∃ (value : Ret (core3 grow)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
            atHook.ctl = { cursor with frames := .prog (cancelHookReturn async subtask) :: cursor.frames }.control (.pure value)
        · obtain ⟨value, cursor, returning⟩ := returns
          rcases pop value cursor returning with _ | _ | ⟨remaining, canon, top, popped, _, rest, _, frame, _, transport⟩
          · exact .inr stopped
          · exact .inr stopped
          subst hookMark
          have initial := sharedTopTransport entry (frame := .core core resume)
            (by rw [segmentStorage, checked]; rfl) (by rw [segmentStorage, canonical]; rfl)
          have prior := (CallbackPrefix.transportAppend initial writePaths).choose_spec.1
          have hookOnly := (CallbackPrefix.transportAppend prior hookPaths).choose_spec.1
          have returned := transport hookOnly
          have originalCaller := transport whole
          let consumed := ((leading ++ write) ++ .tau :: ran) ++ [.tau]
          let canonLabels := ((leading ++ write) ++ .tau :: ranCanon) ++ [.tau]
          have usedAll : labels = consumed ++ remaining := by
            rw [full, popped]
            simp only [consumed, List.append_assoc, List.cons_append, List.nil_append]
          have seen : PayloadPrefix.visible canonLabels = PayloadPrefix.visible consumed := by
            simp only [consumed, canonLabels, visibleTauCons, visibleAppend, observed]
          exact crossCancelAfterHook async subtask value cursor canon usedAll seen returned originalCaller rfl rfl
            (pairAfterComponentPop (left := atHook) (right := peerAtHook) (program := .pure (.cancel .none)) frame)
            frame.thread frame.frames rest paired compare stopped
        · exact .inr stopped

private theorem foldMixedCallbacks {callees : List (ComponentCall.Callee sig)}
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    CallbackSlice profile ready (ComponentCall.hostWithComponent bindings callees) bindings older start incoming labels finish :=
  foldCallbackSlicesWith (classifiedGiveCrossing (base := ComponentCall.hostWithComponent bindings callees) rfl)
    (some ⟨classifiedComponentCrossing⟩) (some ⟨classifiedPollCrossing⟩) (some ⟨classifiedWaitCrossing⟩)
    (some ⟨classifiedWaitResumeCrossing⟩) (some ⟨classifiedCancelResumeCrossing⟩)
    (some ⟨classifiedCancelCrossing⟩) run paired

open ReturnFrame.Occurrence in
theorem classifyCancelHookCallbacks {callees : List (ComponentCall.Callee sig)}
    (async : Bool) (subtask : SubtaskId) (hook : CancelRef)
    {thread frames rest peerFrames peerRest}
    (leftFocus : start.ctl = ⟨thread, .prog (cancelAfterRequestWrite async subtask hook), frames⟩ :: rest)
    (rightFocus : incoming.ctl = ⟨thread, .prog (cancelAfterRequestWrite async subtask hook), peerFrames⟩ :: peerRest)
    (paired : PairedComponentSite older start incoming ⟨thread, frames, rest⟩ ⟨thread, peerFrames, peerRest⟩)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish) :
    CancelHookCallbackSlice profile ready (ComponentCall.hostWithComponent bindings callees) bindings older
      (cancelHookReturn async subtask) start incoming labels finish :=
  classifyCancelHookWith async subtask hook leftFocus rightFocus paired run (Nat.le_refl _) (fun _ => foldMixedCallbacks)

open ReturnFrame.Occurrence in
private theorem classifyParkedCoreCallbacks {callees : List (ComponentCall.Callee sig)}
    (savedProgram : Session grow sig (Ret (core3 grow)))
    {thread core resume frames rest peerFrames peerRest}
    (leftFocus : start.ctl = ⟨some thread, .prog (.op (.block none) (fun _ => savedProgram)), .core core resume :: frames⟩ :: rest)
    (rightFocus : incoming.ctl = ⟨some thread, .prog (.op (.block none) (fun _ => savedProgram)),
      .core core resume :: peerFrames⟩ :: peerRest)
    (paired : PairedComponentSite older start incoming ⟨some thread, .core core resume :: frames, rest⟩
      ⟨some thread, .core core resume :: peerFrames, peerRest⟩)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish) :
    ParkedCoreCalloutSlice profile ready (ComponentCall.hostWithComponent bindings callees) bindings older start incoming labels finish := by
  rcases cutCoreCalloutPark (bindings := bindings) savedProgram leftFocus rightFocus paired run with stopped | parked
  · exact .inl stopped
  obtain ⟨_, split, residual, aligned, paths, leftMark, rightMark⟩ := parked
  obtain ⟨checked, canonical, trailing, reached, peer, used, compared, ending⟩ := foldMixedCallbacks residual aligned
  obtain ⟨move, whole, tracks⟩ := CallbackPrefix.transportAppend paths compared.occurrences
  obtain ⟨left, right⟩ := tracks (some (.saved thread.idx 0))
  exact .inr ⟨checked, canonical, trailing, reached, peer, move (some (.saved thread.idx 0)),
    by rw [split, used]; rfl, whole, leftMark.append left, rightMark.append right, ending⟩

theorem classifyParkedWaitCallbacks {callees : List (ComponentCall.Callee sig)}
    (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry)
    {thread core resume frames rest peerFrames peerRest}
    (leftFocus : start.ctl = ⟨some thread, .prog (waitableWaitAfterDecision mem entry (some thread)), .core core resume :: frames⟩ :: rest)
    (rightFocus : incoming.ctl = ⟨some thread, .prog (waitableWaitAfterDecision mem entry (some thread)),
      .core core resume :: peerFrames⟩ :: peerRest)
    (paired : PairedComponentSite older start incoming ⟨some thread, .core core resume :: frames, rest⟩
      ⟨some thread, .core core resume :: peerFrames, peerRest⟩)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish) :
    ParkedWaitCallbackSlice profile ready (ComponentCall.hostWithComponent bindings callees) bindings older start incoming labels finish :=
  classifyParkedCoreCallbacks (waitableWaitContinue mem entry) leftFocus rightFocus paired run

theorem classifyParkedCancelCallbacks {callees : List (ComponentCall.Callee sig)}
    (subtask : SubtaskId)
    {thread core resume frames rest peerFrames peerRest}
    (leftFocus : start.ctl = ⟨some thread, .prog (cancelAfterHookDecision subtask (some thread)), .core core resume :: frames⟩ :: rest)
    (rightFocus : incoming.ctl = ⟨some thread, .prog (cancelAfterHookDecision subtask (some thread)),
      .core core resume :: peerFrames⟩ :: peerRest)
    (paired : PairedComponentSite older start incoming ⟨some thread, .core core resume :: frames, rest⟩
      ⟨some thread, .core core resume :: peerFrames, peerRest⟩)
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish) :
    ParkedCoreCalloutSlice profile ready (ComponentCall.hostWithComponent bindings callees) bindings older start incoming labels finish :=
  classifyParkedCoreCallbacks (cancelFinish subtask) leftFocus rightFocus paired run

theorem classifyMixedCallbacks {callees : List (ComponentCall.Callee sig)}
    (run : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    MixedCallbackSlice profile ready bindings callees older start incoming labels finish := by
  obtain ⟨checked, canonical, trailing, reached, peer, split, front, ending⟩ := foldMixedCallbacks run paired
  refine ⟨checked, canonical, trailing, reached, peer, split, front, ending, ?_⟩
  cases callbackEndSteps ending with
  | refl => exact .inl ⟨rfl, rfl⟩
  | cons step tail => exact .inr ⟨_, _, _, rfl, step, tail, classifyComponentInstallOutcome step tail front.paired⟩

open ReturnFrame.Occurrence in
theorem compareComponentMarkedWorker {callees : List (ComponentCall.Callee sig)}
    {reached peer : Config (core3 grow) (HostState sig)} {leading suffix : Trace grow sig}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (moved : OccurrenceTransport profile ready (ComponentCall.hostWithComponent bindings callees) bindings
      start incoming leading leading reached peer)
    (reply : ComponentMarkedReplyTail profile ready (ComponentCall.hostWithComponent bindings callees) bindings older
      start incoming reached peer leading check first second suffix finish) :
    ComponentMarkedWorkerTail profile ready (ComponentCall.hostWithComponent bindings callees) bindings older
      start incoming reached peer leading check first second suffix finish := by
  classical
  by_cases focus : reached.ctl = check.control (.pure (.cancel .none))
  · obtain ⟨mark, tracked, result⟩ := reply
    rcases result focus with lost | ⟨after, _, pop⟩
    · exact .inr (.inl ⟨mark, tracked, lost⟩)
    rcases pop with lost | empty | ⟨remaining, rightAfter, _, actual, smaller, residual, _, frame, _, transport⟩
    · exact .inr (.inl ⟨mark, tracked, lost⟩)
    · exact .inr (.inr (.inl empty))
    have continued := transport (markTransport moved)
    refine .inr (.inr (.inr ⟨remaining, after, rightAfter, actual, smaller, residual, continued, ?_⟩))
    by_cases common : first (.cancel .none) = second (.cancel .none)
    · have pair : HostFrame.Related.Paired older
          { reached with ctl := after.control (first (.cancel .none)) }
          { peer with ctl := rightAfter.control (second (.cancel .none)) } := by
        rw [← common]
        exact pairAfterComponentPop frame
      obtain ⟨checked, canonical, trailing, worker, workerPeer, split, segment, ending⟩ :=
        foldMixedCallbacks residual pair
      exact .inr ⟨checked, canonical, trailing, worker, workerPeer, split,
        by simpa only [List.map_nil, List.append_nil] using
          (CallbackPrefix.transportAppend continued segment.occurrences).choose_spec.1, segment.observed, ending⟩
    · exact .inl common
  · exact .inl focus

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan
