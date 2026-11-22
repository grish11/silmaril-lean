module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.CanonicalTree.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadLeaf

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower (Field)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims (Spend)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}
variable {profile : ProfileKind} {ready : HostReady (HostState sig)}
variable {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}

theorem plan_spend_live {store : CStore (core3 grow)} {state : OwnedMemory.Claims.State sig}
    {index : Nat} {item : Field} {update : Spend}
    (planned : liveLeafPlan store state index item = .ok (some update)) : update.Live state := by
  cases item with
  | owner receipt =>
    cases prepared : prepareOwner state receipt with
    | error _ => simp [liveLeafPlan, prepared, Except.map, Except.mapError] at planned
    | ok result =>
      obtain ⟨rep, next⟩ := result
      simp [liveLeafPlan, prepared, Except.map, Except.mapError] at planned
      exact planned ▸ (owner_prepared prepared).2
  | endpoint channel element id =>
    cases prepared : prepareEndpoint store state channel element id with
    | error _ => simp [liveLeafPlan, prepared, Except.map, Except.mapError] at planned
    | ok next =>
      simp [liveLeafPlan, prepared, Except.map, Except.mapError] at planned
      exact planned ▸ (endpoint_prepared prepared).2
  | context id =>
    by_cases missing : (store.errCtx? id).isNone = true <;> simp [liveLeafPlan, missing] at planned
  | data | aggregate | fixed | dynamic | sum => cases planned

private def readPlan (initial : CStore (core3 grow)) (item : Field) (index : Nat) :
    Session grow sig (Except RecordLower.Issue (Option Spend)) :=
  match item with
  | .owner _ => do return liveLeafPlan initial (← hostGet).writer index item
  | .endpoint .. | .context _ => do
    let state ← hostGet
    return liveLeafPlan (← getStore) state.writer index item
  | _ => pure (.ok none)

private def applyPlan : Except RecordLower.Issue (Option Spend) → Session grow sig (Except RecordLower.Issue Unit)
  | .error reason => pure (.error reason)
  | .ok none => pure (.ok ())
  | .ok (some spend) => do
    claims.spend spend
    return .ok ()

private theorem transfer_eq (initial : CStore (core3 grow)) (item : Field) (index : Nat) :
    Effects.transfer (recordClaims (sig := sig)) item index = (readPlan initial item index >>= applyPlan) := by
  cases item with
  | owner receipt =>
    simp only [Effects.transfer, recordClaims, claims, readPlan, liveLeafPlan, Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext state
    simp only [Prog.pure_eq, Prog.pure_bind']
    cases prepareOwner state.writer receipt <;> rfl
  | endpoint channel element id =>
    simp only [Effects.transfer, recordClaims, claims, readPlan, liveLeafPlan, Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext state
    simp only [Prog.pure_eq, Prog.pure_bind']
    congr 1
    funext store
    cases prepareEndpoint store state.writer channel element id <;> rfl
  | context id =>
    simp only [Effects.transfer, recordClaims, claims, readPlan, liveLeafPlan, Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext state
    simp only [Prog.pure_eq, Prog.pure_bind']
    congr 1
    funext store
    by_cases missing : (store.errCtx? id).isNone <;> simp [missing, applyPlan]
  | _ => rfl

theorem guard_tracks {before after labels spend}
    (run : LeafGuardSteps profile ready dispatch before labels after spend) (place : Location) :
    Prefix profile ready dispatch before place labels after place := by
  induction run with
  | done state => exact .done state place
  | read step edit _ _ _ ih => exact .step step (by rw [edit]; rfl) ih
  | commit step edit _ _ => exact .step step (by rw [edit]; rfl) (.done _ _)

private theorem guard_append {before middle after checked trailing frontSpend spend}
    (front : LeafGuardSteps profile ready dispatch before checked middle frontSpend) (unspent : frontSpend = none)
    (back : LeafGuardSteps profile ready dispatch middle trailing after spend) :
    LeafGuardSteps profile ready dispatch before (checked ++ trailing) after spend := by
  induction front with
  | done => exact back
  | read step edit store host _ ih => exact .read step edit store host (ih unspent back)
  | commit => cases unspent

private theorem reads (reached : Machine.Config (core3 grow) (HostState sig)) (item : Field) (index : Nat)
    (finish : Except RecordLower.Issue (Option Spend) → Session grow sig (Ret (core3 grow))) {thread segments rest}
    (focused : reached.ctl = ⟨thread, .prog (readPlan reached.store item index >>= finish), segments⟩ :: rest) :
    ∃ labels, (∀ label ∈ labels, label = .tau) ∧ LeafGuardSteps profile ready dispatch reached labels
      { reached with ctl := ⟨thread, .prog (finish (liveLeafPlan reached.store reached.host.writer index item)),
        segments⟩ :: rest } none := by
  cases item with
  | owner => exact ⟨[.tau], by simp, .read (.hostGet focused)
      (by rw [transitionEdit, focused]; rfl) rfl rfl (.done _)⟩
  | endpoint | context => exact ⟨[.tau, .tau], by simp, .read (.hostGet focused)
      (by rw [transitionEdit, focused]; rfl) rfl rfl (.read (.get rfl) rfl rfl rfl (.done _))⟩
  | _ =>
    refine ⟨[], by simp, ?_⟩
    change reached.ctl = ⟨thread, .prog (finish (.ok none)), segments⟩ :: rest at focused
    change LeafGuardSteps profile ready dispatch reached []
      { reached with ctl := ⟨thread, .prog (finish (.ok none)), segments⟩ :: rest } none
    rw [← focused]
    cases reached
    exact .done _

private theorem spends (reached : Machine.Config (core3 grow) (HostState sig)) (spend : Spend)
    (finish : Session grow sig (Ret (core3 grow))) {thread segments rest}
    (focused : reached.ctl = ⟨thread, .prog (claims.spend spend >>= fun _ => finish), segments⟩ :: rest) :
    LeafGuardSteps profile ready dispatch reached [.tau, .tau]
      { reached with host := { reached.host with writer := spend.apply reached.host.writer }
                     ctl := ⟨thread, .prog finish, segments⟩ :: rest } (some spend) :=
  .read (.hostGet focused) (by rw [transitionEdit, focused]; rfl) rfl rfl
    (.commit (.hostSet (k := fun _ => finish) rfl) rfl rfl rfl)

theorem leaf_prefix (reached : Machine.Config (core3 grow) (HostState sig)) (destination : RecordDestination)
    (inst : InstId) (item : Field) (index : Nat) (output : Lower.Output)
    (finish : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow))) {thread segments rest}
    (focused : reached.ctl = ⟨thread, .prog (Effects.checkedLeaf recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index output >>= finish), segments⟩ :: rest) :
    let canonical := RecordLower.CanonicalTree.leaf Limits.spec Quirks.none (destination.context inst)
      destination.width item output >>= fun result => finish (.ok result)
    let (postHost, next) := match liveLeafPlan reached.store reached.host.writer index item with
      | .error issue => (reached.host, finish (.error issue))
      | .ok none => (reached.host, canonical)
      | .ok (some spend) => ({ reached.host with writer := spend.apply reached.host.writer }, canonical)
    let committed := (liveLeafPlan reached.store reached.host.writer index item).toOption.join
    ∃ labels, (∀ label ∈ labels, label = .tau) ∧ LeafGuardSteps profile ready dispatch reached labels
      { reached with host := postHost, ctl := ⟨thread, .prog next, segments⟩ :: rest } committed := by
  let canonical := RecordLower.CanonicalTree.leaf Limits.spec Quirks.none (destination.context inst)
    destination.width item output >>= fun result => finish (.ok result)
  have leafEq : Effects.canonical Limits.spec Quirks.none (destination.context inst)
      destination.width item output = (RecordLower.CanonicalTree.leaf Limits.spec Quirks.none (destination.context inst)
        destination.width item output : Session grow sig output.Result) := by cases output <;> rfl
  let afterTransfer : Except RecordLower.Issue Unit → Session grow sig (Except RecordLower.Issue output.Result) :=
    fun outcome => match outcome with
    | .error issue => pure (.error issue)
    | .ok () => do
      let result ← RecordLower.CanonicalTree.leaf Limits.spec Quirks.none (destination.context inst)
        destination.width item output
      return .ok result
  have onSuccess : afterTransfer (.ok ()) >>= finish = canonical := by
    simp only [afterTransfer, canonical, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']
  let next := fun plan => applyPlan plan >>= fun verdict => afterTransfer verdict >>= finish
  have atRead : reached.ctl = ⟨thread, .prog (readPlan reached.store item index >>= next), segments⟩ :: rest := by
    simp only [Effects.checkedLeaf, transfer_eq reached.store, bind_assoc, leafEq, next, afterTransfer] at focused ⊢
    exact focused
  obtain ⟨labels, silent, readSteps⟩ := reads (profile := profile) (ready := ready) (dispatch := dispatch)
    reached item index next atRead
  dsimp only
  cases plan : liveLeafPlan reached.store reached.host.writer index item with
  | error issue => exact ⟨labels, silent, by simpa only [plan, next, applyPlan, afterTransfer, pure_bind, Except.toOption, Option.join, Option.bind] using readSteps⟩
  | ok result =>
    cases result with
    | none => exact ⟨labels, silent, by simpa only [plan, next, applyPlan, pure_bind, onSuccess, Except.toOption, Option.join, Option.bind, id] using readSteps⟩
    | some spend =>
      let afterRead := { reached with ctl := ⟨thread, .prog (next (.ok (some spend))), segments⟩ :: rest }
      have readDone : LeafGuardSteps profile ready dispatch reached labels afterRead none := by
        simpa only [plan, afterRead] using readSteps
      have spendSteps := spends (profile := profile) (ready := ready) (dispatch := dispatch) afterRead spend canonical
        (thread := thread) (segments := segments) (rest := rest) (by
          simp only [afterRead, next, applyPlan, bind_assoc, pure_bind, onSuccess])
      refine ⟨labels ++ [.tau, .tau], ?_, guard_append readDone rfl spendSteps⟩
      intro label member
      rcases List.mem_append.mp member with front | back
      · exact silent label front
      · simpa using back

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadLeaf
