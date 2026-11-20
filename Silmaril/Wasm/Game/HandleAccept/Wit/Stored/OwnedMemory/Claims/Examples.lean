module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Examples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Element Endpoint)

private def resource : RtId := ⟨0⟩

private def element : Element := some (.prim .u16)

private inductive Tag where
  | owners | inactiveBorrow | mixed | lateTrap

private def sig : Signature :=
  ⟨Tag, fun
    | .owners => .tuple [.own resource, .own resource]
    | .inactiveBorrow =>
      .result (some (.own resource)) (some (.future (some (.option (.borrow resource)))))
    | .mixed => .record [("owner", .own resource), ("end", .stream element)]
    | .lateTrap => .tuple [.own resource, .stream element, .own resource], fun _ => .fixed 0⟩

private abbrev World := State sig

private def limits : Component.Limits := Component.Limits.spec

private noncomputable def context : LiftLowerContext Mock.mock :=
  { opts := { memory := some 0 }, inst := ⟨0⟩ }

private noncomputable def acquire : P Mock.mock World Unit := do
  let _ ← Builtins.resourceNew limits resource 77
  let _ ← Builtins.resourceNew limits resource 77
  let .error (.lift (.schema .storedBorrow)) ← acceptNode sig limits Quirks.none context .inactiveBorrow
    (.flat [i32Flat 0, i32Flat 1]) [] | internal "inactive stored borrow was accepted"
  let .ok _ ← acceptNode sig limits Quirks.none context .owners (.flat [i32Flat 1, i32Flat 2]) []
    | internal "the two owned leaves were not accepted"

private noncomputable def destructor (id : HandleObjId) (inst : InstId)
    (request : DtorRequest Mock.mock) : P Mock.mock World Unit := do
  let .error .unclaimed ← give limits context resource id
    | internal "reentrant transfer did not reject the spent owner"
  if inst != ⟨0⟩ || request.rt != resource || request.rep != 77 then
    internal "incorrect destructor request"
  else pure ()

private noncomputable def roundTrip : P Mock.mock World (Ret Mock.mock) := do
  acquire
  let .error .wrongResourceType ← give limits context ⟨1⟩ ⟨0⟩
    | internal "nominal type mismatch did not reject"
  let .ok 2 ← give limits context resource ⟨0⟩
    | internal "the guest handle was not reissued"
  let .error .unclaimed ← give limits context resource ⟨0⟩
    | internal "spent claim could be given again"
  let .ok () ← drop (destructor ⟨1⟩) resource ⟨1⟩
    | internal "the other owner was not dropped"
  let .error .unclaimed ← drop (destructor ⟨1⟩) resource ⟨1⟩
    | internal "spent claim could be dropped again"
  pure .unit

private noncomputable def trapDuringDrop : P Mock.mock World (Ret Mock.mock) := do
  acquire
  let _ ← drop (fun inst request => do
    destructor ⟨1⟩ inst request
    trap (.unknownHandle 42)) resource ⟨1⟩
  pure .unit

private noncomputable def trapDuringGive : P Mock.mock World (Ret Mock.mock) := do
  acquire
  let .ok 2 ← give limits context resource ⟨0⟩
    | internal "first owner transfer failed"
  storeInt context 7 0 1
  let _ ← give limits { context with inst := ⟨1⟩ } resource ⟨1⟩
  pure .unit

private noncomputable def reacquire : P Mock.mock World (Ret Mock.mock) := do
  let _ ← roundTrip
  let _ ← Builtins.resourceNew limits resource 77
  let .ok _ ← acceptNode sig limits Quirks.none context .owners (.flat [i32Flat 2, i32Flat 1]) []
    | internal "fresh owner identities in reused guest slots were not accepted"
  let .error .unclaimed ← drop (destructor ⟨0⟩) resource ⟨0⟩
    | internal "reacquisition revived the old claim"
  let .ok () ← drop (destructor ⟨2⟩) resource ⟨2⟩
    | internal "the reacquired owner was not dropped"
  pure .unit

private noncomputable def trapDuringSecondMove : P Mock.mock World (Ret Mock.mock) := do
  acquire
  let _ ← Builtins.resourceNew limits resource 77
  let _ ← acceptNode sig limits Quirks.none context .owners (.flat [i32Flat 2, i32Flat 2]) []
  pure .unit

private noncomputable def createMixed : P Mock.mock World (Endpoint .readableStream element) := do
  let _ ← Builtins.resourceNew limits resource 77
  let _ ← Builtins.streamNew limits element
  Endpoint.inspect .readableStream element ⟨0⟩ 2

private noncomputable def mixedRoundTrip : P Mock.mock World (Ret Mock.mock) := do
  let endpoint ← createMixed
  let .ok tree ← acceptNode sig limits Quirks.none context .mixed (.memory 0) []
    | internal "mixed memory load did not publish a tree"
  trapIf ((rootReceipts tree).map receiptId != [⟨0⟩] || rootEndpoints tree != [endpoint.id])
    (.internal "mixed load changed the claim identities")
  let .error .alias := (← hostGet).register tree
    | internal "the same receipts and endpoint were registered twice"
  let .error .wrongResourceType ← give limits context ⟨1⟩ ⟨0⟩
    | internal "nominal owner mismatch did not reject"
  let .ok 2 ← give limits context resource ⟨0⟩
    | internal "owner could not be given while the endpoint was claimed"
  let .error .unclaimed ← give limits context resource ⟨0⟩
    | internal "owner could be given twice"
  let .error (.endpointTransfer .wrongType) ← giveEndpoint limits context .future element ⟨endpoint.id⟩
    | internal "endpoint kind mismatch did not reject"
  let .error (.endpointTransfer .wrongType) ← giveEndpoint limits context .stream (some (.prim .u8))
      ⟨endpoint.id⟩
    | internal "endpoint element mismatch did not reject"
  let .ok slot ← giveEndpoint limits context .stream element endpoint
    | internal "endpoint could not be given after wrong-type rejection"
  let restored ← Endpoint.inspect .readableStream element ⟨0⟩ slot
  trapIf (restored.id != endpoint.id) (.internal "endpoint identity changed")
  let .error .unclaimedEndpoint ← giveEndpoint limits context .stream element endpoint
    | internal "endpoint could be given twice"
  pure .unit

private noncomputable def trapAfterMixedMoves : P Mock.mock World (Ret Mock.mock) := do
  let _ ← createMixed
  let _ ← acceptNode sig limits Quirks.none context .lateTrap (.flat [i32Flat 1, i32Flat 2, i32Flat 1]) []
  pure .unit

private noncomputable def initial (program : P Mock.mock World (Ret Mock.mock)) :
    Machine.Config Mock.mock World where
  store := { CStore.empty with
    core := { mems := [⟨.i32, ⟨#[1, 0, 0, 0, 2, 0, 0, 0]⟩⟩] }
    insts := [{}]
    resourceTypes := [{ impl := some ⟨0⟩ }]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := {}
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) program]

private def noReady : HostReady World := fun _ _ => false

private noncomputable def noCalls (_ : Canon.Call Mock.mock) : P Mock.mock World (Ret Mock.mock) :=
  internal "unexpected component call"

private noncomputable def run (X : Mock.mock.Exec) (program : P Mock.mock World (Ret Mock.mock)) :=
  Machine.run noReady noCalls X Machine.Oracle.first 256 (initial program)

theorem machine_session_sound (X : Mock.mock.Exec) :
    Machine.Steps .deterministic noReady noCalls (initial roundTrip)
      (run X roundTrip).labels (run X roundTrip).config :=
  Machine.run_sound noReady noCalls X Machine.Oracle.first 256 (initial roundTrip)

theorem give_and_drop_spend_distinct_equal_rep_owners_once (X : Mock.mock.Exec) :
    let result := run X roundTrip
    (result.outcome, result.config.host.accepted.length, result.config.host.held.map receiptId,
      (result.config.store.insts.get? 0).bind (fun inst => inst.handles.get? 2)) =
      (.resolved, 1, [], some (.resource ⟨2⟩)) := by
  dsimp only
  kernel_rfl

theorem reacquire_reused_slots_without_reviving_spent_claims (X : Mock.mock.Exec) :
    let result := run X reacquire
    (result.outcome, result.config.host.accepted.length, result.config.host.held.map receiptId) =
      (.resolved, 2, [⟨3⟩]) := by
  dsimp only
  kernel_rfl

theorem trapping_destructor_keeps_other_owner_and_tree (X : Mock.mock.Exec) :
    let result := run X trapDuringDrop
    (result.labels.any (fun label => match label with | .trap (.unknownHandle 42) => true | _ => false),
      result.config.host.accepted.length, result.config.host.held.map receiptId) =
      (true, 1, [⟨0⟩]) := by
  dsimp only
  kernel_rfl

/-- Missing destination fixture: the new owning object exists but was not inserted.
Inspect retry admission in the reached host state, not a guest call after lockdown. -/
theorem trapping_give_spends_claim_before_insertion (X : Mock.mock.Exec) :
    let result := run X trapDuringGive
    let store := result.config.store
    let state := result.config.host
    let refused := match state.prepare resource ⟨1⟩ with | .error .unclaimed => true | _ => false
    (result.labels.any (fun label => match label with
      | .trap (.internal "dangling arena id") => true
      | _ => false), refused, state.accepted.length, state.held.map receiptId,
      (store.inst? ⟨0⟩).bind (·.handles.get? 2),
      (store.resHandle? ⟨3⟩).map (fun handle => (handle.rt, handle.rep, handle.own)),
      (store.core.mems[0]?.map (·.bytes)).bind (·[0]?)) =
      (true, true, 1, [], some (.resource ⟨2⟩), some (resource, 77, true), some 7) := by
  dsimp only
  kernel_rfl

theorem trapping_second_move_preserves_earlier_claims_without_publishing_partial_claims
    (X : Mock.mock.Exec) :
    let result := run X trapDuringSecondMove
    (result.labels.any (fun label => match label with | .trap (.unknownHandle 2) => true | _ => false),
      result.config.host.accepted.length, result.config.host.held.map receiptId,
      (result.config.store.insts.get? 0).bind (fun inst => inst.handles.get? 2)) =
      (true, 1, [⟨0⟩, ⟨1⟩], none) := by
  dsimp only
  kernel_rfl

theorem mixed_round_trip_sound (X : Mock.mock.Exec) :
    Machine.Steps .deterministic noReady noCalls (initial mixedRoundTrip)
      (run X mixedRoundTrip).labels (run X mixedRoundTrip).config :=
  Machine.run_sound noReady noCalls X Machine.Oracle.first 256 (initial mixedRoundTrip)

theorem mixed_round_trip_transfers_both_claims_once (X : Mock.mock.Exec) :
    let result := run X mixedRoundTrip
    (result.outcome, result.config.host.accepted.length, result.config.host.held.length,
      result.config.host.endpoints.length) = (.resolved, 1, 0, 0) := by
  dsimp only
  kernel_rfl

theorem late_trap_retains_both_moves_but_publishes_neither_claim_nor_tree (X : Mock.mock.Exec) :
    let result := run X trapAfterMixedMoves
    let store := result.config.store
    let handles := (store.insts.get? 0).map (·.handles)
    (result.labels.any (fun label => match label with | .trap (.unknownHandle 1) => true | _ => false),
      result.config.host.accepted.length, result.config.host.held.length,
      result.config.host.endpoints.length, handles.bind (·.get? 1), handles.bind (·.get? 2),
      (store.end? ⟨0⟩).map (fun endpoint => (endpoint.owner, endpoint.index))) =
      (true, 0, 0, 0, none, none, some (none, none)) := by
  dsimp only
  kernel_rfl

theorem mixed_trap_sound (X : Mock.mock.Exec) :
    Machine.Steps .deterministic noReady noCalls (initial trapAfterMixedMoves)
      (run X trapAfterMixedMoves).labels (run X trapAfterMixedMoves).config :=
  Machine.run_sound noReady noCalls X Machine.Oracle.first 256 (initial trapAfterMixedMoves)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Examples
