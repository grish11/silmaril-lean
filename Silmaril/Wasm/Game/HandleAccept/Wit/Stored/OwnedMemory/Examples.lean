module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Component.Reference.Canon.Builtins.Waitable.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Examples

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Value

private def resource : RtId := ⟨0⟩

private def signature : Stored.Signature :=
  ⟨Unit, fun _ => .record [("items", .list (.own resource)), ("last", .option (.own resource))],
    fun _ => .fixed 0⟩

private abbrev World := List (OwnedMemory.Tree signature)

private def limits : Component.Limits := Component.Limits.spec

private noncomputable def context : LiftLowerContext Mock.mock :=
  { opts := { memory := some 0 }, inst := ⟨0⟩ }

private def data (lastSlot : UInt8) : ByteArray :=
  ⟨#[16, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, lastSlot, 0, 0, 0, 1, 0, 0, 0]⟩

private noncomputable def liftBoth (input : Input := .memory 0) : P Mock.mock World (Ret Mock.mock) := do
  let _ ← Builtins.resourceNew limits resource 77
  let _ ← Builtins.resourceNew limits resource 77
  let .ok tree ← buildNode signature limits Quirks.none context () input []
    | internal "ownership tree was not lifted"
  hostSet [tree]
  pure .unit

private noncomputable def initial (lastSlot : UInt8)
    (input : Input := .memory 0) : Machine.Config Mock.mock World where
  store := { CStore.empty with
    core := { mems := [⟨.i32, data lastSlot⟩] }
    insts := [{}]
    resourceTypes := [{ impl := some ⟨0⟩ }]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := []
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) (liftBoth input)]

private def noReady : HostReady World := fun _ _ => false

private noncomputable def noCalls (_ : Canon.Call Mock.mock) : P Mock.mock World (Ret Mock.mock) :=
  internal "unexpected call during owner lift"

private noncomputable def run (X : Mock.mock.Exec) (lastSlot : UInt8)
    (input : Input := .memory 0) :=
  Machine.run noReady noCalls X Machine.Oracle.first 224 (initial lastSlot input)

private noncomputable def observed : OwnedMemory.Tree signature → Observed
  | .atom impossible => impossible.elim
  | .tag payload _ _ => payload.2.val

private def receiptSummary (entry : Receipt) : HandleObjId × Nat :=
  (entry.2.identity, entry.2.representation)

theorem machine_session_sound (X : Mock.mock.Exec) (lastSlot : UInt8) :
    Machine.Steps .deterministic noReady noCalls (initial lastSlot)
      (run X lastSlot).labels (run X lastSlot).config :=
  Machine.run_sound noReady noCalls X Machine.Oracle.first 224 (initial lastSlot)

theorem nested_owners_with_equal_rep_keep_distinct_identities (X : Mock.mock.Exec) :
    let result := run X 2
    (result.outcome, result.config.host.map (fun tree =>
      let payload := observed tree
      (payload.value, payload.owners.map receiptSummary))) =
        (.resolved, [(.record [.list [.own 77], .variant 1 (some (.own 77))],
          [(⟨0⟩, 77), (⟨1⟩, 77)])]) := by
  dsimp only
  kernel_rfl

theorem double_move_traps_without_reversing_first_removal (X : Mock.mock.Exec) :
    let result := run X 1
    (result.labels.any (fun label => match label with | .trap (.unknownHandle 1) => true | _ => false),
      result.config.host.isEmpty,
      (result.config.store.insts.get? 0).map (fun inst =>
        (inst.handles.get? 1, inst.handles.get? 2))) =
      (true, true, some (none, some (.resource ⟨1⟩))) := by
  dsimp only
  kernel_rfl

theorem inactive_borrow_rejected :
    checkSchema (.result (some (.own resource)) (some (.list (.borrow resource)))) =
      .error .storedBorrow := rfl

private def otherResource : RtId := ⟨1⟩

private def nominalPayloadType : TypeOf :=
  .record [("entries", .map .u8 (.own resource)),
    ("choice", .result (some (.own otherResource)) (some (.own resource)))]

private def nominalPayload : Val :=
  .record [.list [.record [.int .u8 3, .own 77]], .variant 0 (some (.own 77))]

private def nominalReceipts : List Receipt :=
  [⟨resource, ⟨⟨4⟩, 77⟩⟩, ⟨otherResource, ⟨⟨9⟩, 77⟩⟩]

theorem equal_rep_receipts_in_nominal_order_are_admitted :
    (checkValue nominalPayloadType ⟨nominalPayload, nominalReceipts⟩).isOk = true := by decide

theorem equal_rep_receipts_in_wrong_nominal_order_are_refused :
    (match checkValue nominalPayloadType ⟨nominalPayload, nominalReceipts.reverse⟩ with
      | .error .incompleteReceipts => true
      | _ => false) = true := by decide

private def flatInput (lastSlot : Nat) : Input :=
  .flat ([16, 1, 1, lastSlot].map i32Flat)

theorem flat_session_sound (X : Mock.mock.Exec) (lastSlot : Nat) :
    Machine.Steps .deterministic noReady noCalls (initial 0 (flatInput lastSlot))
      (run X 0 (flatInput lastSlot)).labels (run X 0 (flatInput lastSlot)).config :=
  Machine.run_sound noReady noCalls X Machine.Oracle.first 224 (initial 0 (flatInput lastSlot))

theorem flat_lift_preserves_direct_and_indirect_owners (X : Mock.mock.Exec) :
    let result := run X 0 (flatInput 2)
    (result.outcome, result.config.host.map (fun tree =>
      let payload := observed tree
      (payload.value, payload.owners.map receiptSummary))) =
        (.resolved, [(.record [.list [.own 77], .variant 1 (some (.own 77))],
          [(⟨0⟩, 77), (⟨1⟩, 77)])]) := by
  dsimp only
  kernel_rfl

theorem repeated_flat_slot_does_not_revive_an_indirect_move (X : Mock.mock.Exec) :
    let result := run X 0 (flatInput 1)
    (result.labels.any (fun label => match label with | .trap (.unknownHandle 1) => true | _ => false),
      result.config.host.isEmpty,
      (result.config.store.insts.get? 0).map (fun inst =>
        (inst.handles.get? 1, inst.handles.get? 2))) =
      (true, true, some (none, some (.resource ⟨1⟩))) := by
  dsimp only
  kernel_rfl

private noncomputable def rejectThenRetry : P Mock.mock World (Ret Mock.mock) := do
  let _ ← Builtins.resourceNew limits resource 77
  let _ ← Builtins.resourceNew limits resource 77
  let invalid := Input.flat [i32Flat 16, i32Flat 1, i32Flat 0, .int .i64 2]
  let .error (.schema .flatTypes) ← buildNode signature limits Quirks.none context () invalid []
    | internal "an incompatible flat vector was not rejected before lifting"
  let .ok tree ← buildNode signature limits Quirks.none context () (flatInput 2) []
    | internal "the typed refusal did not leave both owners available"
  hostSet [tree]
  pure .unit

theorem malformed_inactive_slot_rejects_before_a_move_and_can_retry (X : Mock.mock.Exec) :
    let start := { initial 0 with ctl := [Machine.Activation.ofProg (some ⟨0⟩) rejectThenRetry] }
    let result := Machine.run noReady noCalls X Machine.Oracle.first 256 start
    (result.outcome, result.config.host.map (fun tree => (observed tree).owners.map receiptSummary)) =
      (.resolved, [[(⟨0⟩, 77), (⟨1⟩, 77)]]) := by
  dsimp only
  kernel_rfl

/-! ## The async canonical lower's argument and result cursor -/

private inductive ResolveMode where
  | immediate | cancelBeforeStart | cancelAfterStart
  deriving DecidableEq

private structure CallerLog where
  owners : List Receipt := []
  lowerReply : List FlatValue := []
  cancelReply : List FlatValue := []

private def callerType (spill : Bool) : WIT.FuncType Empty RtId :=
  ⟨[("pair", .tuple [.own resource, .own resource])] ++
    (if spill then [("a", .prim .u32), ("b", .prim .u32), ("c", .prim .u32)] else []),
    some (.prim .u32), true⟩

private noncomputable def callerDispatch (mode : ResolveMode) : Call Mock.mock →
    P Mock.mock CallerLog (Ret Mock.mock)
  | .funcInst _ caller => do
    if mode != .cancelBeforeStart then
      let _ ← callVals (.onStart caller)
    if mode = .immediate then
      callUnit (.onResolve caller (some [Val.u32 42]))
      return .cancel .none
    return .cancel (.host caller.idx)
  | .onStart caller => do
    let args ← observeLowerOnStart limits Quirks.none caller
    hostSet { (← hostGet) with owners := args.flatMap Observed.owners }
    return .vals (args.map Observed.value)
  | .onCancel (.host caller) => do
    callUnit (.onResolve ⟨caller⟩ none)
    return .unit
  | .onResolve caller result => do
    lowerOnResolve limits Quirks.none caller result
    return .unit
  | _ => internal "unexpected call during lower caller replay"

private noncomputable def callerProgram (mode : ResolveMode) (spill : Bool) (slot : UInt8) :
    P Mock.mock CallerLog (Ret Mock.mock) := do
  let _ ← Builtins.resourceNew limits resource 77
  let _ ← Builtins.resourceNew limits resource 77
  let args := if spill then [i32Flat 0, i32Flat 20]
    else [i32Flat 1, i32Flat slot.toNat, i32Flat 20]
  let reply ← canonLower limits Quirks.none ⟨0⟩ (callerType spill)
    { context.opts with async_ := true } ⟨0⟩ args
  let cancelled ← if mode = .immediate then pure [] else do
    let [packed] := reply | internal "unexpected async lower result arity"
    let some (.pending _ handle) := AsyncRef.AsyncLowerResult.unpack? (flatNat packed)
      | internal "expected pending async lower result"
    Builtins.subtaskCancel limits true handle
  hostSet { (← hostGet) with lowerReply := reply, cancelReply := cancelled }
  return .unit

private noncomputable def callerInitial (mode : ResolveMode) (spill : Bool) (slot : UInt8) :
    Machine.Config Mock.mock CallerLog where
  store := { (initial 0).store with
    core := { mems := [⟨.i32, ⟨#[1, 0, 0, 0, slot, 0, 0, 0, 10, 0, 0, 0,
      11, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0]⟩⟩] } }
  host := {}
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) (callerProgram mode spill slot)]

private def callerReady : HostReady CallerLog := fun _ _ => false

private noncomputable def runCaller (X : Mock.mock.Exec) (mode : ResolveMode) (spill : Bool)
    (slot : UInt8) :=
  Machine.run callerReady (callerDispatch mode) X Machine.Oracle.first 320
    (callerInitial mode spill slot)

private def callerPosition (store : CStore Mock.mock) : Option Nat :=
  match store.caller? ⟨0⟩ with
  | some (.lower _ _ _ pos _ _ _) => some pos
  | _ => none

theorem caller_replay_sound (X : Mock.mock.Exec) (mode : ResolveMode) (spill : Bool) (slot : UInt8) :
    Machine.Steps .deterministic callerReady (callerDispatch mode) (callerInitial mode spill slot)
      (runCaller X mode spill slot).labels (runCaller X mode spill slot).config :=
  Machine.run_sound callerReady (callerDispatch mode) X Machine.Oracle.first 320
    (callerInitial mode spill slot)

theorem whole_caller_lift_keeps_nominal_identity_and_resolve_uses_cursor (X : Mock.mock.Exec) :
    ∀ spill : Bool,
      let result := runCaller X .immediate spill 2
      (result.outcome, result.config.host.owners.map receiptSummary,
        result.config.host.lowerReply, callerPosition result.config.store,
        result.config.store.core.mems[0]?.bind (·.bytes.data[20]?)) =
      (.resolved, [(⟨0⟩, 77), (⟨1⟩, 77)], [i32Flat AsyncRef.AsyncLowerResult.returned.pack],
        some (if spill then 1 else 2), some 42) := by
  intro spill
  cases spill <;> (dsimp only; kernel_rfl)

theorem spilling_double_move_traps_before_cursor_commit (X : Mock.mock.Exec) :
    let result := runCaller X .immediate true 1
    (result.labels.any (fun label => match label with | .trap (.unknownHandle 1) => true | _ => false),
      result.config.host.owners.isEmpty, callerPosition result.config.store,
      (result.config.store.insts.get? 0).map (fun inst => (inst.handles.get? 1, inst.handles.get? 2))) =
    (true, true, some 0, some (none, some (.resource ⟨1⟩))) := by
  dsimp only
  kernel_rfl

theorem cancelling_before_or_after_start_preserves_the_reference_phase (X : Mock.mock.Exec) :
    ∀ beforeStart : Bool,
      let result := runCaller X (if beforeStart then .cancelBeforeStart else .cancelAfterStart)
        true 2
      (result.outcome, result.config.host.owners.map receiptSummary, result.config.host.lowerReply,
        result.config.host.cancelReply, callerPosition result.config.store,
        result.config.store.core.mems[0]?.bind (·.bytes.data[20]?)) =
      (.resolved, if beforeStart then [] else [(⟨0⟩, 77), (⟨1⟩, 77)],
        [i32Flat (if beforeStart then AsyncRef.AsyncLowerResult.pending .starting 3
          else .pending .started 2).pack],
        [i32Flat (AsyncRef.subtaskCancelResult
          (some (if beforeStart then .cancelledBeforeStarted else .cancelledBeforeReturned)))],
        some (if beforeStart then 0 else 1), some 0) := by
  intro beforeStart
  cases beforeStart <;> (dsimp only; kernel_rfl)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Examples
