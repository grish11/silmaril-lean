module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Examples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime

private def resource : RtId := ⟨0⟩
private def recordType : TypeOf :=
  .record [("owners", .fixedList (.own resource) 2), ("end", .option (.future none))]
private def allocatedType : TypeOf := .record [("items", .list (.tuple [.own resource, .future none]))]
private def borrowType : TypeOf := .record [("inactive", .option (.borrow resource))]
private def trapType : TypeOf := .record [("owner", .own resource), ("text", .prim .string)]
private def signature : Signature :=
  ⟨Option Bool, fun
    | some false => recordType
    | some true => allocatedType
    | none => trapType, fun _ => .fixed 0⟩
private abbrev World := State signature

private noncomputable def context : LiftLowerContext Mock.mock :=
  { opts := { memory := some 0, realloc := some 0 }, inst := ⟨0⟩ }

private noncomputable def fixed (memory : Bool) (missingDestination : Bool := false) :
    P Mock.mock World (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let _ ← Builtins.resourceNew limits resource 77
  let _ ← Builtins.resourceNew limits resource 77
  let _ ← Builtins.futureNew limits none
  let .ok (.tag label children proof) ← acceptNode signature limits Quirks.none context (some false)
      (.flat [i32Flat 1, i32Flat 2, i32Flat 1, i32Flat 3]) []
    | internal "could not accept the mixed record"
  let observed := label.2.val
  let first :: second :: [] := observed.owners | internal "wrong owner receipts"
  trapIf (receiptId first == receiptId second) (.internal "owner lift collapsed equal representations")
  let .ok aliased := OwnedMemory.checkValue recordType { observed with owners := [first, first] }
    | internal "could not construct alias fixture"
  let .error (.claims .unclaimed) ← lower Access.direct limits Quirks.none context recordType aliased (.memory 0)
    | internal "aliased owners were transmitted"
  let .ok inactive := OwnedMemory.checkValue borrowType (.ordinary (.record [.variant 0 none]))
    | internal "could not construct inactive borrow fixture"
  let .error (.preflight (.schema .storedBorrow)) ←
      lower Access.direct limits Quirks.none context borrowType inactive (.memory 0)
    | internal "inactive stored borrow was accepted"
  trapIf ((← loadInt context 0 4) != 0) (.internal "alias refusal wrote output")
  let tree : Tree signature := .tag label children proof
  if missingDestination then
    let _ ← lowerRoot Access.direct limits Quirks.none { context with inst := ⟨1⟩ } tree (.memory 0)
    return .unit
  if memory then
    let .ok () ← lowerRoot Access.direct limits Quirks.none context tree (.memory 0)
      | internal "corrected memory lowering did not succeed"
    trapIf ((← loadInt context 0 4) != 3 || (← loadInt context 4 4) != 2 ||
      (← loadInt context 8 1) != 1 || (← loadInt context 12 4) != 1)
      (.internal "wrong mixed memory layout")
  else
    let .ok words ← lowerRoot Access.direct limits Quirks.none context tree .flat
      | internal "corrected flat lowering did not succeed"
    let words : List FlatValue := words
    trapIf (words != [i32Flat 3, i32Flat 2, i32Flat 1, i32Flat 1]) (.internal "wrong mixed flat values")
  let .error (.claims .unclaimed) ← lowerRoot Access.direct limits Quirks.none context tree .flat
    | internal "old receipt became live after guest slot reuse"
  return .unit

private noncomputable def allocating : P Mock.mock World (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let _ ← Builtins.resourceNew limits resource 77
  let _ ← Builtins.futureNew limits none
  let .ok tree ← acceptNode signature limits Quirks.none context (some true) (.flat [i32Flat 48, i32Flat 1]) []
    | internal "could not accept owner/future list"
  let .error (.nested 0 (.claims .unclaimed)) ← lowerRoot Access.direct limits Quirks.none context tree (.memory 0)
    | internal "list kept a stale reservation after realloc"
  return .unit

private noncomputable def lateTrap : P Mock.mock World (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let _ ← Builtins.resourceNew limits resource 77
  let .ok tree ← acceptNode signature limits Quirks.none context none (.flat [i32Flat 1, i32Flat 48, i32Flat 1]) []
    | internal "could not accept owner/string record"
  let _ ← lowerRoot Access.direct limits Quirks.none context tree (.memory 0)
  return .unit

private noncomputable def dispatch : Canon.Call Mock.mock → P Mock.mock World (Ret Mock.mock)
  | .reallocate _ 0 0 4 8 => do
    storeInt context 7 32 1
    let .ok _ ← Claims.give Limits.spec context resource ⟨0⟩
      | internal "reentrant owner transfer failed"
    return .nat 24
  | .reallocate _ 0 0 1 1 => trap .outOfBounds
  | _ => internal "unexpected allocator call"

private noncomputable def initial (program : P Mock.mock World (Ret Mock.mock)) : Machine.Config Mock.mock World where
  store := { CStore.empty with
    core := { mems := [⟨.i32, ⟨Array.replicate 48 0 ++ #[1, 0, 0, 0, 2, 0, 0, 0]⟩⟩] }
    insts := [{}]
    resourceTypes := [{ impl := some ⟨0⟩ }]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := {}
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) program]

private def noReady : HostReady World := fun _ _ => false

private noncomputable def run (exec : Mock.mock.Exec) (program : P Mock.mock World (Ret Mock.mock)) :=
  Machine.run noReady dispatch exec Machine.Oracle.first 336 (initial program)

theorem roundtrip_sound (exec : Mock.mock.Exec) (memory : Bool) :
    Machine.Steps .deterministic noReady dispatch (initial (fixed memory))
      (run exec (fixed memory)).labels (run exec (fixed memory)).config :=
  Machine.run_sound noReady dispatch exec Machine.Oracle.first 336 (initial (fixed memory))

theorem correct_retry_lowers_distinct_equal_rep_owners_and_future (exec : Mock.mock.Exec) (memory : Bool) :
    let result := run exec (fixed memory)
    let handles := (result.config.store.inst? ⟨0⟩).map (·.handles)
    (result.outcome, result.config.host.held.map receiptId, result.config.host.endpoints,
      handles.bind (·.get? 3), handles.bind (·.get? 2)) =
      (.resolved, [], [], some (.resource ⟨2⟩), some (.resource ⟨3⟩)) := by
  cases memory <;> dsimp only <;> kernel_rfl

theorem reentry_preserves_allocator_effects_and_leaves_future_held (exec : Mock.mock.Exec) :
    let result := run exec allocating
    let bytes := (result.config.store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
    (result.outcome, result.config.host.accepted.length, result.config.host.held.map receiptId,
      result.config.host.endpoints, (bytes.extract 0 32).data, bytes[32]?) =
      (.resolved, 1, [], [⟨0⟩], Array.replicate 32 0, some 7) := by
  dsimp only
  kernel_rfl

theorem late_trap_preserves_committed_owner_and_prefix (exec : Mock.mock.Exec) :
    let result := run exec lateTrap
    let bytes := (result.config.store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
    (result.labels.any (fun label => match label with | .trap .outOfBounds => true | _ => false),
      result.config.host.accepted.length, result.config.host.held.map receiptId,
      (result.config.store.inst? ⟨0⟩).bind (fun inst => inst.handles.get? 1), (bytes.extract 0 12).data) =
      (true, 1, [], some (.resource ⟨1⟩), #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  dsimp only
  kernel_rfl

theorem failed_insertion_spends_owner_in_recursive_emitter (exec : Mock.mock.Exec) :
    let result := run exec (fixed true true)
    let state := result.config.host
    let store := result.config.store
    let refused := match state.prepare resource ⟨0⟩ with | .error .unclaimed => true | _ => false
    let bytes := (store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
    (result.labels.any (fun label => match label with
      | .trap (.internal "dangling arena id") => true
      | _ => false), refused, state.accepted.length, state.held.map receiptId, state.endpoints,
      (store.resHandle? ⟨2⟩).map (fun handle => (handle.rt, handle.rep, handle.own)),
      (store.inst? ⟨0⟩).bind (·.handles.get? 1), (bytes.extract 0 12).data) =
      (true, true, 1, [⟨1⟩], [⟨0⟩], some (resource, 77, true), none, Array.replicate 12 0) := by
  dsimp only
  kernel_rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Examples
