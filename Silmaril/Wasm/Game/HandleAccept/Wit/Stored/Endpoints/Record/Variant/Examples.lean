module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.VariantExamples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime

private def element : Async.Element := some (.prim .u8)
private def choice : TypeOf := .variant [("wide", some (.prim .u64)),
  ("readers", some (.list (.stream element))), ("empty", none)]
private def response : TypeOf := .result (some choice) (some (.prim .u64))
private def recordType : TypeOf := .record [("response", response), ("mark", .prim .u8)]
private def signature : Signature := ⟨Unit, fun _ => recordType, fun _ => .fixed 0⟩
private abbrev World := State signature

private noncomputable def context : LiftLowerContext Mock.mock :=
  { opts := { memory := some 0, realloc := some 0 }, inst := ⟨0⟩ }

private def unsupported : TypeOf := .record [("choice", .variant
  [("none", none), ("map", some (.map .u8 (.own ⟨0⟩)))])]

theorem inactive_variant_checks_whole_schema :
    preflight context unsupported ⟨.record [.variant 0 none], by decide⟩ .flat =
      .error (.preflight (.schema .ownedResourceNeedsIdentity)) := by kernel_rfl

private def wide (value : Nat) : FlatValue := .int .i64 (BitVec.ofNat 64 value)

private noncomputable def session (memory : Bool) : P Mock.mock World (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let _ ← (Async.Call.create .stream element).program limits Quirks.none
  let .ok (.tag label _ _) ← acceptNode signature limits Quirks.none context ()
      (.flat [i32Flat 0, wide 1, wide 56, i32Flat 1, i32Flat 42]) []
    | internal "could not lift the readers variant"
  if memory then
    let .ok () ← lower limits Quirks.none context recordType label.2 (.memory 0)
      | internal "could not store the readers variant"
    pure .unit
  else
    let .ok words ← lower limits Quirks.none context recordType label.2 .flat
      | internal "could not flatten the readers variant"
    let actual : List FlatValue := words
    trapIf (actual != [i32Flat 0, wide 1, wide 40, i32Flat 1, i32Flat 42])
      (.internal "wrong canonical joined result slots")
    pure .unit

private noncomputable def initial (memory : Bool) : Machine.Config Mock.mock World where
  store := { CStore.empty with
    core := { mems := [⟨.i32, ⟨Array.replicate 56 0 ++ #[1, 0, 0, 0]⟩⟩] }
    insts := [{}]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := {}
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) (session memory)]

private noncomputable def dispatch (destination : Nat) : Canon.Call Mock.mock → P Mock.mock World (Ret Mock.mock)
  | .reallocate _ 0 0 4 4 => do
    storeInt context 9 48 1
    return .nat destination
  | _ => internal "unexpected allocator call"

private def noReady : HostReady World := fun _ _ => false

private noncomputable def run (exec : Mock.mock.Exec) (memory : Bool) (destination : Nat) :=
  Machine.run noReady (dispatch destination) exec Machine.Oracle.first 350 (initial memory)

theorem variant_session_sound (exec : Mock.mock.Exec) (memory : Bool) (destination : Nat) :
    Machine.Steps .deterministic noReady (dispatch destination) (initial memory)
      (run exec memory destination).labels (run exec memory destination).config :=
  Machine.run_sound noReady (dispatch destination) exec Machine.Oracle.first 350 (initial memory)

theorem variant_flat_slots (exec : Mock.mock.Exec) :
    let result := run exec false 40
    (result.outcome, result.config.host.held) = (.resolved, []) := by
  dsimp only
  kernel_rfl

theorem variant_aligned_payload_and_prefix (exec : Mock.mock.Exec) :
    let result := run exec true 40
    let bytes := (result.config.store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
    (result.outcome, result.config.host.held, (bytes.extract 0 25).data, bytes[48]?) =
      (.resolved, [], #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
        40, 0, 0, 0, 1, 0, 0, 0, 42], some 9) := by
  dsimp only
  kernel_rfl

theorem variant_allocator_trap_preserves_tags_and_claim (exec : Mock.mock.Exec) :
    let result := run exec true 41
    let bytes := (result.config.store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
    (result.labels.any (· matches .trap .unalignedPointer), result.config.host.held,
      bytes[8]?, bytes[24]?, bytes[48]?) = (true, [⟨0⟩], some 1, some 0, some 9) := by
  dsimp only
  kernel_rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.VariantExamples
