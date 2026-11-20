module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.ListExamples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime

private def entry : TypeOf := .tuple [.prim .u8, .fixedList (.future none) 2]
private def recordType : TypeOf := .record [("mark", .prim .u8), ("entries", .list entry)]
private def signature : Signature := ⟨Unit, fun _ => recordType, fun _ => .fixed 0⟩
private abbrev World := State signature

private noncomputable def context : LiftLowerContext Mock.mock :=
  { opts := { memory := some 0, realloc := some 0 }, inst := ⟨0⟩ }

private def duplicate : Payload recordType :=
  ⟨.record [.int .u8 50, .list [.record [.int .u8 11, .list [.future ⟨0⟩, .future ⟨0⟩]]]], by decide⟩

private noncomputable def session (reenter : Bool) : P Mock.mock World (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  for _ in [0, 1, 2, 3] do
    let _ ← (Async.Call.create .future none).program limits Quirks.none
  let .ok (.tag label _ _) ← acceptNode signature limits Quirks.none context ()
      (.flat [i32Flat 42, i32Flat 64, i32Flat 2]) []
    | internal "could not lift the fixed pairs inside a list"
  let .error (.preflight .unclaimed) ← lower limits Quirks.none context recordType duplicate (.memory 0)
    | internal "a duplicate endpoint was not detected before allocation"
  trapIf ((← loadInt context 0 1 false) != 0) (.internal "refusal wrote the record prefix")
  match ← lower limits Quirks.none context recordType label.2 (.memory 0) with
  | .error (.field 1 (.afterAllocation .unclaimed)) =>
    trapIf (!reenter) (.internal "unexpected post-allocation refusal")
  | .ok () => trapIf reenter (.internal "a reentrant transfer did not invalidate the list")
  | .error _ => internal "wrong refusal for the compound list"
  pure .unit

private noncomputable def initial (reenter : Bool) : Machine.Config Mock.mock World where
  store := { CStore.empty with
    core := { mems := [⟨.i32, ⟨Array.replicate 64 0 ++ #[11, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0,
      22, 0, 0, 0, 5, 0, 0, 0, 7, 0, 0, 0]⟩⟩] }
    insts := [{}]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := {}
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) (session reenter)]

private noncomputable def dispatch (reenter : Bool) : Canon.Call Mock.mock → P Mock.mock World (Ret Mock.mock)
  | .reallocate _ 0 0 4 24 => do
    storeInt context 9 56 1
    if reenter then
      let .ok 7 ← give Limits.spec context .future none ⟨⟨0⟩⟩
        | internal "reentrant future transfer failed"
    return .nat 24
  | _ => internal "unexpected allocator call"

private def noReady : HostReady World := fun _ _ => false

private noncomputable def run (exec : Mock.mock.Exec) (reenter : Bool) :=
  Machine.run noReady (dispatch reenter) exec Machine.Oracle.first 420 (initial reenter)

theorem compound_list_session_sound (exec : Mock.mock.Exec) (reenter : Bool) :
    Machine.Steps .deterministic noReady (dispatch reenter) (initial reenter)
      (run exec reenter).labels (run exec reenter).config :=
  Machine.run_sound noReady (dispatch reenter) exec Machine.Oracle.first 420 (initial reenter)

theorem aligned_elements_and_canonical_stride (exec : Mock.mock.Exec) :
    let result := run exec false
    let bytes := (result.config.store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
    (result.outcome, result.config.host.held, (bytes.extract 0 12).data, (bytes.extract 24 48).data) =
      (.resolved, [], #[42, 0, 0, 0, 24, 0, 0, 0, 2, 0, 0, 0],
        #[11, 0, 0, 0, 7, 0, 0, 0, 5, 0, 0, 0, 22, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0]) := by
  dsimp only
  kernel_rfl

theorem post_allocation_refusal_keeps_prefix_and_other_claims (exec : Mock.mock.Exec) :
    let result := run exec true
    let bytes := (result.config.store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
    (result.outcome, result.config.host.held, (bytes.extract 0 12).data,
      bytes[24]?, bytes[28]?, bytes[56]?) =
      (.resolved, [⟨2⟩, ⟨4⟩, ⟨6⟩], #[42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], some 0, some 0, some 9) := by
  dsimp only
  kernel_rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.ListExamples
