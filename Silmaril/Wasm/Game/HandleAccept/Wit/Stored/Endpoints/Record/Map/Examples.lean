module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.MapExamples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime

private def entryMap : TypeOf := .map .string (.future none)
private def recordType : TypeOf := .record [("mark", .prim .u8), ("entries", entryMap)]
private def aliasType : TypeOf := .record [("direct", .future none), ("entries", entryMap)]
private def signature : Signature := ⟨Unit, fun _ => recordType, fun _ => .fixed 0⟩
private abbrev World := State signature

private noncomputable def context : LiftLowerContext Mock.mock :=
  { opts := { memory := some 0, realloc := some 0, encoding := .utf8 }, inst := ⟨0⟩ }

private noncomputable def session (memory reenter : Bool) : P Mock.mock World (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let _ ← (Async.Call.create .future none).program limits Quirks.none
  let .ok (.tag label _ _) ← acceptNode signature limits Quirks.none context ()
      (.flat [i32Flat 42, i32Flat 64, i32Flat 1]) []
    | internal "could not lift the endpoint map"
  let .record [_, entries] := label.2.val | internal "wrong lifted shape"
  let .ok aliased := checkValue aliasType (.record [.future ⟨0⟩, entries])
    | internal "wrong alias fixture"
  let .error (.preflight .unclaimed) ← lower limits Quirks.none context aliasType aliased (.memory 0)
    | internal "map alias accepted before allocation"
  trapIf ((← loadInt context 56 1 false) != 0) (.internal "refused map called realloc")
  if memory then
    match ← lower limits Quirks.none context recordType label.2 (.memory 0) with
    | .error (.nested 1 (.nested 0 (.field 1 (.beforeAllocation .unclaimed)))) =>
      trapIf (!reenter) (.internal "unexpected post-key refusal")
    | .ok () => trapIf reenter (.internal "reentrant key allocation did not invalidate the claim")
    | .error _ => internal "wrong map refusal"
  else
    let .ok words ← lower limits Quirks.none context recordType label.2 .flat
      | internal "could not flatten the endpoint map"
    let actual : List FlatValue := words
    trapIf (actual != [i32Flat 42, i32Flat 24, i32Flat 1]) (.internal "wrong map pointer or length")
  return .unit

private noncomputable def initial (memory reenter : Bool) : Machine.Config Mock.mock World where
  store := { CStore.empty with
    core := { mems := [⟨.i32, ⟨Array.replicate 64 0 ++ #[80, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0,
      0, 0, 0, 0, 107, 101, 121]⟩⟩] }
    insts := [{}]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := {}
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) (session memory reenter)]

private noncomputable def dispatch (reenter : Bool) : Canon.Call Mock.mock → P Mock.mock World (Ret Mock.mock)
  | .reallocate _ 0 0 4 12 => do
    storeInt context 7 56 1
    return .nat 24
  | .reallocate _ 0 0 1 3 => do
    storeInt context 9 57 1
    if reenter then
      let .ok 1 ← give Limits.spec context .future none ⟨⟨0⟩⟩
        | internal "reentrant future transfer failed"
    return .nat 48
  | _ => internal "unexpected allocator call"

private def noReady : HostReady World := fun _ _ => false

private noncomputable def run (exec : Mock.mock.Exec) (memory reenter : Bool) :=
  Machine.run noReady (dispatch reenter) exec Machine.Oracle.first 360 (initial memory reenter)

theorem map_session_sound (exec : Mock.mock.Exec) (memory reenter : Bool) :
    Machine.Steps .deterministic noReady (dispatch reenter) (initial memory reenter)
      (run exec memory reenter).labels (run exec memory reenter).config :=
  Machine.run_sound noReady (dispatch reenter) exec Machine.Oracle.first 360 (initial memory reenter)

theorem map_entries_use_canonical_key_and_value_layout (exec : Mock.mock.Exec) (memory : Bool) :
    let result := run exec memory false
    let bytes := (result.config.store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
    (result.outcome, result.config.host.held, (bytes.extract 0 12).data, (bytes.extract 24 36).data,
      (bytes.extract 48 51).data, (bytes.extract 56 58).data) =
      (.resolved, [], (if memory then #[42, 0, 0, 0, 24, 0, 0, 0, 1, 0, 0, 0] else Array.replicate 12 0),
        #[48, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0], #[107, 101, 121], #[7, 9]) := by
  cases memory <;> dsimp only <;> kernel_rfl

theorem reentrant_key_realloc_keeps_key_but_does_not_publish_map (exec : Mock.mock.Exec) :
    let result := run exec true true
    let bytes := (result.config.store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
    (result.outcome, result.config.host.held, (bytes.extract 0 12).data, (bytes.extract 24 36).data,
      (bytes.extract 48 51).data, (bytes.extract 56 58).data) =
      (.resolved, [], #[42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        #[48, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0], #[107, 101, 121], #[7, 9]) := by
  dsimp only
  kernel_rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.MapExamples
