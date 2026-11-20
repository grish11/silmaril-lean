module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower.Thms
import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower.Examples

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Formats

def sig : Signature :=
  ⟨Unit, fun _ => .record [("tag", .prim .u8), ("items", .option (.fixedList (.prim .u16) 2))],
    fun _ => .fixed 0⟩

def value : Val := .record [.int .u8 7, .variant 1 (some (.list [.int .u16 513, .int .u16 1027]))]

def payload : Payload (sig.payload ()) := ⟨value, by decide⟩

noncomputable def roundtrip (output : Output) : P Mock.mock (List (Tree sig)) (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let cx : LiftLowerContext Mock.mock := { opts := { memory := some 0 }, inst := ⟨0⟩ }
  let input ← match output with
    | .memory ptr => do
      let .ok () ← lower limits Quirks.none cx (sig.payload ()) payload (.memory ptr)
        | internal "unexpected lower diagnostic"
      pure (Input.memory ptr)
    | .flat => do
      let .ok values ← lower limits Quirks.none cx (sig.payload ()) payload .flat
        | internal "unexpected lower diagnostic"
      pure (Input.flat values)
  let .ok tree ← buildNode sig limits Quirks.none cx () input []
    | internal "unexpected lift diagnostic"
  record sig tree
  pure .unit

def acceptedPayload {signature : Signature} : Tree signature → Val
  | .atom impossible => impossible.elim
  | .tag label _ _ => label.2.val

noncomputable def initial (width : AddrType) (output : Output) :
    Machine.Config Mock.mock (List (Tree sig)) where
  store := { CStore.empty with
    core := { mems := [⟨width, ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩⟩] }
    insts := [{}]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := []
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) (roundtrip output)]

def noReady {signature : Signature} : HostReady (List (Tree signature)) := fun _ _ => false

noncomputable def noCalls (_ : Canon.Call Mock.mock) : P Mock.mock (List (Tree sig)) (Ret Mock.mock) :=
  internal "unexpected call during payload roundtrip"

noncomputable def run (exec : Mock.mock.Exec) (width : AddrType) (output : Output) :=
  Machine.run noReady noCalls exec Machine.Oracle.first 160 (initial width output)

theorem roundtrip_sound (exec : Mock.mock.Exec) (width : AddrType) (output : Output) :
    Machine.Steps .deterministic noReady noCalls (initial width output)
      (run exec width output).labels (run exec width output).config :=
  Machine.run_sound noReady noCalls exec Machine.Oracle.first 160 (initial width output)

theorem memory64_roundtrip (exec : Mock.mock.Exec) :
    let result := run exec .i64 (.memory 0)
    (result.outcome, result.config.host.map acceptedPayload,
      Mock.mock.memRead? result.config.store.core 0 0 8) =
      (.resolved, [value], some ⟨#[7, 0, 1, 0, 1, 2, 3, 4]⟩) := by
  dsimp only
  kernel_rfl

theorem flat_roundtrip (exec : Mock.mock.Exec) :
    let result := run exec .i32 .flat
    (result.outcome, result.config.host.map acceptedPayload) =
      (.resolved, [value]) := by
  dsimp only
  kernel_rfl

theorem out_of_bounds_preserves_memory (exec : Mock.mock.Exec) :
    let result := run exec .i32 (.memory 2)
    (result.labels.any (fun label => match label with
      | .trap .outOfBounds => true
      | _ => false), result.config.host.isEmpty,
      Mock.mock.memRead? result.config.store.core 0 0 8) =
      (true, true, some ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩) := by
  dsimp only
  kernel_rfl

theorem rejects_inactive_nested_endpoint :
    checkSchema (.option (.list (.future none))) = .error .endpointNeedsTransfer := by kernel_rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower.Examples
