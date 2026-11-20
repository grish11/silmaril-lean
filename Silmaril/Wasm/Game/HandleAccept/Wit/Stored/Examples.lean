module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Async.Defs
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Examples

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Call)

def optionalFuture : Signature :=
  ⟨Unit, fun _ => .option (.future none), fun _ => .fixed 0⟩

def typedStream : Signature :=
  ⟨Unit, fun _ => .stream (some (.prim .u8)), fun _ => .fixed 0⟩

def twoFutures : Signature :=
  ⟨Unit, fun _ => .tuple [.future none, .future none], fun _ => .fixed 0⟩

def acceptedPayload {sig : Signature} : Tree sig → Val
  | .atom impossible => impossible.elim
  | .tag label _ _ => label.2.val

noncomputable def memoryFuture : P Mock.mock (List (Tree optionalFuture)) (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let _ ← (Call.create .future none).program limits Quirks.none
  let cx : LiftLowerContext Mock.mock := { opts := { memory := some 0 }, inst := ⟨0⟩ }
  let .ok tree ← buildNode optionalFuture limits Quirks.none cx () (.memory 0) []
    | internal "optional future was not lifted"
  record optionalFuture tree
  pure .unit

noncomputable def flatStream : P Mock.mock (List (Tree typedStream)) (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let _ ← (Call.create .stream (some (.prim .u8))).program limits Quirks.none
  let cx : LiftLowerContext Mock.mock := { opts := {}, inst := ⟨0⟩ }
  let .ok tree ← buildNode typedStream limits Quirks.none cx () (.flat [i32Flat 1]) []
    | internal "byte stream was not lifted"
  record typedStream tree
  pure .unit

noncomputable def repeatSlot : P Mock.mock (List (Tree twoFutures)) (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let _ ← (Call.create .future none).program limits Quirks.none
  let cx : LiftLowerContext Mock.mock := { opts := {}, inst := ⟨0⟩ }
  let .ok tree ← buildNode twoFutures limits Quirks.none cx () (.flat [i32Flat 1, i32Flat 1]) []
    | internal "expected a reference handle trap, not an adapter error"
  record twoFutures tree
  pure .unit

noncomputable def initial {sig : Signature} (body : P Mock.mock (List (Tree sig)) (Ret Mock.mock)) :
    Machine.Config Mock.mock (List (Tree sig)) where
  store := { CStore.empty with
    core := { mems := [⟨.i32, ⟨#[1, 0, 0, 0, 1, 0, 0, 0]⟩⟩] }
    insts := [{}]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := []
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) body]

def noReady {sig : Signature} : HostReady (List (Tree sig)) := fun _ _ => false

noncomputable def noCalls {sig : Signature} (_ : Canon.Call Mock.mock) :
    P Mock.mock (List (Tree sig)) (Ret Mock.mock) := internal "unexpected call during tree lift"

noncomputable def run {sig : Signature} (X : Mock.mock.Exec)
    (body : P Mock.mock (List (Tree sig)) (Ret Mock.mock)) :=
  Machine.run noReady noCalls X Machine.Oracle.first 160 (initial body)

theorem sessions_sound {sig : Signature} (X : Mock.mock.Exec)
    (body : P Mock.mock (List (Tree sig)) (Ret Mock.mock)) :
    Machine.Steps .deterministic noReady noCalls (initial body)
      (run X body).labels (run X body).config :=
  Machine.run_sound noReady noCalls X Machine.Oracle.first 160 (initial body)

theorem memory_future_becomes_tree_payload (X : Mock.mock.Exec) :
    let result := run X memoryFuture
    (result.outcome, result.config.host.map acceptedPayload,
      (result.config.store.insts.get? 0).map (fun inst => inst.handles.get? 1)) =
      (.resolved, [.variant 1 (some (.future ⟨0⟩))], some none) := by
  dsimp only
  kernel_rfl

theorem flat_stream_becomes_tree_payload (X : Mock.mock.Exec) :
    let result := run X flatStream
    (result.outcome, result.config.host.map acceptedPayload,
      (result.config.store.insts.get? 0).map (fun inst => inst.handles.get? 1)) =
      (.resolved, [.stream ⟨0⟩], some none) := by
  dsimp only
  kernel_rfl

theorem repeated_slot_traps_without_recording (X : Mock.mock.Exec) :
    let result := run X repeatSlot
    (result.labels.any (fun label => match label with
      | .trap (.unknownHandle 1) => true
      | _ => false), result.config.host.isEmpty,
      (result.config.store.insts.get? 0).map (fun inst => inst.handles.get? 1)) =
      (true, true, some none) := by
  dsimp only
  kernel_rfl

theorem rejects_inactive_nested_borrow :
    checkSchema (.option (.list (.borrow ⟨0⟩))) = .error .storedBorrow := rfl

theorem does_not_discard_nested_owner_identity :
    checkSchema (.result (some (.future none)) (some (.list (.own ⟨0⟩)))) =
      .error .ownedResourceNeedsIdentity := rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Examples
