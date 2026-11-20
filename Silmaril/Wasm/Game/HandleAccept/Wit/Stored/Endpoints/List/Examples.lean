module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.List.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.ListLower.Examples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value

def element : Async.Element := some (.prim .u8)
def streamList : TypeOf := .list (endpointType .stream element)
def signature : Signature := ⟨Unit, fun _ => streamList, fun _ => .fixed 0⟩

noncomputable def cx : LiftLowerContext Mock.mock :=
  { opts := { memory := some 0, realloc := some 0 }, inst := ⟨0⟩ }

def aliases : Payload streamList := ⟨.list [.stream ⟨0⟩, .stream ⟨0⟩], by decide⟩

theorem empty_needs_realloc :
    preflight { cx with opts := { cx.opts with realloc := none } } .stream element
      ⟨.list [], by decide⟩ .flat = .error (.abi .reallocRequired) := by kernel_rfl

noncomputable def session (reenter memory : Bool) : P Mock.mock (State signature) (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let _ ← (Async.Call.create .stream element).program limits Quirks.none
  let _ ← (Async.Call.create .stream element).program limits Quirks.none
  let .ok (.tag label _ _) ← acceptNode signature limits Quirks.none cx () (.memory 0) []
    | internal "could not lift the stream list"
  let .error (.endpoint .wrongType) ← transfer limits cx .future element ⟨0⟩
    | internal "single endpoint transfer did not reject a wrong channel"
  let .error (.beforeAllocation .unclaimed) ← lower limits cx .stream element aliases .flat
    | internal "alias was not rejected before allocating"
  if memory then
    let .ok () ← lower limits cx .stream element label.2 (.memory 0)
      | internal "endpoint list was not stored to memory"
    return .unit
  let reply ← lower limits cx .stream element label.2 .flat
  if reenter then
    let .error (.afterAllocation .unclaimed) := reply | return ← internal "missing post-realloc rejection"
    pure .unit
  else
    let .ok words := reply | return ← internal "valid endpoint list was rejected"
    let flat : List FlatValue := words
    trapIf (flat != [i32Flat 16, i32Flat 2]) (.internal "wrong canonical flat list")
    pure .unit

noncomputable def dispatch (reenter : Bool) (ptr : Nat) :
    Canon.Call Mock.mock → P Mock.mock (State signature) (Ret Mock.mock)
  | .reallocate _ 0 0 4 8 => do
    let marker ← loadInt cx 24 1 false
    trapIf (marker != 0) (.internal "unexpected second allocation")
    storeInt cx 9 24 1
    if reenter then
      let .ok 3 ← give Component.Limits.spec cx .stream element ⟨⟨0⟩⟩
        | internal "reentrant transfer failed"
    return .nat ptr
  | _ => internal "unexpected allocator call"

noncomputable def initial (reenter memory : Bool) : Machine.Config Mock.mock (State signature) where
  store := { CStore.empty with
    insts := [{}]
    core := { mems := [⟨.i32, ⟨#[8, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]⟩⟩] }
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := {}
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) (session reenter memory)]

def noReady : HostReady (State signature) := fun _ _ => false

noncomputable def run (exec : Mock.mock.Exec) (reenter : Bool) (ptr : Nat := 16) (memory : Bool := false) :=
  Machine.run noReady (dispatch reenter ptr) exec Machine.Oracle.first 300 (initial reenter memory)

theorem session_sound (exec : Mock.mock.Exec) (reenter : Bool) (ptr : Nat) (memory : Bool) :
    Machine.Steps .deterministic noReady (dispatch reenter ptr) (initial reenter memory)
      (run exec reenter ptr memory).labels (run exec reenter ptr memory).config :=
  Machine.run_sound noReady (dispatch reenter ptr) exec Machine.Oracle.first 300 (initial reenter memory)

theorem realloc_and_transfer (exec : Mock.mock.Exec) :
    let result := run exec false
    (result.outcome, result.config.host.accepted.map rootIds, result.config.host.held,
      Mock.mock.memRead? result.config.store.core 0 16 9,
      (result.config.store.insts.get? 0).map (fun inst => [inst.handles.get? 3, inst.handles.get? 1])) =
      (.resolved, [[⟨0⟩, ⟨2⟩]], [], some ⟨#[3, 0, 0, 0, 1, 0, 0, 0, 9]⟩,
        some [some (.waitable (.end_ ⟨0⟩)), some (.waitable (.end_ ⟨2⟩))]) := by
  dsimp only
  kernel_rfl

theorem alignment_trap_preserves_claims (exec : Mock.mock.Exec) :
    let result := run exec false 17
    (result.labels.any (fun label => match label with
      | .trap .unalignedPointer => true
      | _ => false), result.config.host.held, Mock.mock.memRead? result.config.store.core 0 16 9) =
      (true, [⟨0⟩, ⟨2⟩], some ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 9]⟩) := by
  dsimp only
  kernel_rfl

theorem publish_memory_header (exec : Mock.mock.Exec) :
    let result := run exec false 16 true
    (result.outcome, result.config.host.held,
      Mock.mock.memRead? result.config.store.core 0 0 8,
      Mock.mock.memRead? result.config.store.core 0 16 8) =
      (.resolved, [], some ⟨#[16, 0, 0, 0, 2, 0, 0, 0]⟩, some ⟨#[3, 0, 0, 0, 1, 0, 0, 0]⟩) := by
  dsimp only
  kernel_rfl

theorem allocator_effect_survives_refusal (exec : Mock.mock.Exec) :
    let result := run exec true
    (result.outcome, result.config.host.accepted.map rootIds, result.config.host.held,
      Mock.mock.memRead? result.config.store.core 0 16 9) =
      (.resolved, [[⟨0⟩, ⟨2⟩]], [⟨2⟩], some ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 9]⟩) := by
  dsimp only
  kernel_rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.ListLower.Examples
