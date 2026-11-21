module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.OptionExamples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime

private def element : Async.Element := some (.prim .u8)
private def optionalList : TypeOf := .option (.list (.stream element))
private def recordType : TypeOf := .record [("optional", optionalList), ("mark", .prim .u8)]
private def aliasType : TypeOf := .record [("direct", .stream element), ("optional", optionalList)]
private def signature : Signature := ⟨Unit, fun _ => recordType, fun _ => .fixed 0⟩
private abbrev World := State signature

private noncomputable def context : LiftLowerContext Mock.mock :=
  { opts := { memory := some 0, realloc := some 0 }, inst := ⟨0⟩ }

theorem empty_option_checks_allocation_capability :
    preflight { context with opts := { context.opts with realloc := none } } recordType
      ⟨.record [.variant 0 none, .int .u8 42], by decide⟩ .flat =
      .error (.preflight (.abi .reallocRequired)) := by kernel_rfl

private noncomputable def session (present memory : Bool) : P Mock.mock World (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let _ ← (Async.Call.create .stream element).program limits Quirks.none
  let input := if present then [i32Flat 1, i32Flat 32, i32Flat 1, i32Flat 42]
    else [i32Flat 0, i32Flat 0, i32Flat 0, i32Flat 42]
  let .ok (.tag label _ _) ← acceptNode signature limits Quirks.none context () (.flat input) []
    | internal "could not lift the optional endpoint list"
  if present then
    let .error (.preflight .unclaimed) ← lower limits Quirks.none context aliasType
        ⟨.record [.stream ⟨0⟩, .variant 1 (some (.list [.stream ⟨0⟩]))], by decide⟩ (.memory 0)
      | internal "an endpoint aliased a claim inside an option"
  if memory then
    let .ok () ← lower limits Quirks.none context recordType label.2 (.memory 0)
      | internal "could not store the optional endpoint list"
    pure .unit
  else
    let .ok words ← lower limits Quirks.none context recordType label.2 .flat
      | internal "could not flatten the optional endpoint list"
    let expected := if present then [i32Flat 1, i32Flat 24, i32Flat 1, i32Flat 42]
      else [i32Flat 0, i32Flat 0, i32Flat 0, i32Flat 42]
    let actual : List FlatValue := words
    trapIf (actual != expected) (.internal "wrong canonical flat option")
    pure .unit

private noncomputable def initial (present memory : Bool) : Machine.Config Mock.mock World where
  store := { CStore.empty with
    core := { mems := [⟨.i32, ⟨Array.replicate 32 0 ++ #[1, 0, 0, 0]⟩⟩] }
    insts := [{}]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := {}
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) (session present memory)]

private noncomputable def dispatch (destination : Nat) :
    Canon.Call Mock.mock → P Mock.mock World (Ret Mock.mock)
  | .reallocate _ 0 0 4 4 => do
    storeInt context 9 28 1
    return .nat destination
  | _ => internal "unexpected allocator call"

private def noReady : HostReady World := fun _ _ => false

private noncomputable def run (exec : Mock.mock.Exec) (present memory : Bool) (destination : Nat := 24) :=
  Machine.run noReady (dispatch destination) exec Machine.Oracle.first 260 (initial present memory)

theorem option_session_sound (exec : Mock.mock.Exec) (present memory : Bool) (destination : Nat) :
    Machine.Steps .deterministic noReady (dispatch destination) (initial present memory)
      (run exec present memory destination).labels (run exec present memory destination).config :=
  Machine.run_sound noReady (dispatch destination) exec Machine.Oracle.first 260 (initial present memory)

theorem optional_list_flat (exec : Mock.mock.Exec) (present : Bool) :
    let result := run exec present false
    (result.outcome, result.config.host.held) = (.resolved, []) := by
  cases present <;> dsimp only <;> kernel_rfl

theorem optional_list_memory (exec : Mock.mock.Exec) (present : Bool) :
    let result := run exec present true
    let bytes := (result.config.store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
    (result.outcome, result.config.host.held, (bytes.extract 0 13).data, bytes[28]?) =
      (.resolved, [], (if present then #[1, 0, 0, 0, 24, 0, 0, 0, 1, 0, 0, 0, 42]
        else #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42]), some (if present then 9 else 0)) := by
  cases present <;> dsimp only <;> kernel_rfl

theorem option_allocator_trap_keeps_tag_and_unmoved_claim (exec : Mock.mock.Exec) :
    let result := run exec true true 25
    let bytes := (result.config.store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
    (result.labels.any (· matches .trap .unalignedPointer), result.config.host.held, bytes[0]?, bytes[28]?) =
      (true, [⟨0⟩], some 1, some 9) := by
  dsimp only
  kernel_rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.OptionExamples
