module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Canon.Builtins.ErrorContext.Defs
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.Examples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value

def element : Async.Element := some (.prim .u8)
def recordType : TypeOf :=
  .record [("first", .future none), ("many", .list (.stream element)), ("word", .prim .u16),
    ("context", .errorContext)]
def nestedType : TypeOf :=
  .record [("first", .future none), ("inside", .record [("many", .list (.stream element)),
    ("word", .prim .u16)]), ("mark", .prim .u8), ("context", .errorContext)]

def exampleType (nested : Bool) : TypeOf := if nested then nestedType else recordType

def signature (nested : Bool) : Signature := ⟨Unit, fun _ => exampleType nested, fun _ => .fixed 0⟩

noncomputable def cx : LiftLowerContext Mock.mock :=
  { opts := { memory := some 0, realloc := some 0 }, inst := ⟨0⟩ }

def aliasType : TypeOf := .record [("direct", .future none), ("list", .list (.future none))]

def aliasPayload : Payload aliasType := ⟨.record [.future ⟨0⟩, .list [.future ⟨0⟩]], by decide⟩

def nestedAliasType : TypeOf :=
  .record [("direct", .future none), ("inside", .record [("list", .list (.future none))])]

def nestedAliasPayload : Payload nestedAliasType :=
  ⟨.record [.future ⟨0⟩, .record [.list [.future ⟨0⟩]]], by decide⟩

def contextType : TypeOf := .record [("first", .future none), ("context", .errorContext)]

def unsupportedList : TypeOf := .list (.map .u8 (.own ⟨0⟩))

def inactiveType : TypeOf := .record [("direct", .future none), ("maybe", .option unsupportedList)]

theorem inactive_field_rejected :
    preflight cx inactiveType ⟨.record [.future ⟨0⟩, .variant 0 none], by decide⟩ .flat =
      .error (.preflight (.schema .ownedResourceNeedsIdentity)) := by kernel_rfl

theorem missing_realloc_rejected :
    preflight { cx with opts := { cx.opts with realloc := none } } aliasType aliasPayload .flat =
      .error (.preflight (.abi .reallocRequired)) := by kernel_rfl

def nestedInactiveType : TypeOf :=
  .record [("first", .future none), ("inside", .record [("maybe", .option unsupportedList)])]

theorem nested_inactive_field_rejected :
    preflight cx nestedInactiveType
      ⟨.record [.future ⟨0⟩, .record [.variant 0 none]], by decide⟩ .flat =
        .error (.preflight (.schema .ownedResourceNeedsIdentity)) := by kernel_rfl

noncomputable def session (reenter memory : Bool) (nested : Bool := false) :
    P Mock.mock (State (signature nested)) (Ret Mock.mock) := do
  let limits := Component.Limits.spec
  let _ ← (Async.Call.create .future none).program limits Quirks.none
  let _ ← (Async.Call.create .stream element).program limits Quirks.none
  let [contextSlot] ← Builtins.errorContextNew limits Quirks.none cx.opts 0 0
    | internal "could not create the error context"
  let marker := if nested then [i32Flat 11] else []
  let input := [i32Flat 1, i32Flat 32, i32Flat 1, i32Flat 258] ++ marker ++ [contextSlot]
  let .ok (.tag label _ _) ← acceptNode (signature nested) limits Quirks.none cx () (.flat input) []
    | internal "could not lift the record"
  let .error (.preflight .unclaimed) ← lower limits Quirks.none cx aliasType aliasPayload (.memory 0)
    | internal "cross-field alias was not rejected before writing"
  let .error (.preflight .missingContext) ← lower limits Quirks.none cx contextType
      ⟨.record [.future ⟨0⟩, .errorContext ⟨1⟩], by decide⟩ (.memory 0)
    | internal "absent context was not rejected before writing"
  if nested then
    let .error (.preflight .unclaimed) ←
        lower limits Quirks.none cx nestedAliasType nestedAliasPayload (.memory 0)
      | internal "an outer claim aliased a nested claim"
  if memory then
    let reply ← lower limits Quirks.none cx (exampleType nested) label.2 (.memory 0)
    if reenter then
      let .error issue := reply | return ← internal "missing post-allocation field rejection"
      let expected : Issue := if nested then .nested 1 (.field 0 (.afterAllocation .unclaimed))
        else .field 1 (.afterAllocation .unclaimed)
      trapIf (issue != expected) (.internal "wrong field path for the post-allocation failure")
      pure .unit
    else
      let .ok () := reply | return ← internal "valid record was not stored"
      pure .unit
  else
    let .ok values ← lower limits Quirks.none cx (exampleType nested) label.2 .flat
      | internal "valid record was not flattened"
    let words : List FlatValue := values
    trapIf (words != [i32Flat 3, i32Flat 24, i32Flat 1, i32Flat 258] ++ marker ++ [i32Flat 6])
      (.internal "wrong canonical flat record")
    pure .unit

noncomputable def dispatch (reenter : Bool) (ptr : Nat) (nested : Bool) :
    Canon.Call Mock.mock → P Mock.mock (State (signature nested)) (Ret Mock.mock)
  | .reallocate _ 0 0 4 4 => do
    let marker ← loadInt cx 28 1 false
    trapIf (marker != 0) (.internal "unexpected second allocation")
    storeInt cx 9 28 1
    if reenter then
      let .ok 1 ← give Component.Limits.spec cx .stream element ⟨⟨2⟩⟩
        | internal "reentrant transfer failed"
    return .nat ptr
  | _ => internal "unexpected allocator call"

noncomputable def initial (reenter memory : Bool) (nested : Bool := false) :
    Machine.Config Mock.mock (State (signature nested)) where
  store := { CStore.empty with
    insts := [{}]
    core := { mems := [⟨.i32, ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0]⟩⟩] }
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := {}
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) (session reenter memory nested)]

def noReady {nested : Bool} : HostReady (State (signature nested)) := fun _ _ => false

noncomputable def run (exec : Mock.mock.Exec) (reenter memory : Bool) (ptr : Nat := 24)
    (nested : Bool := false) :=
  Machine.run noReady (dispatch reenter ptr nested) exec Machine.Oracle.first 320 (initial reenter memory nested)

theorem session_sound (exec : Mock.mock.Exec) (reenter memory : Bool) (ptr : Nat)
    (nested : Bool := false) :
    Machine.Steps .deterministic noReady (dispatch reenter ptr nested) (initial reenter memory nested)
      (run exec reenter memory ptr nested).labels (run exec reenter memory ptr nested).config :=
  Machine.run_sound noReady (dispatch reenter ptr nested) exec Machine.Oracle.first 320 (initial reenter memory nested)

theorem publish_memory (exec : Mock.mock.Exec) :
    let result := run exec false true
    (result.outcome, result.config.host.accepted.map rootIds, result.config.host.held,
      Mock.mock.memRead? result.config.store.core 0 0 29,
      (result.config.store.insts.get? 0).bind (fun inst => inst.handles.get? 6)) =
      (.resolved, [[⟨0⟩, ⟨2⟩]], [], some ⟨#[3, 0, 0, 0, 24, 0, 0, 0, 1, 0, 0, 0,
        2, 1, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 9]⟩, some (.errCtx ⟨0⟩)) := by
  dsimp only
  kernel_rfl

theorem publish_flat (exec : Mock.mock.Exec) :
    let result := run exec false false
    (result.outcome, result.config.host.held, Mock.mock.memRead? result.config.store.core 0 0 4) =
      (.resolved, [], some ⟨#[0, 0, 0, 0]⟩) := by
  dsimp only
  kernel_rfl

theorem reentry_preserves_earlier_field (exec : Mock.mock.Exec) :
    let result := run exec true true
    (result.outcome, result.config.host.held, Mock.mock.memRead? result.config.store.core 0 0 29,
      (result.config.store.insts.get? 0).map (fun inst => [inst.handles.get? 3, inst.handles.get? 1])) =
      (.resolved, [], some ⟨#[3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9]⟩,
        some [some (.waitable (.end_ ⟨0⟩)), some (.waitable (.end_ ⟨2⟩))]) := by
  dsimp only
  kernel_rfl

theorem allocation_trap_preserves_earlier_field (exec : Mock.mock.Exec) :
    let result := run exec false true 25
    (result.labels.any (fun label => match label with
      | .trap .unalignedPointer => true
      | _ => false), result.config.host.held, Mock.mock.memRead? result.config.store.core 0 0 29) =
      (true, [⟨2⟩], some ⟨#[3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9]⟩) := by
  dsimp only
  kernel_rfl

theorem nested_memory_respects_record_padding (exec : Mock.mock.Exec) :
    let result := run exec false true (nested := true)
    (result.outcome, result.config.host.accepted.map rootIds, result.config.host.held,
      Mock.mock.memRead? result.config.store.core 0 0 29) =
      (.resolved, [[⟨0⟩, ⟨2⟩]], [], some ⟨#[3, 0, 0, 0, 24, 0, 0, 0, 1, 0, 0, 0,
        2, 1, 0, 0, 11, 0, 0, 0, 6, 0, 0, 0, 1, 0, 0, 0, 9]⟩) := by
  dsimp only
  kernel_rfl

theorem nested_flat_same_operand_order (exec : Mock.mock.Exec) :
    let result := run exec false false (nested := true)
    (result.outcome, result.config.host.held) = (.resolved, []) := by
  dsimp only
  kernel_rfl

theorem nested_reentry_preserves_completed_prefix (exec : Mock.mock.Exec) :
    let result := run exec true true (nested := true)
    (result.outcome, result.config.host.held, Mock.mock.memRead? result.config.store.core 0 0 29) =
      (.resolved, [], some ⟨#[3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9]⟩) := by
  dsimp only
  kernel_rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.Examples
