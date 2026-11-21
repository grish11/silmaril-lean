module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.ReferenceTable.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Defs
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.ReferenceTable.Examples

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.Accept Silmaril.Wasm.Execution.Core

noncomputable section

private def resource : RtId := ⟨3⟩
private def context : LiftLowerContext Mock.mock := { opts := {}, inst := ⟨0⟩ }

private def store : CStore Mock.mock := { CStore.empty with
  insts := [({} : InstState).addHandle (.resource ⟨0⟩) |>.addHandle (.resource ⟨1⟩)]
  resHandles := List.replicate 2 { rt := resource, rep := 77, own := true } }

private def table : RT := snapshot store context.inst

private def sig : WitSig :=
  ⟨Unit, fun _ => [.record [("first", .option (.own 3)), ("rest", .list (.own 3))]], fun _ => .fixed 0⟩

private def input (second : UInt32) : Op (Nested.rawSignature sig) :=
  ⟨(), ((some (1 : UInt32), ([second], ())), ())⟩

private def removed (reference : CStore Mock.mock) (slot : Nat) : CStore Mock.mock :=
  ArenaField.insts.modify reference context.inst (InstState.removeHandle slot)

theorem nested_owner_commit :
    Commit Limits.spec context store [1, 2]
      [⟨resource, ⟨⟨0⟩, 77⟩⟩, ⟨resource, ⟨⟨1⟩, 77⟩⟩] (removed (removed store 1) 2) := by
  refine .cons (updated := removed store 1) ?_ ?_ (.cons ?_ ?_ (.nil _)) <;> kernel_rfl

theorem recursive_reservations_keep_the_two_slots :
    (Nested.reserveOp sig table (input 2)).map (·.2.val) = .ok [2, 1] := by
  kernel_rfl

theorem duplicate_rejected_before_commit :
    Nested.reserveOp sig table (input 1) = .error (.resource .duplicate) := by
  kernel_rfl

theorem eager_duplicate_keeps_the_first_removal :
    Stored.Endpoints.Core.runLocal (Resources.take Limits.spec context resource 1) (removed store 1) =
      (removed store 1, .error (.trapped (.unknownHandle 1))) := by
  kernel_rfl

theorem eager_nested_resolution_produces_typed_values_and_receipts :
    (Nested.resolveTypesWith (takeIndex Limits.spec context) (sig.params ()) (input 2).2).run.run ⟨store, []⟩ =
      (.ok ((some (77 : Nat), ([(77 : Nat)], ())), ()),
        ⟨removed (removed store 1) 2, [(2, ⟨resource, ⟨⟨1⟩, 77⟩⟩), (1, ⟨resource, ⟨⟨0⟩, 77⟩⟩)]⟩) := by
  kernel_rfl

private def textRecord : PTy :=
  .record [("first", .option (.own 3)), ("rest", .list (.own 3)), ("text", .string)]

private def textSig : WitSig := ⟨Unit, fun _ => [textRecord], fun _ => .fixed 0⟩

private def textBytes (low high : UInt8) : ByteArray :=
  ⟨#[1, 0, 0, 0, 1, 0, 0, 0, 24, 0, 0, 0, 1, 0, 0, 0,
    28, 0, 0, 0, 1, 0, 0, 128, 2, 0, 0, 0, low, high]⟩

private def checkedText (bytes : ByteArray) :=
  Nested.checkedNode textSig (fun _ => some ()) { encoding := .latin1Utf16 } table
    (⟨("wit", "node"), [.i32 0, .i32 0, .i32 0, .i32 0], some bytes⟩ : Callout)

private def referenceText (bytes : ByteArray) :=
  let initial : CStore Mock.mock := { store with core := { mems := [⟨.i32, bytes⟩] } }
  let cx := { context with opts := { memory := some 0, encoding := .latin1Utf16 } }
  Stored.Endpoints.Core.runLocal (Stored.OwnedMemory.lift Limits.spec Quirks.none cx
    (.record [("first", .option (.own resource)), ("rest", .list (.own resource)), ("text", .prim .string)])
    (.memory 0)) initial

private def referenceObservation (bytes : ByteArray) : Option (String × List (HandleObjId × Nat)) := do
  let .ok (.ok payload) := (referenceText bytes).2 | none
  let .record [.variant 1 (some (.own 77)), .list [.own 77], .string text] := payload.val.value | none
  return (text.v.str, payload.val.owners.map fun receipt => (receipt.2.identity, receipt.2.representation))

theorem compact_text_keeps_both_nested_owners :
    (checkedText (textBytes 233 0)).map (fun result => (result.1.1.2, result.1.2)) =
      .ok (((some (77 : Nat), ([(77 : Nat)], ("é", ()))), ()), []) ∧
    referenceObservation (textBytes 233 0) = some ("é", [(⟨0⟩, 77), (⟨1⟩, 77)]) := by
  constructor <;> kernel_rfl

private def trapObservation (bytes : ByteArray) :=
  let (final, outcome) := referenceText bytes
  (outcome.map (fun _ => ()), (final.inst? context.inst).map fun (inst : InstState) =>
    (inst.handles.get? 1, inst.handles.get? 2))

theorem invalid_compact_text_separates_rejection_from_eager_trap :
    checkedText (textBytes 0 216) = .error .badPayload ∧
    trapObservation (textBytes 0 216) = (.error (.trapped .invalidUtf16), some (none, none)) := by
  constructor <;> kernel_rfl

end

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.ReferenceTable.Examples
