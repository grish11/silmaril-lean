module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Effects.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Transfer.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.CheckedCanonicalEffects

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open RecordLower (Field)

variable {E : CoreEngine} {World : Type} {sig : Signature}
variable (access : Access E World sig) (limits : Component.Limits) (quirks : Quirks)
  (cx : LiftLowerContext E) (width : AddrType)

mutual
theorem field (item : Field) (index : Nat) (output : Lower.Output) :
    RecordLower.Internal.runField limits quirks cx (authority access limits cx) width item index output =
      Effects.field access limits quirks cx width item index output := by
  cases item with
  | data type payload => rfl
  | owner receipt =>
    rw [runField_owner_canon, Effects.field]
    cases output <;> simp [Effects.checkedLeaf, Effects.transfer, Effects.canonical, Field.value, Field.type,
      Prog.bind_eq, Prog.bind_assoc]
    all_goals
      congr 1
      funext state
      cases prepareOwner state receipt <;> simp only [Prog.bind_assoc, Prog.pure_bind']
  | endpoint channel element id =>
    rw [runField_endpoint_canon, Effects.field]
    cases output <;> cases channel <;>
      simp [Effects.checkedLeaf, Effects.transfer, Effects.canonical, Field.value, Field.type, Lower.Output.Result,
        Prog.bind_eq, Prog.bind_assoc]
    all_goals
      congr 1
      funext state
      congr 1
      funext store
      split <;> rename_i result verdict <;> simp only [verdict, Prog.bind_assoc, Prog.pure_bind']
  | context id =>
    rw [runField_context_canon, Effects.field]
    cases output <;> simp [Effects.checkedLeaf, Effects.transfer, Effects.canonical, Field.value, Field.type,
      Prog.bind_eq, Prog.bind_assoc]
    all_goals
      congr 1
      funext state
      congr 1
      funext store
      split <;> rfl
  | aggregate type children =>
    cases output <;> simp only [RecordLower.Internal.runField, Effects.field, flat, memory]
  | fixed element length entries =>
    cases output <;> simp only [RecordLower.Internal.runField, Effects.field, flat, elements]
  | dynamic type element entries =>
    simp only [RecordLower.Internal.runField, Effects.field, ListLower.allocateRange, elements]
    rfl
  | sum type arms tag selected =>
    cases selected with
    | none => cases output <;> simp only [RecordLower.Internal.runField, Effects.field]
    | some child =>
      cases output with
      | memory ptr => simp only [RecordLower.Internal.runField, Effects.field, field]
      | flat => simp only [RecordLower.Internal.runField, Effects.field, field]; rfl
termination_by structural item

theorem memory (fields : List Field) (cursor index : Nat) :
    RecordLower.Internal.runMemory limits quirks cx (authority access limits cx) width fields cursor index =
      Effects.memory access limits quirks cx width fields cursor index := by
  cases fields with
  | nil => rfl
  | cons child rest => simp only [RecordLower.Internal.runMemory, Effects.memory, field, memory]; rfl
termination_by structural fields

theorem elements (fields : List Field) (stride ptr index : Nat) :
    RecordLower.Internal.runElements limits quirks cx (authority access limits cx) width fields stride ptr index =
      Effects.elements access limits quirks cx width fields stride ptr index := by
  cases fields with
  | nil => rfl
  | cons child rest => simp only [RecordLower.Internal.runElements, Effects.elements, field, elements]; rfl
termination_by structural fields

theorem flat (fields : List Field) (index : Nat) :
    RecordLower.Internal.runFlat limits quirks cx (authority access limits cx) width fields index =
      Effects.flat access limits quirks cx width fields index := by
  cases fields with
  | nil => rfl
  | cons child rest => simp only [RecordLower.Internal.runFlat, Effects.flat, field, flat]; rfl
termination_by structural fields
end

theorem root (type : TypeOf) (item : Field) (output : Lower.Output) :
    RecordLower.Internal.emitValue limits quirks cx (authority access limits cx) width type item output =
      Effects.root access limits quirks cx width type item output := by
  cases output <;> simp only [RecordLower.Internal.emitValue, Effects.root, field]

theorem lowerValue (type : TypeOf) (payload : OwnedMemory.Payload type) (output : Lower.Output) :
    Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.lowerValue
      access limits quirks cx type payload output =
      RecordLower.Internal.lowerWithPlan quirks cx (authority access limits cx) type payload.val.value
        (preflightValue cx type payload output) Field.objects
        (fun width item => Effects.root access limits quirks cx width type item output) := by
  unfold Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.lowerValue
  simp only [root]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.CheckedCanonicalEffects
