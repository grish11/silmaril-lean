module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Defs
import Silmaril.Wasm.Component.Reference.Canon.Flat.Thms
import Silmaril.Wasm.Component.Reference.Canon.Store.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordStoreInv

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open RecordLower (Authority Field Object)
open RecordLower.Internal (runField runMemory runElements runFlat emitValue publishSlot lowerWithPlan)

variable {E : CoreEngine} {World : Type} {I : CStore E → Prop}

private theorem data_inv (preserves : P.Inv.StorePres I) (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (type : TypeOf) (payload : Payload type) (output : Lower.Output) :
    P.Inv I (Lower.lower limits quirks cx type payload output : P E World _) := by
  unfold Lower.lower
  split
  · exact P.Inv.pure _
  · refine P.Inv.bind (P.Inv.ptrType _) fun width => P.Inv.ite (P.Inv.pure _) ?_
    refine P.Inv.bind ?_ fun _ => P.Inv.pure _
    cases output with
    | flat => exact P.Inv.lowerFlatAt preserves _ _ _ _ _ _
    | memory => exact P.Inv.bind (P.Inv.checkAligned _ _) fun _ =>
        P.Inv.bind (P.Inv.checkInBounds _ _ _) fun _ => P.Inv.store preserves _ _ _ _ _ _

private theorem slot_inv (preserves : P.Inv.StorePres I) (cx : LiftLowerContext E) (slot : Nat)
    (output : Lower.Output) : P.Inv I (publishSlot cx slot output : P E World _) := by
  cases output with
  | flat => exact P.Inv.pure _
  | memory ptr => exact P.Inv.storeInt cx slot ptr 4 false (preserves.write · _ _)

private theorem descriptor_inv (preserves : P.Inv.StorePres I) (cx : LiftLowerContext E)
    (width : AddrType) (ptr count : Nat) (output : Lower.Output) :
    P.Inv I (ListLower.publish cx width ptr count output : P E World _) := by
  cases output with
  | flat => exact P.Inv.pure _
  | memory dest => exact P.Inv.storeListDescriptor cx ptr count dest preserves.write

section

variable (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
  (authority : Authority E World) (width : AddrType) (preserves : P.Inv.StorePres I)
  (prepare : ∀ plan, P.Inv I (authority.prepare plan))
  (transfer : ∀ index object, P.Inv I (authority.transfer index object))

include preserves transfer in
private theorem transfer_inv (index : Nat) (object : Object) (output : Lower.Output) :
    P.Inv I (show P E World (Except RecordLower.Issue output.Result) from do
      match ← authority.transfer index object with
      | .error issue => return .error issue
      | .ok slot => return .ok (← publishSlot cx slot output)) := by
  refine P.Inv.bind (transfer _ _) fun result => ?_
  cases result with
  | error => exact P.Inv.pure _
  | ok slot => exact P.Inv.bind (slot_inv preserves cx slot output) fun _ => P.Inv.pure _

private structure Rules (authority : Authority E World) (I : CStore E → Prop) : Prop where
  preserves : P.Inv.StorePres I
  prepare : ∀ plan, P.Inv I (authority.prepare plan)
  transfer : ∀ index object, P.Inv I (authority.transfer index object)

mutual
private theorem lower_field_inv (rules : Rules authority I) :
    (field : Field) → (index : Nat) → (output : Lower.Output) →
    P.Inv I (runField limits quirks cx authority width field index output)
  | .data _ _, _, _ => by
    rw [runField]
    exact P.Inv.bind (data_inv rules.preserves _ _ _ _ _ _) fun _ => P.Inv.pure _
  | .endpoint _ _ _, _, _ | .context _, _, _ | .owner _, _, _ => by
    rw [runField]
    exact transfer_inv cx authority rules.preserves rules.transfer _ _ _
  | .aggregate _ fields, _, .flat => by
    rw [runField]
    exact P.Inv.bind (flat_inv rules fields 0) fun _ => P.Inv.pure _
  | .aggregate _ fields, _, .memory ptr => by
    rw [runField]
    exact P.Inv.bind (P.Inv.checkInBounds _ _ _) fun _ =>
      P.Inv.bind (memory_inv rules fields ptr 0) fun _ => P.Inv.pure _
  | .fixed _ _ entries, _, .flat => by
    rw [runField]
    exact P.Inv.bind (flat_inv rules entries 0) fun _ => P.Inv.pure _
  | .fixed element _ entries, _, .memory ptr => by
    rw [runField]
    exact P.Inv.bind (elements_inv rules entries (layout width element).size ptr 0) fun _ => P.Inv.pure _
  | .dynamic _ element entries, _, _ => by
    rw [runField]
    refine P.Inv.bind (rules.prepare _) fun before => ?_
    split
    · exact P.Inv.pure _
    · exact P.Inv.pure _
    · refine P.Inv.bind (P.Inv.allocateListRange _ _ _) fun ptr => ?_
      refine P.Inv.bind (rules.prepare _) fun after => ?_
      split
      · exact P.Inv.pure _
      · exact P.Inv.pure _
      · refine P.Inv.bind (elements_inv rules entries (layout width element).size ptr 0) fun result => ?_
        cases result with
        | error => exact P.Inv.pure _
        | ok => exact P.Inv.bind (descriptor_inv rules.preserves _ _ _ _ _) fun _ => P.Inv.pure _
  | .sum _ _ _ none, _, .flat => by
    rw [runField]
    exact P.Inv.bind (P.Inv.lowerFlatVariantWith _ _ _ _ (P.Inv.pure _)) fun _ => P.Inv.pure _
  | .sum _ _ _ (some payload), _, .flat => by
    rw [runField]
    refine P.Inv.bind (lower_field_inv rules payload 0 .flat) fun result => ?_
    cases result with
    | error => exact P.Inv.pure _
    | ok => exact P.Inv.bind (P.Inv.lowerFlatVariantWith _ _ _ _ (P.Inv.pure _)) fun _ => P.Inv.pure _
  | .sum _ _ _ none, _, .memory _ => by
    rw [runField]
    exact P.Inv.bind (P.Inv.storeVariantHead _ _ _ _ _ rules.preserves.write) fun _ => P.Inv.pure _
  | .sum _ _ _ (some payload), _, .memory _ => by
    rw [runField]
    exact P.Inv.bind (P.Inv.storeVariantHead _ _ _ _ _ rules.preserves.write) fun ptr =>
      P.Inv.bind (lower_field_inv rules payload 0 (.memory ptr)) fun _ => P.Inv.pure _
termination_by structural field => field

private theorem memory_inv (rules : Rules authority I) : (fields : List Field) → (ptr index : Nat) →
    P.Inv I (runMemory limits quirks cx authority width fields ptr index)
  | [], _, _ => P.Inv.pure _
  | field :: rest, cursor, index => by
    rw [runMemory]
    let area := layout width field.type
    let ptr := alignTo cursor area.alignment
    refine P.Inv.bind (lower_field_inv rules field index (.memory ptr)) fun result => ?_
    cases result with
    | error => exact P.Inv.pure _
    | ok => exact memory_inv rules rest (ptr + area.size) (index + 1)
termination_by structural fields => fields

private theorem elements_inv (rules : Rules authority I) : (fields : List Field) → (stride ptr index : Nat) →
    P.Inv I (runElements limits quirks cx authority width fields stride ptr index)
  | [], _, _, _ => P.Inv.pure _
  | field :: rest, stride, ptr, index => by
    rw [runElements]
    refine P.Inv.bind (lower_field_inv rules field index (.memory ptr)) fun result => ?_
    cases result with
    | error => exact P.Inv.pure _
    | ok => exact elements_inv rules rest stride (ptr + stride) (index + 1)
termination_by structural fields => fields

private theorem flat_inv (rules : Rules authority I) : (fields : List Field) → (index : Nat) →
    P.Inv I (runFlat limits quirks cx authority width fields index)
  | [], _ => P.Inv.pure _
  | field :: rest, index => by
    rw [runFlat]
    refine P.Inv.bind (lower_field_inv rules field index .flat) fun result => ?_
    cases result with
    | error => exact P.Inv.pure _
    | ok => exact P.Inv.bind (flat_inv rules rest (index + 1)) fun _ => P.Inv.pure _
termination_by structural fields => fields
end

include preserves prepare transfer

theorem field_inv (field : Field) (index : Nat) (output : Lower.Output) :
    P.Inv I (runField limits quirks cx authority width field index output) :=
  lower_field_inv limits quirks cx authority width ⟨preserves, prepare, transfer⟩ field index output

theorem compiled_value_inv (type : TypeOf) (value : Val) (output : Lower.Output)
    (compiled : Except RecordLower.Issue (Field × List Object)) :
    P.Inv I (lowerWithPlan quirks cx authority type value compiled Field.objects fun reached field =>
      emitValue limits quirks cx authority reached type field output) := by
  unfold lowerWithPlan
  cases compiled with
  | error => exact P.Inv.pure _
  | ok compiled =>
    refine P.Inv.bind (prepare _) fun result => ?_
    cases result with
    | error => exact P.Inv.pure _
    | ok =>
      refine P.Inv.bind (P.Inv.ptrType _) fun reached => ?_
      refine P.Inv.ite (P.Inv.pure _) ?_
      cases output with
      | flat => exact field_inv limits quirks cx authority reached preserves prepare transfer _ _ _
      | memory ptr =>
        exact P.Inv.bind (P.Inv.checkAligned _ _) fun _ =>
          P.Inv.bind (P.Inv.checkInBounds _ _ _) fun _ =>
            field_inv limits quirks cx authority reached preserves prepare transfer _ _ _

end

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordStoreInv
