module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Defs
public import Silmaril.Wasm.Component.Reference.HostWrite.Defs
import Silmaril.Wasm.Component.Reference.HostWrite.Thms
import Silmaril.Wasm.Component.Reference.Canon.Flat.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordEffects

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Reference
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (TypeOf)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open RecordLower (Authority Field Object)
open RecordLower.Internal (runField runMemory runElements runFlat emitRecord emitValue publishSlot
  lowerCompiled lowerWithPlan)

variable {E : CoreEngine} {World : Type} {Write : World → World → Prop}

private abbrev Safe {Result : Type} (program : P E World Result) := HostSafe Write none program

private theorem unchanged {Result : Type} {program : P E World Result}
    (safe : P.InvW (fun _ => True) (fun _ => False) program) : Safe (Write := Write) program :=
  HostWrite.hostSafe_of_invW safe _

private theorem plainPres : P.Inv.StorePres (E := E) (fun _ => True) :=
  ⟨fun _ _ _ _ _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ => trivial,
    fun _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩

private theorem data_safe (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (type : TypeOf) (payload : Stored.Payload type) (output : Stored.Lower.Output) :
    P.InvW (fun _ => True) (fun _ => False) (Stored.Lower.lower limits quirks cx type payload output : P E World _) := by
  unfold Stored.Lower.lower
  split
  · exact P.Inv.pure _
  · refine P.Inv.bind (P.Inv.ptrType _) fun width => P.Inv.ite (P.Inv.pure _) ?_
    refine P.Inv.bind ?_ fun _ => P.Inv.pure _
    cases output with
    | flat => exact P.Inv.lowerFlatAt plainPres _ _ _ _ _ _
    | memory =>
      exact P.Inv.bind (P.Inv.checkAligned _ _) fun _ =>
        P.Inv.bind (P.Inv.checkInBounds _ _ _) fun _ => P.Inv.store plainPres _ _ _ _ _ _

private theorem publish_slot_safe (cx : LiftLowerContext E) (slot : Nat) (output : Stored.Lower.Output) :
    Safe (Write := Write) (publishSlot cx slot output : P E World _) := by
  cases output with
  | flat => exact .pure none _
  | memory ptr => exact unchanged (P.Inv.storeInt cx slot ptr 4 false (fun _ _ _ => True.intro))

private theorem list_publish_safe (cx : LiftLowerContext E) (width : AddrType) (ptr count : Nat)
    (output : Stored.Lower.Output) :
    Safe (Write := Write) (ListLower.publish cx width ptr count output : P E World _) := by
  cases output with
  | flat => exact .pure none _
  | memory dest =>
    exact unchanged (P.Inv.bind (P.Inv.ptrSize _) fun size =>
      P.Inv.bind (P.Inv.storeInt cx ptr dest size false (fun _ _ _ => True.intro)) fun _ =>
        P.Inv.storeInt cx count (dest + size) size false (fun _ _ _ => True.intro))

private theorem allocation_safe (cx : LiftLowerContext E) (area : Layout) (count : Nat) :
    Safe (Write := Write) (ListLower.allocateRange cx area count : P E World Nat) :=
  unchanged (P.Inv.bind (P.Inv.allocate _ _ _) fun _ =>
    P.Inv.bind (P.Inv.trapIf _ _) fun _ => P.Inv.bind (P.Inv.checkInBounds _ _ _) fun _ => P.Inv.pure _)

private theorem transfer_safe (cx : LiftLowerContext E) (authority : Authority E World)
    (transfer : ∀ index object, Safe (Write := Write) (authority.transfer index object))
    (index : Nat) (object : Object) (output : Stored.Lower.Output) :
    Safe (Write := Write) (show P E World (Except RecordLower.Issue output.Result) from do
      match ← authority.transfer index object with
      | .error issue => return .error issue
      | .ok slot => return .ok (← publishSlot cx slot output)) := by
  refine HostWrite.bind (transfer _ _) fun result => ?_
  cases result with
  | ok slot => exact HostWrite.bind (publish_slot_safe _ slot _) fun _ => .pure none _
  | error => exact .pure none _

section

variable (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E) (authority : Authority E World)
  (width : AddrType)

private structure AuthoritySafe (authority : Authority E World) (write : World → World → Prop) : Prop where
  prepare : ∀ plan, HostSafe write none (authority.prepare plan)
  transfer : ∀ index object, HostSafe write none (authority.transfer index object)

mutual
private theorem field_safe (rules : AuthoritySafe authority Write) :
    (field : Field) → (index : Nat) → (output : Stored.Lower.Output) →
    Safe (Write := Write) (runField limits quirks cx authority width field index output)
  | .data type payload, _, output => by
    rw [runField]
    exact HostWrite.bind (unchanged (data_safe _ _ _ _ _ _)) fun _ => .pure none _
  | .endpoint channel element id, index, output => by
    rw [runField]
    exact transfer_safe cx authority rules.transfer index (.shared (.endpoint channel element id)) output
  | .context id, index, output => by
    rw [runField]
    exact transfer_safe cx authority rules.transfer index (.shared (.errorContext id)) output
  | .owner receipt, index, output => by
    rw [runField]
    exact transfer_safe cx authority rules.transfer index (.owner receipt) output
  | .aggregate _ fields, _, .flat => by
    rw [runField]
    exact HostWrite.bind (flat_safe rules fields 0) fun _ => .pure none _
  | .aggregate _ fields, _, .memory ptr => by
    rw [runField]
    exact HostWrite.bind (unchanged (P.Inv.checkInBounds _ _ _)) fun _ =>
      HostWrite.bind (memory_safe rules fields ptr 0) fun _ => .pure none _
  | .fixed _ _ entries, _, .flat => by
    rw [runField]
    exact HostWrite.bind (flat_safe rules entries 0) fun _ => .pure none _
  | .fixed element _ entries, _, .memory ptr => by
    rw [runField]
    exact HostWrite.bind (elements_safe rules entries (layout width element).size ptr 0) fun _ => .pure none _
  | .dynamic _ element entries, _, output => by
    rw [runField]
    let plan := Field.listObjects entries
    refine HostWrite.bind (rules.prepare plan) fun before => ?_
    split
    · exact .pure none _
    · exact .pure none _
    · refine HostWrite.bind (allocation_safe _ _ _) fun ptr => ?_
      refine HostWrite.bind (rules.prepare plan) fun after => ?_
      split
      · exact .pure none _
      · exact .pure none _
      · refine HostWrite.bind (elements_safe rules entries (layout width element).size ptr 0) fun result => ?_
        cases result with
        | ok => exact HostWrite.bind (list_publish_safe _ _ _ _ _) fun _ => .pure none _
        | error => exact .pure none _
  | .sum _ _ _ none, _, .flat => by
    rw [runField]
    exact HostWrite.bind (unchanged (P.Inv.lowerFlatVariantWith _ _ _ _ (P.Inv.pure _))) fun _ => .pure none _
  | .sum _ _ _ (some payload), _, .flat => by
    rw [runField]
    refine HostWrite.bind (field_safe rules payload 0 .flat) fun result => ?_
    cases result with
    | ok => exact HostWrite.bind (unchanged (P.Inv.lowerFlatVariantWith _ _ _ _ (P.Inv.pure _))) fun _ => .pure none _
    | error => exact .pure none _
  | .sum _ _ _ none, _, .memory _ => by
    rw [runField]
    exact HostWrite.bind (unchanged (P.Inv.storeVariantHead _ _ _ _ _ plainPres.write)) fun _ => .pure none _
  | .sum _ _ _ (some payload), _, .memory _ => by
    rw [runField]
    exact HostWrite.bind (unchanged (P.Inv.storeVariantHead _ _ _ _ _ plainPres.write)) fun ptr =>
      HostWrite.bind (field_safe rules payload 0 (.memory ptr)) fun _ => .pure none _
termination_by structural field => field

private theorem memory_safe (rules : AuthoritySafe authority Write) : (fields : List Field) → (ptr index : Nat) →
    Safe (Write := Write) (runMemory limits quirks cx authority width fields ptr index)
  | [], _, _ => .pure none _
  | field :: rest, cursor, index => by
    rw [runMemory]
    let area := layout width field.type
    let ptr := alignTo cursor area.alignment
    refine HostWrite.bind (field_safe rules field index (.memory ptr)) fun result => ?_
    cases result with
    | ok => exact memory_safe rules rest (ptr + area.size) (index + 1)
    | error => exact .pure none _
termination_by structural fields => fields

private theorem elements_safe (rules : AuthoritySafe authority Write) :
    (fields : List Field) → (stride ptr index : Nat) →
    Safe (Write := Write) (runElements limits quirks cx authority width fields stride ptr index)
  | [], _, _, _ => .pure none _
  | field :: rest, stride, ptr, index => by
    rw [runElements]
    refine HostWrite.bind (field_safe rules field index (.memory ptr)) fun result => ?_
    cases result with
    | ok => exact elements_safe rules rest stride (ptr + stride) (index + 1)
    | error => exact .pure none _
termination_by structural fields => fields

private theorem flat_safe (rules : AuthoritySafe authority Write) : (fields : List Field) → (index : Nat) →
    Safe (Write := Write) (runFlat limits quirks cx authority width fields index)
  | [], _ => .pure none _
  | field :: rest, index => by
    rw [runFlat]
    refine HostWrite.bind (field_safe rules field index .flat) fun result => ?_
    cases result with
    | ok => exact HostWrite.bind (flat_safe rules rest (index + 1)) fun _ => .pure none _
    | error => exact .pure none _
termination_by structural fields => fields
end

private theorem emit_safe (rules : AuthoritySafe authority Write) (type : TypeOf) (fields : List Field)
    (output : Stored.Lower.Output) :
    Safe (Write := Write) (emitRecord limits quirks cx authority width type fields output) := by
  cases output with
  | flat => exact flat_safe limits quirks cx authority width rules fields 0
  | memory ptr => exact HostWrite.bind (unchanged (P.Inv.checkAligned _ _)) fun _ =>
      HostWrite.bind (unchanged (P.Inv.checkInBounds _ _ _)) fun _ =>
        memory_safe limits quirks cx authority width rules fields _ 0

private theorem plan_safe {Shape Result : Type} (type : TypeOf) (value : Value.Val)
    (compiled : Except RecordLower.Issue (Shape × List Object))
    (objects : Shape → List Object)
    (emit : AddrType → Shape → P E World (Except RecordLower.Issue Result))
    (prepare : ∀ plan, HostSafe Write none (authority.prepare plan))
    (safe : ∀ width shape, HostSafe Write none (emit width shape)) :
    HostSafe Write none (lowerWithPlan quirks cx authority type value compiled objects emit) := by
  cases compiled with
  | error issue => exact .pure none _
  | ok compiled =>
    obtain ⟨shape, _⟩ := compiled
    refine HostWrite.bind (prepare (objects shape)) fun result => ?_
    cases result with
    | error issue => exact .pure none _
    | ok _ =>
      refine HostWrite.bind (unchanged (P.Inv.ptrType _)) fun width => ?_
      split
      · exact .pure none _
      · exact safe width shape

theorem compiled_safe (type : TypeOf) (value : Value.Val) (output : Stored.Lower.Output)
    (compiled : Except RecordLower.Issue (List Field × List Object))
    (prepare : ∀ plan, HostSafe Write none (authority.prepare plan))
    (transfer : ∀ index object, HostSafe Write none (authority.transfer index object)) :
    HostSafe Write none (lowerCompiled limits quirks cx authority type value output compiled) :=
  plan_safe quirks cx authority type value compiled Field.listObjects _ prepare fun width fields =>
    emit_safe limits quirks cx authority width ⟨prepare, transfer⟩ type fields output

theorem compiled_value_safe (type : TypeOf) (value : Value.Val) (output : Stored.Lower.Output)
    (compiled : Except RecordLower.Issue (Field × List Object))
    (prepare : ∀ plan, HostSafe Write none (authority.prepare plan))
    (transfer : ∀ index object, HostSafe Write none (authority.transfer index object)) :
    HostSafe Write none (lowerWithPlan quirks cx authority type value compiled Field.objects fun width field =>
      emitValue limits quirks cx authority width type field output) := by
  refine plan_safe quirks cx authority type value compiled Field.objects _ prepare fun width field => ?_
  cases output with
  | flat => exact field_safe limits quirks cx authority width ⟨prepare, transfer⟩ field 0 .flat
  | memory ptr => exact HostWrite.bind (unchanged (P.Inv.checkAligned _ _)) fun _ =>
      HostWrite.bind (unchanged (P.Inv.checkInBounds _ _ _)) fun _ =>
        field_safe limits quirks cx authority width ⟨prepare, transfer⟩ field 0 (.memory ptr)

end

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordEffects
