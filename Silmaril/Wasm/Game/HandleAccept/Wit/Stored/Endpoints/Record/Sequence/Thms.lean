module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Sequence.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordSequence

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value

/-- The actual flat emitter sequences checked child programs in canonical order.
No leaf effect is erased, and neither a typed refusal nor a canonical trap runs the tail. -/
theorem runFlat_sequence {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (authority : Authority E World) (width : AddrType)
    (fields : List Field) (index : Nat) :
    Internal.runFlat limits quirks cx authority width fields index =
      (flatSequence (m := ExceptT Issue (P E World))
        (fun atIndex field => ExceptT.mk (Internal.runField limits quirks cx authority width
          field atIndex .flat)) fields index).run :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordSequence.runFlat
    limits quirks cx authority width fields index

theorem lowerFlatFields_sequence {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (fields : List Field)
    (schema : List (String × TypeOf)) (index : Nat)
    (types : fields.map Field.type = schema.map Prod.snd) :
    (Canon.lowerFlatFields limits quirks cx width (Field.values fields) schema : P E World _) =
      flatSequence (fun _ field => lowerFlatAt limits quirks cx width field.value field.type) fields index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordSequence.lowerFlatFields
    limits quirks cx width fields schema index types

theorem lowerFlatTypes_sequence {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (fields : List Field) (index : Nat) :
    (Canon.lowerFlatTypes limits quirks cx width (Field.values fields) (fields.map Field.type) : P E World _) =
      flatSequence (fun _ field => lowerFlatAt limits quirks cx width field.value field.type) fields index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordSequence.lowerFlatTypes
    limits quirks cx width fields index

theorem lowerFlatFixed_sequence {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (fields : List Field)
    (element : TypeOf) (length index : Nat) (types : ∀ field ∈ fields, field.type = element) :
    (lowerFlatAt limits quirks cx width (.list (Field.values fields)) (.fixedList element length) : P E World _) =
      flatSequence (fun _ field => lowerFlatAt limits quirks cx width field.value field.type) fields index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordSequence.lowerFlatFixed
    limits quirks cx width fields element length index types

/-- The checked cursor uses the emitter's width. The canonical rule below reads
the reached width per field; relating those across reentry is a separate obligation. -/
theorem runMemory_sequence {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (authority : Authority E World) (width : AddrType)
    (fields : List Field) (ptr index : Nat) :
    Internal.runMemory limits quirks cx authority width fields ptr index =
      (memorySequence (m := ExceptT Issue (P E World)) (pure width)
        (fun atIndex field addr => ExceptT.mk (Internal.runField limits quirks cx authority width
          field atIndex (.memory addr))) fields ptr index).run :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordSequence.runMemory
    limits quirks cx authority width fields ptr index

theorem storeFields_sequence {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (fields : List Field) (schema : List (String × TypeOf)) (ptr index : Nat)
    (types : fields.map Field.type = schema.map Prod.snd) :
    (Canon.storeFields limits quirks cx (Field.values fields) schema ptr : P E World _) =
      memorySequence (ptrType cx) (fun _ field addr => store limits quirks cx field.value field.type addr)
        fields ptr index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordSequence.storeFields
    limits quirks cx fields schema ptr index types

theorem storeTuple_sequence {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (fields : List Field) (ptr index : Nat) :
    (Canon.storeTuple limits quirks cx (Field.values fields) (fields.map Field.type) ptr : P E World _) =
      memorySequence (ptrType cx) (fun _ field addr => store limits quirks cx field.value field.type addr)
        fields ptr index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordSequence.storeTuple
    limits quirks cx fields ptr index

theorem runElements_sequence {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (authority : Authority E World) (width : AddrType)
    (fields : List Field) (stride ptr index : Nat) :
    Internal.runElements limits quirks cx authority width fields stride ptr index =
      (elementSequence (m := ExceptT Issue (P E World))
        (fun atIndex field addr => ExceptT.mk (Internal.runField limits quirks cx authority width
          field atIndex (.memory addr))) fields stride ptr index).run :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordSequence.runElements
    limits quirks cx authority width fields stride ptr index

theorem storeListIntoValidRangeWith_sequence {E : CoreEngine} {World : Type}
    (storeElem : Val → Nat → P E World Unit) (fields : List Field) (stride ptr index : Nat) :
    Canon.storeListIntoValidRangeWith stride storeElem (Field.values fields) ptr =
      elementSequence (fun _ field addr => storeElem field.value addr) fields stride ptr index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordSequence.storeListIntoValidRangeWith
    storeElem fields stride ptr index

/-- The dynamic list and map branch runs the canonical allocation program between the
two live checks. Only successful element traversal reaches descriptor publication. -/
theorem runDynamic_sequence {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (authority : Authority E World) (width : AddrType)
    (type element : TypeOf) (entries : List Field) (index : Nat) (output : Stored.Lower.Output) :
    Internal.runField limits quirks cx authority width (.dynamic type element entries) index output = (do
      let plan := Field.listObjects entries
      match ← authority.prepare plan with
      | .error (.preflight issue) => return .error (.field index (.beforeAllocation issue))
      | .error issue => return .error (.nested index issue)
      | .ok () =>
        let area := layout width element
        let ptr ← Canon.allocateListRange cx area entries.length
        match ← authority.prepare plan with
        | .error (.preflight issue) => return .error (.field index (.afterAllocation issue))
        | .error issue => return .error (.nested index issue)
        | .ok () =>
          match ← (elementSequence (m := ExceptT Issue (P E World))
            (fun atIndex field addr => ExceptT.mk (Internal.runField limits quirks cx authority width
              field atIndex (.memory addr))) entries area.size ptr 0).run with
          | .error issue => return .error (.nested index issue)
          | .ok () => return .ok (← ListLower.publish cx width ptr entries.length output)) := by
  rw [Internal.runField]
  simp only [ListLower.allocateRange, runElements_sequence]
  rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
