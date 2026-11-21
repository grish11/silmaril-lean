module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Sequence.Defs

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordSequence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (TypeOf)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

theorem runFlat {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (authority : Authority E World) (width : AddrType)
    (fields : List Field) (index : Nat) :
    Internal.runFlat limits quirks cx authority width fields index =
      (flatSequence (m := ExceptT Issue (P E World))
        (fun atIndex field => ExceptT.mk (Internal.runField limits quirks cx authority width
          field atIndex .flat)) fields index).run := by
  induction fields generalizing index with
  | nil => rw [Internal.runFlat]; rfl
  | cons field rest ih =>
    rw [Internal.runFlat, flatSequence]
    rw [ih]
    simp only [bind_pure_comp]
    congr 1
    funext result
    cases result with
    | error => rfl
    | ok words =>
      simp only [ExceptT.bindCont, ← bind_pure_comp]
      change (_ : P E World _) >>= _ = _ >>= _
      congr 1
      funext tailResult
      cases tailResult <;> rfl

theorem lowerFlatFields {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (fields : List Field)
    (schema : List (String × TypeOf)) (index : Nat)
    (types : fields.map Field.type = schema.map Prod.snd) :
    (Canon.lowerFlatFields limits quirks cx width (Field.values fields) schema : P E World _) =
      flatSequence (fun _ field => lowerFlatAt limits quirks cx width field.value field.type) fields index := by
  induction fields generalizing schema index with
  | nil => cases schema <;> cases types; rfl
  | cons field rest ih =>
    cases schema with
    | nil => cases types
    | cons entry schema =>
      obtain ⟨sameType, sameRest⟩ := List.cons.inj types
      rw [Field.values, Canon.lowerFlatFields, flatSequence, sameType, ih schema _ sameRest]

theorem lowerFlatTypes {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (fields : List Field) (index : Nat) :
    (Canon.lowerFlatTypes limits quirks cx width (Field.values fields) (fields.map Field.type) : P E World _) =
      flatSequence (fun _ field => lowerFlatAt limits quirks cx width field.value field.type) fields index := by
  induction fields generalizing index with
  | nil => rfl
  | cons field rest ih =>
    rw [List.map_cons, Field.values, Canon.lowerFlatTypes, flatSequence, ih]

private theorem flatElements {E : CoreEngine} {World : Type} (limits : Component.Limits)
    (quirks : Quirks) (cx : LiftLowerContext E) (width : AddrType) (fields : List Field)
    (element : TypeOf) (index : Nat) (types : ∀ field ∈ fields, field.type = element) :
    (do let parts ← Prog.mapM (fun entry => lowerFlatAt limits quirks cx width entry element)
          (Field.values fields)
        return parts.flatten : P E World _) =
      flatSequence (fun _ field => lowerFlatAt limits quirks cx width field.value field.type) fields index := by
  induction fields generalizing index with
  | nil => rfl
  | cons field rest ih =>
    rw [Field.values, Prog.mapM, flatSequence, types field (List.mem_cons_self ..)]
    rw [← ih (index + 1) (fun item mem => types item (List.mem_cons_of_mem _ mem))]
    simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.pure_bind', List.flatten_cons]

theorem lowerFlatFixed {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (fields : List Field)
    (element : TypeOf) (length index : Nat) (types : ∀ field ∈ fields, field.type = element) :
    (lowerFlatAt limits quirks cx width (.list (Field.values fields)) (.fixedList element length) : P E World _) =
      flatSequence (fun _ field => lowerFlatAt limits quirks cx width field.value field.type) fields index := by
  rw [lowerFlatAt]
  exact flatElements limits quirks cx width fields element index types

theorem runMemory {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (authority : Authority E World) (width : AddrType)
    (fields : List Field) (ptr index : Nat) :
    Internal.runMemory limits quirks cx authority width fields ptr index =
      (memorySequence (m := ExceptT Issue (P E World)) (pure width)
        (fun atIndex field addr => ExceptT.mk (Internal.runField limits quirks cx authority width
          field atIndex (.memory addr))) fields ptr index).run := by
  induction fields generalizing ptr index with
  | nil => rw [Internal.runMemory]; rfl
  | cons field rest ih =>
    rw [Internal.runMemory, memorySequence]
    dsimp only
    rw [ih]
    simp only [pure_bind]
    congr 1
    funext result
    cases result with
    | error => rfl
    | ok stored => cases stored; rfl

theorem storeFields {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (fields : List Field) (schema : List (String × TypeOf)) (ptr index : Nat)
    (types : fields.map Field.type = schema.map Prod.snd) :
    (Canon.storeFields limits quirks cx (Field.values fields) schema ptr : P E World _) =
      memorySequence (ptrType cx) (fun _ field addr => store limits quirks cx field.value field.type addr)
        fields ptr index := by
  induction fields generalizing schema ptr index with
  | nil => cases schema <;> cases types; rw [Field.values, Canon.storeFields]; rfl
  | cons field rest ih =>
    cases schema with
    | nil => cases types
    | cons entry schema =>
      obtain ⟨sameType, sameRest⟩ := List.cons.inj types
      rw [Field.values, Canon.storeFields, memorySequence, sameType]
      simp only [Prog.bind_eq]
      congr 1
      funext reachedWidth
      congr 1
      funext stored
      exact ih schema _ _ sameRest

theorem storeTuple {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (fields : List Field) (ptr index : Nat) :
    (Canon.storeTuple limits quirks cx (Field.values fields) (fields.map Field.type) ptr : P E World _) =
      memorySequence (ptrType cx) (fun _ field addr => store limits quirks cx field.value field.type addr)
        fields ptr index := by
  induction fields generalizing ptr index with
  | nil => rw [List.map_nil, Field.values, Canon.storeTuple]; rfl
  | cons field rest ih =>
    rw [List.map_cons, Field.values, Canon.storeTuple, memorySequence]
    simp only [Prog.bind_eq]
    congr 1
    funext reachedWidth
    congr 1
    funext stored
    exact ih _ _

theorem runElements {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (authority : Authority E World) (width : AddrType)
    (fields : List Field) (stride ptr index : Nat) :
    Internal.runElements limits quirks cx authority width fields stride ptr index =
      (elementSequence (m := ExceptT Issue (P E World))
        (fun atIndex field addr => ExceptT.mk (Internal.runField limits quirks cx authority width
          field atIndex (.memory addr))) fields stride ptr index).run := by
  induction fields generalizing ptr index with
  | nil => rw [Internal.runElements]; rfl
  | cons field rest ih =>
    rw [Internal.runElements, elementSequence, ih]
    congr 1
    funext result
    cases result with
    | error => rfl
    | ok stored => cases stored; rfl

private theorem storeListLoop {E : CoreEngine} {World : Type} (storeElem : Val → Nat → P E World Unit)
    (fields : List Field) (stride ptr offset index : Nat) :
    Prog.forM ((Field.values fields).zipIdx offset) (fun (value, position) => storeElem value (ptr + position * stride)) =
      elementSequence (fun _ field addr => storeElem field.value addr) fields stride
        (ptr + offset * stride) index := by
  induction fields generalizing offset index with
  | nil => rfl
  | cons field rest ih =>
    rw [Field.values, List.zipIdx_cons, Prog.forM, elementSequence, ih (offset + 1) (index + 1)]
    congr 1
    rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]

theorem storeListIntoValidRangeWith {E : CoreEngine} {World : Type}
    (storeElem : Val → Nat → P E World Unit) (fields : List Field) (stride ptr index : Nat) :
    Canon.storeListIntoValidRangeWith stride storeElem (Field.values fields) ptr =
      elementSequence (fun _ field addr => storeElem field.value addr) fields stride ptr index := by
  simpa only [Canon.storeListIntoValidRangeWith, Nat.zero_mul, Nat.add_zero] using
    storeListLoop storeElem fields stride ptr 0 index

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordSequence
