module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Collection.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Sequence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordCollection

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored

variable {E : CoreEngine} {World : Type}

private theorem values_length (entries : List Field) : (Field.values entries).length = entries.length := by
  induction entries with
  | nil => rfl
  | cons field rest ih => simp only [Field.values, List.length_cons, ih]

theorem dynamic_list (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (element : TypeOf) (entries : List Field) (output : Lower.Output) :
    Lower.Output.rec (motive := fun out => P E World out.Result)
      (fun ptr => store limits quirks cx (.list (Field.values entries)) (.list element) ptr)
      (lowerFlatAt limits quirks cx width (.list (Field.values entries)) (.list element)) output =
    canonicalDynamic cx width element entries (fun _ field ptr => store limits quirks cx field.value element ptr)
      output := by
  cases output with
  | memory ptr =>
    change store limits quirks cx (.list (Field.values entries)) (.list element) ptr = _
    rw [store]
    simp only [storeListWith, Bool.false_eq_true, ↓reduceIte, canonicalDynamic, ListLower.publish,
      storeListIntoRangeWith, values_length, storeListIntoValidRangeWith_sequence (index := 0),
      bind_assoc, pure_bind]
    rfl
  | flat =>
    change lowerFlatAt limits quirks cx width (.list (Field.values entries)) (.list element) = _
    rw [lowerFlatAt]
    simp only [canonicalDynamic, ListLower.publish, storeListIntoRange, storeListIntoRangeWith, values_length,
      storeListIntoValidRangeWith_sequence (index := 0), bind_assoc, pure_bind]
    rfl

theorem fixed_memory (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (element : TypeOf) (length : Nat) (entries : List Field) (ptr index : Nat) :
    (store limits quirks cx (.list (Field.values entries)) (.fixedList element length) ptr : P E World Unit) = (do
      let width ← ptrType cx
      elementSequence (fun _ field addr => store limits quirks cx field.value element addr)
        entries (layout width element).size ptr index) := by
  rw [store]
  simp only [storeListWith, ↓reduceIte, storeListIntoValidRangeWith_sequence (index := index)]

theorem dynamic_map_flat (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (key : WIT.KeyType) (element : TypeOf) (entries : List Field) :
    (lowerFlatAt limits quirks cx width (.list (Field.values entries)) (.map key element) : P E World _) =
    canonicalDynamic cx width (.record (mapEntryFields key element)) entries
      (fun _ field ptr => store limits quirks cx field.value (.record (mapEntryFields key element)) ptr) .flat := by
  rw [lowerFlatAt]
  simp only [canonicalDynamic, ListLower.publish, storeListIntoRange, storeListIntoRangeWith, values_length,
    storeListIntoValidRangeWith_sequence (index := 0), bind_assoc, pure_bind]
  rfl

theorem dynamic_map_memory (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (key : WIT.KeyType) (element : TypeOf) (entries : List Field) (dest : Nat) :
    (store limits quirks cx (.list (Field.values entries)) (.map key element) dest : P E World _) =
    canonicalDynamic cx width (.record (mapEntryFields key element)) entries
      (fun reachedWidth field => canonicalMapEntry limits quirks cx reachedWidth key element field.value)
      (.memory dest) := by
  rw [store]
  simp only [storeListWith, Bool.false_eq_true, ↓reduceIte, canonicalDynamic, ListLower.publish,
    storeListIntoRangeWith, values_length, storeListIntoValidRangeWith_sequence (index := 0),
    bind_assoc, pure_bind]
  rfl

theorem map_entry_layout {entry : Field} {key : WIT.KeyType} {element : TypeOf}
    (checked : entry.LayoutMatches (.record (mapEntryFields key element))) :
    (∃ keyField valueField, entry = .aggregate (.record (mapEntryFields key element)) [keyField, valueField] ∧
      keyField.LayoutMatches (.prim key.toPrimitive) ∧ valueField.LayoutMatches element) ∨
    (∃ payload, entry = .data (.record (mapEntryFields key element)) payload) := by
  cases entry with
  | endpoint channel => cases channel <;> cases checked
  | data => cases checked; exact Or.inr ⟨_, rfl⟩
  | aggregate =>
    cases checked with
    | record fields =>
      change Field.FieldsMatch _ [.prim key.toPrimitive, element] at fields
      cases fields with
      | cons keyLayout tail =>
        cases tail with
        | cons valueLayout empty =>
          cases empty
          exact Or.inl ⟨_, _, rfl, keyLayout, valueLayout⟩
  | _ => cases checked

theorem map_entry_memory (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (key : WIT.KeyType) (element : TypeOf) (keyField valueField : Field)
    (keyLayout : keyField.LayoutMatches (.prim key.toPrimitive)) (valueLayout : valueField.LayoutMatches element)
    (ptr index : Nat) :
    (canonicalMapEntry limits quirks cx width key element (.record (Field.values [keyField, valueField])) ptr :
      P E World Unit) =
    memorySequence (pure width) (fun _ field addr => store limits quirks cx field.value field.type addr)
      [keyField, valueField] ptr index := by
  have unit_id : (fun _ : Unit => ()) = id := funext fun value => by cases value; rfl
  simp only [canonicalMapEntry, Field.values, memorySequence, pure_bind, keyLayout.type_eq, valueLayout.type_eq,
    layout, store, bind_pure_comp, unit_id, id_map]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordCollection
