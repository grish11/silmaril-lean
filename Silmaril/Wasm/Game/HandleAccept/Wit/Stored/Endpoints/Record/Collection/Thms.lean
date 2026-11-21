module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Collection.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Sequence.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordCollection

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value

variable {E : CoreEngine} {World : Type}

/-- Both list ABIs allocate, validate the reached range, store the elements
in order, then publish. This identifies the entire canonical program. -/
theorem dynamic_list_canon (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (element : TypeOf) (entries : List Field) (output : Lower.Output) :
    Lower.Output.rec (motive := fun out => P E World out.Result)
      (fun ptr => store limits quirks cx (.list (Field.values entries)) (.list element) ptr)
      (lowerFlatAt limits quirks cx width (.list (Field.values entries)) (.list element)) output =
    canonicalDynamic cx width element entries (fun _ field ptr => store limits quirks cx field.value element ptr)
      output :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordCollection.dynamic_list
    limits quirks cx width element entries output

/-- A fixed collection uses the in-place canonical traversal, with no outer
allocation; its children can still perform canonical calls. -/
theorem fixed_memory_canon (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (element : TypeOf) (length : Nat) (entries : List Field) (ptr index : Nat) :
    (store limits quirks cx (.list (Field.values entries)) (.fixedList element length) ptr : P E World Unit) = (do
      let width ← ptrType cx
      elementSequence (fun _ field addr => store limits quirks cx field.value element addr)
        entries (layout width element).size ptr index) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordCollection.fixed_memory
    limits quirks cx element length entries ptr index

/-- A flat map stores despecialized records in the allocated range, then
returns the descriptor in the enclosing flat ABI's width. -/
theorem dynamic_map_flat_canon (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (key : WIT.KeyType) (element : TypeOf) (entries : List Field) :
    (lowerFlatAt limits quirks cx width (.list (Field.values entries)) (.map key element) : P E World _) =
    canonicalDynamic cx width (.record (mapEntryFields key element)) entries
      (fun _ field ptr => store limits quirks cx field.value (.record (mapEntryFields key element)) ptr) .flat :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordCollection.dynamic_map_flat
    limits quirks cx width key element entries

/-- A memory map stores its key and value with the allocation-time layout,
then writes the descriptor using the reached memory. -/
theorem dynamic_map_memory_canon (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (key : WIT.KeyType) (element : TypeOf) (entries : List Field) (dest : Nat) :
    (store limits quirks cx (.list (Field.values entries)) (.map key element) dest : P E World _) =
    canonicalDynamic cx width (.record (mapEntryFields key element)) entries
      (fun reachedWidth field => canonicalMapEntry limits quirks cx reachedWidth key element field.value)
      (.memory dest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordCollection.dynamic_map_memory
    limits quirks cx width key element entries dest

theorem map_entry_layout {entry : Field} {key : WIT.KeyType} {element : TypeOf}
    (checked : entry.LayoutMatches (.record (mapEntryFields key element))) :
    (∃ keyField valueField, entry = .aggregate (.record (mapEntryFields key element)) [keyField, valueField] ∧
      keyField.LayoutMatches (.prim key.toPrimitive) ∧ valueField.LayoutMatches element) ∨
    (∃ payload, entry = .data (.record (mapEntryFields key element)) payload) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordCollection.map_entry_layout checked

/-- With the allocation width supplied to the cursor, the memory-map entry
is exactly the same key-then-value program, including a key callback or trap. -/
theorem map_entry_memory_canon (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (key : WIT.KeyType) (element : TypeOf) (keyField valueField : Field)
    (keyLayout : keyField.LayoutMatches (.prim key.toPrimitive)) (valueLayout : valueField.LayoutMatches element)
    (ptr index : Nat) :
    (canonicalMapEntry limits quirks cx width key element (.record (Field.values [keyField, valueField])) ptr :
      P E World Unit) =
    memorySequence (pure width) (fun _ field addr => store limits quirks cx field.value field.type addr)
      [keyField, valueField] ptr index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordCollection.map_entry_memory
    limits quirks cx width key element keyField valueField keyLayout valueLayout ptr index

/-- The checked traversal uses the same full allocator/range program as the
canonical collection. Revalidation is after that program, not before it. -/
theorem checked_dynamic_canon_range (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (authority : Authority E World) (width : AddrType) (type element : TypeOf) (entries : List Field)
    (index : Nat) (output : Lower.Output) :
    Internal.runField limits quirks cx authority width (.dynamic type element entries) index output = (do
      let plan := Field.listObjects entries
      match ← authority.prepare plan with
      | .error (.preflight issue) => return .error (.field index (.beforeAllocation issue))
      | .error issue => return .error (.nested index issue)
      | .ok () =>
        let ptr ← allocateListRange cx (layout width element) entries.length
        let verdict ← authority.prepare plan
        checkedDynamicContinue limits quirks cx authority width element entries index output ptr verdict) := by
  rw [runDynamic_sequence]
  rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
