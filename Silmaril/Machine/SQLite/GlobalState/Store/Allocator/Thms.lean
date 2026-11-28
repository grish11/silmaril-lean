module

public import Silmaril.Machine.SQLite.GlobalState.Store.Allocator.Defs
public import Silmaril.Machine.SQLite.GlobalState.Store.Thms
import Std.Data.ExtHashMap.Lemmas

public section

namespace Silmaril.Machine.SQLite.GlobalState

universe u v p l t

variable {ObjectId : Type u} [BEq ObjectId] [Hashable ObjectId] [LawfulBEq ObjectId]
variable {AllocId : Type v} [BEq AllocId] [Hashable AllocId] [LawfulBEq AllocId]
variable {Payload : ObjectKind → Type p} {Live : Type l} {Tombstone : Type t}

namespace AllocationHistory

@[simp] theorem lookup_empty (id : AllocId) :
    AllocationHistory.lookup (∅ : AllocationHistory AllocId Live Tombstone) id = none :=
  Std.ExtHashMap.getElem?_empty

@[simp] theorem lookup_insert_self (history : AllocationHistory AllocId Live Tombstone)
    (id : AllocId) (entry : AllocationEntry Live Tombstone) :
    AllocationHistory.lookup (history.insert id entry) id = some entry :=
  Std.ExtHashMap.getElem?_insert_self (m := history)

theorem lookup_insert_of_ne (history : AllocationHistory AllocId Live Tombstone) {id query : AllocId}
    (other : query ≠ id) (entry : AllocationEntry Live Tombstone) :
    AllocationHistory.lookup (history.insert id entry) query = history.lookup query :=
  (Std.ExtHashMap.getElem?_insert (m := history)).trans (ite_eq_right (by simpa using Ne.symm other))

end AllocationHistory

namespace AllocatorStore

/-- Tagged erasure preserves present object lookups and drops object tombstones
and every raw allocation, even when the two ID types coincide. -/
theorem lookup_toObjects (store : AllocatorStore ObjectId AllocId Payload Live Tombstone)
    (id : StoreId ObjectId AllocId) :
    store.toObjects.lookupTagged id = (store.lookup id).bind StoreEntry.toObject := by
  cases id <;> simp [toObjects, Objects.lookupTagged, lookup, Option.bind_map,
    Function.comp_def, StoreEntry.toObject]

omit [LawfulBEq AllocId] in
@[simp] theorem checkObjectId_allocation (store : AllocatorStore ObjectId AllocId Payload Live Tombstone)
    (view : KindView) (id : AllocId) :
    store.checkObjectId view (.allocation id) = none :=
  rfl

end AllocatorStore

end Silmaril.Machine.SQLite.GlobalState
