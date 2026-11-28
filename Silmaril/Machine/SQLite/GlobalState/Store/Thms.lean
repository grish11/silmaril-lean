module

public import Silmaril.Machine.SQLite.GlobalState.Store.Defs
public import Silmaril.Machine.SQLite.GlobalState.Thms
import Silmaril.Proofs.Machine.SQLite.GlobalState.Store.Erasure
import Std.Data.ExtHashMap.Lemmas

public section

namespace Silmaril.Machine.SQLite.GlobalState

universe u v w

variable {ObjectId : Type u} [BEq ObjectId] [Hashable ObjectId] [LawfulBEq ObjectId]
variable {Payload : ObjectKind → Type v} {Target : ObjectKind → Type w}

@[simp] theorem ObjectStore.lookup_restrict (store : ObjectStore ObjectId) (view : KindView)
    (id : ObjectId) :
    (store.restrict view).lookup id = (store.lookup id).filter view.supports :=
  Std.ExtHashMap.getElem?_filter' (m := store)

namespace Objects

@[simp] theorem lookup_map (store : Objects ObjectId Payload)
    (f : (kind : ObjectKind) → Payload kind → Target kind) (id : ObjectId) :
    (store.map f).lookup id = (store.lookup id).map (Object.map f) :=
  Std.ExtHashMap.getElem?_map (m := store)

@[simp] theorem lookup_toKinds (store : Objects ObjectId Payload) (id : ObjectId) :
    store.toKinds.lookup id = (store.lookup id).map Object.kind :=
  Std.ExtHashMap.getElem?_map (m := store)

@[simp] theorem lookup_restrict (store : Objects ObjectId Payload) (view : KindView)
    (id : ObjectId) :
    (store.restrict view).lookup id = store.lookupSupported view id :=
  Std.ExtHashMap.getElem?_filter' (m := store)

theorem toKinds_map (store : Objects ObjectId Payload)
    (f : (kind : ObjectKind) → Payload kind → Target kind) :
    (store.map f).toKinds = store.toKinds := by
  apply ObjectStore.ext
  intro id
  simp [Object.map, Function.comp_def]

theorem map_restrict (store : Objects ObjectId Payload) (view : KindView)
    (f : (kind : ObjectKind) → Payload kind → Target kind) :
    (store.restrict view).map f = (store.map f).restrict view :=
  Proofs.Machine.SQLite.GlobalState.Store.map_restrict store view f

theorem toKinds_restrict (store : Objects ObjectId Payload) (view : KindView) :
    (store.restrict view).toKinds = store.toKinds.restrict view :=
  Proofs.Machine.SQLite.GlobalState.Store.toKinds_restrict store view

theorem checkId_isSome (store : Objects ObjectId Payload) (view : KindView) (id : ObjectId) :
    (store.checkId view id).isSome = ((store.toKinds.restrict view).lookup id).isSome :=
  Proofs.Machine.SQLite.GlobalState.Store.checkId_isSome store view id

theorem lookup_get (store : Objects ObjectId Payload) (view : KindView)
    (id : store.PresentId view) :
    store.lookup id.val = some (store.get view id) :=
  Option.eq_some_of_filter_eq_some (Option.some_get id.property).symm

theorem lookup_kind_get (store : Objects ObjectId Payload) (view : KindView)
    (id : store.PresentId view) :
    (store.toKinds.restrict view).lookup id.val = some (store.get view id).kind :=
  Proofs.Machine.SQLite.GlobalState.Store.lookup_kind_get store view id

end Objects

namespace History

@[simp] theorem lookup_empty (id : ObjectId) :
    (empty : History ObjectId Payload).lookup id = none :=
  Std.ExtHashMap.getElem?_empty

@[simp] theorem lookup_map (history : History ObjectId Payload)
    (f : (kind : ObjectKind) → Payload kind → Target kind) (id : ObjectId) :
    (history.map f).lookup id = (history.lookup id).map (HistoryEntry.map f) :=
  Std.ExtHashMap.getElem?_map (m := history)

@[simp] theorem lookup_toObjects (history : History ObjectId Payload) (id : ObjectId) :
    history.toObjects.lookup id = (history.lookup id).bind HistoryEntry.toObject :=
  Std.ExtHashMap.getElem?_filterMap' (m := history)

theorem toObjects_map (history : History ObjectId Payload)
    (f : (kind : ObjectKind) → Payload kind → Target kind) :
    (history.map f).toObjects = history.toObjects.map f :=
  Proofs.Machine.SQLite.GlobalState.Store.toObjects_map history f

private theorem lookup_insert_of_ne (history : History ObjectId Payload) {id query : ObjectId}
    (other : query ≠ id) (entry : HistoryEntry Payload) :
    History.lookup (Std.ExtHashMap.insert history id entry) query = history.lookup query :=
  (Std.ExtHashMap.getElem?_insert (m := history)).trans (ite_eq_right (by simpa using Ne.symm other))

@[simp] theorem lookup_allocate_self (history : History ObjectId Payload) (id : ObjectId)
    (kind : ObjectKind) (payload : Payload kind) (fresh : history.Fresh id) :
    (history.allocate id kind payload fresh).lookup id = some (.present ⟨kind, .live, payload⟩) :=
  Std.ExtHashMap.getElem?_insert_self (m := history)

theorem lookup_allocate_of_ne (history : History ObjectId Payload) {id query : ObjectId}
    (other : query ≠ id) (kind : ObjectKind) (payload : Payload kind) (fresh : history.Fresh id) :
    (history.allocate id kind payload fresh).lookup query = history.lookup query :=
  lookup_insert_of_ne history other (.present ⟨kind, .live, payload⟩)

@[simp] theorem lookup_updatePresent_self (history : History ObjectId Payload) (id : ObjectId)
    {object : Object Payload} (present : history.lookup id = some (.present object))
    (state : PresentState) (payload : Payload object.kind) :
    (history.updatePresent id present state payload).lookup id =
      some (.present ⟨object.kind, state, payload⟩) :=
  Std.ExtHashMap.getElem?_insert_self (m := history)

theorem lookup_updatePresent_of_ne (history : History ObjectId Payload) {id query : ObjectId}
    (other : query ≠ id) {object : Object Payload} (present : history.lookup id = some (.present object))
    (state : PresentState) (payload : Payload object.kind) :
    (history.updatePresent id present state payload).lookup query = history.lookup query :=
  lookup_insert_of_ne history other (.present ⟨object.kind, state, payload⟩)

@[simp] theorem lookup_free_self (history : History ObjectId Payload) (id : ObjectId)
    {object : Object Payload} (present : history.lookup id = some (.present object)) :
    (history.free id present).lookup id = some (.freed object.kind) :=
  Std.ExtHashMap.getElem?_insert_self (m := history)

theorem lookup_free_of_ne (history : History ObjectId Payload) {id query : ObjectId}
    (other : query ≠ id) {object : Object Payload} (present : history.lookup id = some (.present object)) :
    (history.free id present).lookup query = history.lookup query :=
  lookup_insert_of_ne history other (.freed object.kind)

theorem fresh_allocate_iff (history : History ObjectId Payload) (id query : ObjectId)
    (kind : ObjectKind) (payload : Payload kind) (fresh : history.Fresh id) :
    (history.allocate id kind payload fresh).Fresh query ↔ query ≠ id ∧ history.Fresh query :=
  Proofs.Machine.SQLite.GlobalState.Store.fresh_allocate_iff history id query kind payload fresh

theorem fresh_updatePresent_iff (history : History ObjectId Payload) (id query : ObjectId)
    {object : Object Payload} (present : history.lookup id = some (.present object))
    (state : PresentState) (payload : Payload object.kind) :
    (history.updatePresent id present state payload).Fresh query ↔ history.Fresh query :=
  Proofs.Machine.SQLite.GlobalState.Store.fresh_updatePresent_iff history id query present state payload

theorem fresh_free_iff (history : History ObjectId Payload) (id query : ObjectId)
    {object : Object Payload} (present : history.lookup id = some (.present object)) :
    (history.free id present).Fresh query ↔ history.Fresh query :=
  Proofs.Machine.SQLite.GlobalState.Store.fresh_free_iff history id query present

/-- Forgetting a tombstone gives the same present snapshot as deleting the object. -/
theorem toObjects_free (history : History ObjectId Payload) (id : ObjectId)
    {object : Object Payload} (present : history.lookup id = some (.present object)) :
    (history.free id present).toObjects = history.toObjects.erase id :=
  Proofs.Machine.SQLite.GlobalState.Store.toObjects_free history id present

/-- A freed binding and an unbound identity can have identical objects-only observations. -/
theorem toObjects_not_injective (id : ObjectId) (kind : ObjectKind) :
    ¬ Function.Injective (History.toObjects (ObjectId := ObjectId) (Payload := Payload)) :=
  Proofs.Machine.SQLite.GlobalState.Store.toObjects_not_injective id kind

end History

end Silmaril.Machine.SQLite.GlobalState
