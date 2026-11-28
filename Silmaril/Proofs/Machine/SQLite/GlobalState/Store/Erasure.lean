module

public import Silmaril.Machine.SQLite.GlobalState.Store.Defs
import Silmaril.Machine.SQLite.GlobalState.Thms
import Std.Data.ExtHashMap.Lemmas

public section

namespace Silmaril.Proofs.Machine.SQLite.GlobalState.Store

open Silmaril.Machine.SQLite.GlobalState

universe u v w

variable {ObjectId : Type u} [BEq ObjectId] [Hashable ObjectId] [LawfulBEq ObjectId]
variable {Payload : ObjectKind → Type v} {Target : ObjectKind → Type w}

private theorem lookup_supported_kind (store : Objects ObjectId Payload) (view : KindView)
    (id : ObjectId) :
    (store.toKinds.restrict view).lookup id = (store.lookupSupported view id).map Object.kind := by
  calc
    _ = (store.toKinds.lookup id).filter view.supports :=
      Std.ExtHashMap.getElem?_filter' (m := store.toKinds)
    _ = ((store.lookup id).map Object.kind).filter view.supports :=
      congrArg (Option.filter view.supports) (Std.ExtHashMap.getElem?_map (m := store))
    _ = _ := Option.filter_map

theorem map_restrict (store : Objects ObjectId Payload) (view : KindView)
    (f : (kind : ObjectKind) → Payload kind → Target kind) :
    (store.restrict view).map f = (store.map f).restrict view := by
  apply Std.ExtHashMap.ext_getElem?
  intro id
  unfold Objects.map Objects.restrict
  rw [Std.ExtHashMap.getElem?_map, Std.ExtHashMap.getElem?_filter',
    Std.ExtHashMap.getElem?_filter', Std.ExtHashMap.getElem?_map, Option.filter_map]
  rfl

theorem toKinds_restrict (store : Objects ObjectId Payload) (view : KindView) :
    (store.restrict view).toKinds = store.toKinds.restrict view := by
  apply ObjectStore.ext
  intro id
  rw [lookup_supported_kind]
  calc
    _ = ((store.restrict view).lookup id).map Object.kind :=
      Std.ExtHashMap.getElem?_map (m := store.restrict view)
    _ = _ := congrArg (Option.map Object.kind) (Std.ExtHashMap.getElem?_filter' (m := store))

theorem checkId_isSome (store : Objects ObjectId Payload) (view : KindView) (id : ObjectId) :
    (store.checkId view id).isSome = ((store.toKinds.restrict view).lookup id).isSome := by
  rw [lookup_supported_kind, Option.isSome_map]
  by_cases h : (store.lookupSupported view id).isSome <;> simp [Objects.checkId, h]

theorem lookup_kind_get (store : Objects ObjectId Payload) (view : KindView)
    (id : store.PresentId view) :
    (store.toKinds.restrict view).lookup id.val = some (store.get view id).kind := by
  rw [lookup_supported_kind]
  exact congrArg (Option.map Object.kind) (Option.some_get id.property).symm

theorem toObjects_map (history : History ObjectId Payload)
    (f : (kind : ObjectKind) → Payload kind → Target kind) :
    (history.map f).toObjects = history.toObjects.map f := by
  apply Std.ExtHashMap.ext_getElem?
  intro id
  unfold History.map History.toObjects Objects.map
  rw [Std.ExtHashMap.getElem?_filterMap', Std.ExtHashMap.getElem?_map,
    Std.ExtHashMap.getElem?_map, Std.ExtHashMap.getElem?_filterMap']
  cases (show Std.ExtHashMap ObjectId (HistoryEntry Payload) from history)[id]? with
  | none => rfl
  | some entry => cases entry <;> rfl

private theorem fresh_insert_iff (history : History ObjectId Payload) (id query : ObjectId)
    (entry : HistoryEntry Payload) :
    (History.lookup (Std.ExtHashMap.insert history id entry) query = none) ↔
      query ≠ id ∧ history.Fresh query := by
  change ((Std.ExtHashMap.insert history id entry)[query]? = none) ↔
    query ≠ id ∧ history[query]? = none
  rw [Std.ExtHashMap.getElem?_insert]
  by_cases h : query = id <;> simp [beq_iff_eq, eq_comm (a := id), h]

theorem fresh_allocate_iff (history : History ObjectId Payload) (id query : ObjectId)
    (kind : ObjectKind) (payload : Payload kind) (fresh : history.Fresh id) :
    (history.allocate id kind payload fresh).Fresh query ↔ query ≠ id ∧ history.Fresh query :=
  fresh_insert_iff history id query (.present ⟨kind, .live, payload⟩)

private theorem fresh_write_iff_of_present (history : History ObjectId Payload)
    (id query : ObjectId) {object : Object Payload}
    (present : history.lookup id = some (.present object)) (entry : HistoryEntry Payload) :
    (History.lookup (Std.ExtHashMap.insert history id entry) query = none) ↔ history.Fresh query := by
  rw [fresh_insert_iff]
  refine ⟨And.right, fun fresh => ⟨?_, fresh⟩⟩
  rintro rfl
  simp [History.Fresh, present] at fresh

theorem fresh_updatePresent_iff (history : History ObjectId Payload) (id query : ObjectId)
    {object : Object Payload} (present : history.lookup id = some (.present object))
    (state : PresentState) (payload : Payload object.kind) :
    (history.updatePresent id present state payload).Fresh query ↔ history.Fresh query :=
  fresh_write_iff_of_present history id query present (.present ⟨object.kind, state, payload⟩)

theorem fresh_free_iff (history : History ObjectId Payload) (id query : ObjectId)
    {object : Object Payload} (present : history.lookup id = some (.present object)) :
    (history.free id present).Fresh query ↔ history.Fresh query :=
  fresh_write_iff_of_present history id query present (.freed object.kind)

theorem toObjects_free (history : History ObjectId Payload) (id : ObjectId)
    {object : Object Payload} (present : history.lookup id = some (.present object)) :
    (history.free id present).toObjects = history.toObjects.erase id := by
  apply Std.ExtHashMap.ext_getElem?
  intro query
  unfold History.toObjects History.free
  rw [Std.ExtHashMap.getElem?_filterMap', Std.ExtHashMap.getElem?_insert,
    Std.ExtHashMap.getElem?_erase, Std.ExtHashMap.getElem?_filterMap']
  split <;> rfl

theorem toObjects_not_injective (id : ObjectId) (kind : ObjectKind) :
    ¬ Function.Injective (History.toObjects (ObjectId := ObjectId) (Payload := Payload)) := by
  intro injective
  let empty : History ObjectId Payload := History.empty
  let tombstone : History ObjectId Payload := Std.ExtHashMap.insert empty id (.freed kind)
  have erased : tombstone.toObjects = empty.toObjects := by
    apply Std.ExtHashMap.ext_getElem?
    intro query
    unfold History.toObjects tombstone
    rw [Std.ExtHashMap.getElem?_filterMap', Std.ExtHashMap.getElem?_insert,
      Std.ExtHashMap.getElem?_filterMap']
    split <;> simp [empty, History.empty, HistoryEntry.toObject]
  have equal := congrArg (fun history : History ObjectId Payload => history.lookup id)
    (injective erased)
  change (Std.ExtHashMap.insert empty id (.freed kind))[id]? = _ at equal
  simp [empty, History.lookup, History.empty] at equal

end Silmaril.Proofs.Machine.SQLite.GlobalState.Store
