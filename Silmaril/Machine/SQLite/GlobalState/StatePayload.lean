module

public import Silmaril.Machine.SQLite.GlobalState.Store.Thms
public import Silmaril.Machine.SQLite.GlobalState.StructThms
public import Silmaril.Machine.SQLite.GlobalState.Flat.Thms
import Std.Data.ExtHashMap.Lemmas

@[expose] public section

namespace Silmaril.Machine.SQLite.GlobalState.IndexedStore

/-- Add a caller-supplied live/zombie state to each present struct. The
existing kind store supplies the finite set of tagged keys. -/
def toObjects (store : IndexedStore) (state : TaggedId → PresentState) :
    Objects TaggedId LocalFields :=
  Std.ExtHashMap.filterMap (fun id _ =>
    (store.lookup id.localId).map fun fields => ⟨id.kind, state id, fields⟩) store.erasePayloads

@[simp] theorem lookup_toObjects (store : IndexedStore) (state : TaggedId → PresentState)
    (id : TaggedId) : (store.toObjects state).lookup id =
    (store.lookup id.localId).map (fun fields => ⟨id.kind, state id, fields⟩) := by
  refine (Std.ExtHashMap.getElem?_filterMap' (m := store.erasePayloads)).trans ?_
  change (store.erasePayloads.lookup id).bind _ = _
  rw [store.lookup_erasePayloads id]
  cases store.lookup id.localId <;> rfl

@[simp] theorem toObjects_toKinds (store : IndexedStore) (state : TaggedId → PresentState) :
    (store.toObjects state).toKinds = store.erasePayloads := by
  apply ObjectStore.ext fun id => ?_
  rw [Objects.lookup_toKinds, lookup_toObjects, lookup_erasePayloads]
  cases store.lookup id.localId <;> rfl

/-- Dropping fields before dropping the live/zombie state gives the same
kind store as erasing the indexed structs directly. -/
theorem toObjects_toStates_toKinds (store : IndexedStore) (state : TaggedId → PresentState) :
    (store.toObjects state).toStates.toKinds = store.erasePayloads :=
  (Objects.toKinds_map (store.toObjects state) (fun _ _ => ())).trans (store.toObjects_toKinds state)

end Silmaril.Machine.SQLite.GlobalState.IndexedStore

namespace Silmaril.Machine.SQLite.GlobalState.FlatStore

theorem lookup_toObjects (store : FlatStore) (state : TaggedId → PresentState) (id : TaggedId) :
    (store.toIndexed.toObjects state).lookup id =
      (store.get? id).map (fun fields => ⟨id.kind, state id, fields⟩) := by
  rw [IndexedStore.lookup_toObjects, lookup_toIndexed]

/-- The state-store erasures agree with the kind at each original flat key. -/
theorem lookup_toStates_toKinds (store : FlatStore) (state : TaggedId → PresentState) (id : TaggedId) :
    (store.toIndexed.toObjects state).toStates.toKinds.lookup id =
      (store.get? id).map (fun _ => id.kind) := by
  rw [IndexedStore.toObjects_toStates_toKinds, IndexedStore.lookup_erasePayloads, lookup_toIndexed]

end Silmaril.Machine.SQLite.GlobalState.FlatStore
