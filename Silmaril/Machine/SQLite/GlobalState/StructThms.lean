module

public import Silmaril.Machine.SQLite.GlobalState.Indexed
public import Silmaril.Machine.SQLite.GlobalState.Thms
import Silmaril.Proofs.Machine.SQLite.GlobalState.Indexed

public section

namespace Silmaril.Machine.SQLite.GlobalState.IndexedStore

@[simp] theorem lookup_empty {kind : ObjectKind} (id : LocalId kind) :
    empty.lookup id = none :=
  Proofs.Machine.SQLite.GlobalState.IndexedStore.lookup_empty id

@[simp] theorem lookup_insert_self (store : IndexedStore) {kind : ObjectKind} (id : LocalId kind)
    (fields : LocalFields kind) : (store.insert id fields).lookup id = some fields :=
  Proofs.Machine.SQLite.GlobalState.IndexedStore.lookup_insert_self store id fields

@[simp] theorem lookup_erase_self (store : IndexedStore) {kind : ObjectKind} (id : LocalId kind) :
    (store.erase id).lookup id = none :=
  Proofs.Machine.SQLite.GlobalState.IndexedStore.lookup_erase_self store id

theorem lookup_insert_of_ne (store : IndexedStore) {kind otherKind : ObjectKind}
    (id : LocalId kind) (fields : LocalFields kind) (other : LocalId otherKind)
    (different : other.tagged ≠ id.tagged) : (store.insert id fields).lookup other = store.lookup other :=
  Proofs.Machine.SQLite.GlobalState.IndexedStore.lookup_insert_of_ne store id fields other different

theorem lookup_erase_of_ne (store : IndexedStore) {kind otherKind : ObjectKind}
    (id : LocalId kind) (other : LocalId otherKind) (different : other.tagged ≠ id.tagged) :
    (store.erase id).lookup other = store.lookup other :=
  Proofs.Machine.SQLite.GlobalState.IndexedStore.lookup_erase_of_ne store id other different

theorem mem_taggedKeys_iff (store : IndexedStore) (id : TaggedId) :
    id ∈ store.taggedKeys ↔ (store.lookup id.localId).isSome :=
  Proofs.Machine.SQLite.GlobalState.IndexedStore.mem_taggedKeys_iff store id

/-- Erasing fields preserves precisely the kinds at the tagged local IDs. -/
theorem lookup_erasePayloads (store : IndexedStore) (id : TaggedId) :
    store.erasePayloads.lookup id = (store.lookup id.localId).map (fun _ => id.kind) :=
  Proofs.Machine.SQLite.GlobalState.IndexedStore.lookup_erasePayloads store id

/-- A classified ID in the kind store recovers a payload through the original
indexed store, at the kind in the tag. -/
theorem hasKind_erasePayloads_iff (store : IndexedStore) (id : TaggedId) (kind : ObjectKind) :
    store.erasePayloads.HasKind id kind ↔
      id.kind = kind ∧ ∃ fields, store.lookup id.localId = some fields :=
  Proofs.Machine.SQLite.GlobalState.IndexedStore.hasKind_erasePayloads_iff store id kind

theorem erasePayloads_insert (store : IndexedStore) {kind : ObjectKind} (id : LocalId kind)
    (fields : LocalFields kind) :
    (store.insert id fields).erasePayloads = store.erasePayloads.insert id.tagged kind :=
  Proofs.Machine.SQLite.GlobalState.IndexedStore.erasePayloads_insert store id fields

theorem erasePayloads_erase (store : IndexedStore) {kind : ObjectKind} (id : LocalId kind) :
    (store.erase id).erasePayloads = store.erasePayloads.erase id.tagged :=
  Proofs.Machine.SQLite.GlobalState.IndexedStore.erasePayloads_erase store id

end Silmaril.Machine.SQLite.GlobalState.IndexedStore
