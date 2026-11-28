module

public import Silmaril.Machine.SQLite.GlobalState.Indexed
public import Silmaril.Machine.SQLite.GlobalState.Thms
import Std.Data.ExtTreeMap.Lemmas

public section

namespace Silmaril.Proofs.Machine.SQLite.GlobalState.IndexedStore

open Silmaril.Machine.SQLite.GlobalState

private theorem setMap_self (store : IndexedStore) (kind : ObjectKind)
    (entries : Std.ExtTreeMap Nat (LocalFields kind)) :
    (store.setMap kind entries).byKind kind = entries := by
  simp [IndexedStore.setMap]

theorem lookup_empty {kind : ObjectKind} (id : LocalId kind) :
    IndexedStore.empty.lookup id = none :=
  Std.ExtTreeMap.getElem?_empty

theorem lookup_insert_self (store : IndexedStore) {kind : ObjectKind} (id : LocalId kind)
    (fields : LocalFields kind) : (store.insert id fields).lookup id = some fields := by
  simp only [IndexedStore.lookup, IndexedStore.insert, setMap_self]
  exact Std.ExtTreeMap.getElem?_insert_self

theorem lookup_erase_self (store : IndexedStore) {kind : ObjectKind} (id : LocalId kind) :
    (store.erase id).lookup id = none := by
  simp only [IndexedStore.lookup, IndexedStore.erase, setMap_self]
  exact Std.ExtTreeMap.getElem?_erase_self

theorem lookup_insert_of_ne (store : IndexedStore) {kind otherKind : ObjectKind}
    (id : LocalId kind) (fields : LocalFields kind) (other : LocalId otherKind)
    (different : other.tagged ≠ id.tagged) : (store.insert id fields).lookup other = store.lookup other := by
  by_cases sameKind : kind = otherKind
  · subst otherKind
    have slots : id.slot ≠ other.slot := fun same => different (congrArg (TaggedId.mk kind) same.symm)
    simp only [IndexedStore.lookup, IndexedStore.insert, setMap_self]
    change ((store.byKind kind).insert id.slot fields)[other.slot]? = (store.byKind kind)[other.slot]?
    simp [Std.ExtTreeMap.getElem?_insert, slots]
  · simp [IndexedStore.lookup, IndexedStore.insert, IndexedStore.setMap, sameKind]

theorem lookup_erase_of_ne (store : IndexedStore) {kind otherKind : ObjectKind}
    (id : LocalId kind) (other : LocalId otherKind) (different : other.tagged ≠ id.tagged) :
    (store.erase id).lookup other = store.lookup other := by
  by_cases sameKind : kind = otherKind
  · subst otherKind
    have slots : id.slot ≠ other.slot := fun same => different (congrArg (TaggedId.mk kind) same.symm)
    simp only [IndexedStore.lookup, IndexedStore.erase, setMap_self]
    change ((store.byKind kind).erase id.slot)[other.slot]? = (store.byKind kind)[other.slot]?
    simp [Std.ExtTreeMap.getElem?_erase, slots]
  · simp [IndexedStore.lookup, IndexedStore.erase, IndexedStore.setMap, sameKind]

private theorem lookup_kindsOfKeys (keys : List TaggedId) (id : TaggedId) :
    (IndexedStore.kindsOfKeys keys).lookup id = if id ∈ keys then some id.kind else none := by
  induction keys with
  | nil => simp [IndexedStore.kindsOfKeys]
  | cons key keys ih =>
    change ((IndexedStore.kindsOfKeys keys).insert key key.kind).lookup id = _
    by_cases hit : id = key
    · subst key
      simp
    · simpa [ObjectStore.lookup_insert_of_ne _ hit, hit] using ih

private theorem mem_kinds (kind : ObjectKind) : kind ∈ IndexedStore.kinds := by
  cases kind <;> decide

theorem mem_taggedKeys_iff (store : IndexedStore) (id : TaggedId) :
    id ∈ store.taggedKeys ↔ (store.lookup id.localId).isSome := by
  simp only [IndexedStore.taggedKeys, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨kind, _, slot, member, rfl⟩
    exact Std.ExtTreeMap.mem_iff_isSome_getElem?.mp (Std.ExtTreeMap.mem_keys.mp member)
  · intro present
    refine ⟨id.kind, mem_kinds id.kind, id.slot, ?_, by cases id; rfl⟩
    exact Std.ExtTreeMap.mem_keys.mpr (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr present)

theorem lookup_erasePayloads (store : IndexedStore) (id : TaggedId) :
    store.erasePayloads.lookup id = (store.lookup id.localId).map (fun _ => id.kind) := by
  simp only [IndexedStore.erasePayloads, lookup_kindsOfKeys, mem_taggedKeys_iff]
  cases store.lookup id.localId <;> rfl

theorem hasKind_erasePayloads_iff (store : IndexedStore) (id : TaggedId) (kind : ObjectKind) :
    store.erasePayloads.HasKind id kind ↔
      id.kind = kind ∧ ∃ fields, store.lookup id.localId = some fields := by
  rw [ObjectStore.HasKind, lookup_erasePayloads]
  cases store.lookup id.localId <;> simp

theorem erasePayloads_insert (store : IndexedStore) {kind : ObjectKind} (id : LocalId kind)
    (fields : LocalFields kind) :
    (store.insert id fields).erasePayloads = store.erasePayloads.insert id.tagged kind := by
  apply ObjectStore.ext
  intro query
  by_cases hit : query = id.tagged
  · subst query
    cases id
    simp [lookup_erasePayloads, LocalId.tagged, TaggedId.localId, lookup_insert_self]
  · rw [ObjectStore.lookup_insert_of_ne _ hit, lookup_erasePayloads, lookup_erasePayloads]
    rw [lookup_insert_of_ne store id fields query.localId]
    exact hit

theorem erasePayloads_erase (store : IndexedStore) {kind : ObjectKind} (id : LocalId kind) :
    (store.erase id).erasePayloads = store.erasePayloads.erase id.tagged := by
  apply ObjectStore.ext
  intro query
  by_cases hit : query = id.tagged
  · subst query
    cases id
    simp [lookup_erasePayloads, LocalId.tagged, TaggedId.localId, lookup_erase_self]
  · rw [ObjectStore.lookup_erase_of_ne _ hit, lookup_erasePayloads, lookup_erasePayloads]
    rw [lookup_erase_of_ne store id query.localId]
    exact hit

end Silmaril.Proofs.Machine.SQLite.GlobalState.IndexedStore
