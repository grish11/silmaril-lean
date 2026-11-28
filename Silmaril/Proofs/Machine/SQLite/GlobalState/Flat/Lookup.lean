module

public import Silmaril.Machine.SQLite.GlobalState.Flat.Defs
import Silmaril.Machine.SQLite.GlobalState.StructThms
import Std.Data.DHashMap.Lemmas

public section

namespace Silmaril.Proofs.Machine.SQLite.GlobalState.Flat

open Silmaril.Machine.SQLite.GlobalState

private theorem lookup_ofEntries (entries : List FlatStore.Entry) (id : TaggedId)
    (result : Option (LocalFields id.kind))
    (agrees : ∀ fields, (⟨id, fields⟩ : FlatStore.Entry) ∈ entries ↔ result = some fields) :
    (FlatStore.ofEntries entries).get? id = result := by
  induction entries with
  | nil =>
    cases result with
    | none => exact Std.DHashMap.get?_empty
    | some fields => exact False.elim (List.not_mem_nil ((agrees fields).mpr rfl))
  | cons entry entries ih =>
    obtain ⟨key, fields⟩ := entry
    change ((FlatStore.ofEntries entries).insert key fields).get? id = result
    by_cases same : key = id
    · subst key
      exact Std.DHashMap.get?_insert_self.trans ((agrees fields).mp (List.mem_cons_self ..)).symm
    · rw [Std.DHashMap.get?_insert, dite_eq_right (fun h => same (eq_of_beq h))]
      apply ih
      intro value
      have different : (⟨id, value⟩ : FlatStore.Entry) ≠ ⟨key, fields⟩ :=
        fun h => same (congrArg Sigma.fst h).symm
      simpa [different] using agrees value

private theorem lookup_indexEntries (entries : List FlatStore.Entry) (id : TaggedId) :
    (FlatStore.indexEntries entries).lookup id.localId = (FlatStore.ofEntries entries).get? id := by
  induction entries with
  | nil => simp [FlatStore.indexEntries, FlatStore.ofEntries]
  | cons entry entries ih =>
    obtain ⟨key, fields⟩ := entry
    change ((FlatStore.indexEntries entries).insert key.localId fields).lookup id.localId =
      ((FlatStore.ofEntries entries).insert key fields).get? id
    by_cases same : key = id
    · subst key
      simp
    · rw [IndexedStore.lookup_insert_of_ne _ key.localId fields id.localId (Ne.symm same),
        Std.DHashMap.get?_insert, dite_eq_right (fun h => same (eq_of_beq h))]
      exact ih

private theorem mem_flatEntries_iff (store : IndexedStore) (id : TaggedId)
    (fields : LocalFields id.kind) :
    (⟨id, fields⟩ : FlatStore.Entry) ∈ store.flatEntries ↔ store.lookup id.localId = some fields := by
  simp only [IndexedStore.flatEntries, List.mem_filterMap]
  constructor
  · rintro ⟨key, _, equal⟩
    cases found : store.lookup key.localId with
    | none => simp [found] at equal
    | some value =>
      simp only [found, Option.map_some, Option.some.injEq] at equal
      cases equal
      exact found
  · intro found
    refine ⟨id, (store.mem_taggedKeys_iff id).mpr (Option.isSome_of_eq_some found), ?_⟩
    simp [found]

theorem lookup_toFlat (store : IndexedStore) (id : TaggedId) :
    store.toFlat.get? id = store.lookup id.localId :=
  lookup_ofEntries store.flatEntries id _ (mem_flatEntries_iff store id)

theorem lookup_toIndexed (store : FlatStore) (id : TaggedId) :
    store.toIndexed.lookup id.localId = store.get? id :=
  (lookup_indexEntries store.toList id).trans
    (lookup_ofEntries store.toList id _ (fun _ => Std.DHashMap.mem_toList_iff_get?_eq_some))

end Silmaril.Proofs.Machine.SQLite.GlobalState.Flat
