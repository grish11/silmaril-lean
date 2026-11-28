module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary

open Silmaril.Languages.Starlark.Lists.GoDictionary
open Silmaril.Languages.Starlark.Lists (Heap Value)

theorem slot_count (bucket : Bucket) : bucket.slots.length = 8 := by
  have := bucket.bounded
  simp only [Bucket.slots, List.length_append, List.length_map, List.length_replicate]
  omega

theorem insert_slots (bucket : Bucket) (row : Row) (room : bucket.rows.length < 8) :
    (bucket.insert row room).slots = bucket.slots.set (7 - bucket.rows.length) (some row) := by
  let slot := 7 - bucket.rows.length
  have vacant : 8 - bucket.rows.length = slot + 1 := by dsimp [slot]; omega
  have remains : 8 - (bucket.rows.length + 1) = slot := by dsimp [slot]; omega
  simp only [Bucket.slots, Bucket.insert, List.length_cons, List.map_cons, vacant, remains]
  change _ = (List.replicate (slot + 1) none ++ bucket.rows.map some).set slot (some row)
  rw [List.replicate_succ', List.append_assoc, List.set_append_right (h := by simp)]
  simp

theorem replace_slots (bucket : Bucket) (hit : Row × Nat) (value : Value) :
    (bucket.replace hit value).slots =
      bucket.slots.set (8 - bucket.rows.length + hit.2) (some { hit.1 with value }) := by
  simp [Bucket.slots, Bucket.replace, List.set_append_right]

theorem set_hit_slots (heap : Heap) (bucket : Bucket) (key value : Value) (hash : UInt32)
    (hit : Row × Nat) (found : lookupWithHash heap bucket key = .ok (hash, some hit)) :
    (set heap bucket key value).map Bucket.slots = .ok
      (bucket.slots.set (8 - bucket.rows.length + hit.2) (some { hit.1 with value })) := by
  have ran : set heap bucket key value = .ok (bucket.replace hit value) := by
    unfold Silmaril.Languages.Starlark.Lists.GoDictionary.set
    rw [found]
    rfl
  rw [ran]
  exact congrArg Except.ok (replace_slots bucket hit value)

theorem set_miss_slots (heap : Heap) (bucket : Bucket) (key value : Value) (hash : UInt32)
    (missing : lookupWithHash heap bucket key = .ok (hash, none)) (room : bucket.rows.length < 8) :
    (set heap bucket key value).map Bucket.slots = .ok
      (bucket.slots.set (7 - bucket.rows.length) (some ⟨hash, key, value⟩)) := by
  have ran : set heap bucket key value = .ok (bucket.insert ⟨hash, key, value⟩ room) := by
    unfold Silmaril.Languages.Starlark.Lists.GoDictionary.set
    rw [missing]
    change (if h : bucket.rows.length < 8 then Except.ok (bucket.insert ⟨hash, key, value⟩ h)
      else Except.error Error.capacity) = _
    rw [dite_eq_left room]
  rw [ran]
  exact congrArg Except.ok (insert_slots bucket ⟨hash, key, value⟩ room)

theorem replace_keeps_keys (bucket : Bucket) (hit : Row × Nat) (value : Value)
    (present : bucket.rows[hit.2]? = some hit.1) :
    (bucket.replace hit value).rows.map (fun row => (row.hash, row.key)) =
      bucket.rows.map (fun row => (row.hash, row.key)) := by
  obtain ⟨valid, same⟩ := List.getElem?_eq_some_iff.mp present
  have keyAt : (bucket.rows.map (fun row => (row.hash, row.key)))[hit.2]'(by simpa using valid) =
      (hit.1.hash, hit.1.key) := by simp [same]
  simp only [Bucket.replace, List.map_set]
  rw [← keyAt, List.set_getElem_self]

private theorem candidates_zipIdx (rows : List Row) (hash : UInt32) (start : Nat) :
    ((rows.zipIdx start).filter fun item => item.1.hash == hash).map Prod.fst =
      rows.filter fun row => row.hash == hash := by
  induction rows generalizing start with
  | nil => rfl
  | cons row later ih =>
    cases same : row.hash == hash <;> simp [same, ih]

theorem candidates_slots (bucket : Bucket) (hash : UInt32) :
    (bucket.candidates hash).map Prod.fst =
      bucket.slots.filterMap (fun cell => cell.filter fun row => row.hash == hash) := by
  rw [Bucket.candidates, candidates_zipIdx]
  let select : Option Row → Option Row := fun cell => cell.filter fun row => row.hash == hash
  change _ = bucket.slots.filterMap select
  have empty : select none = none := rfl
  simp only [Bucket.slots, List.filterMap_append, List.filterMap_replicate_of_none empty,
    List.nil_append, List.filterMap_map]
  exact congrFun (List.filterMap_eq_filter (p := fun row : Row => row.hash == hash)).symm bucket.rows

theorem probe_hit_mem {α : Type} (test : α → Except Silmaril.Languages.Starlark.Lists.Error Bool)
    (candidates : List α) (hit : α) (found : Silmaril.Languages.Starlark.Lists.Comparison.probe test candidates = .ok (some hit)) :
    hit ∈ candidates := by
  induction candidates with
  | nil => simp [Silmaril.Languages.Starlark.Lists.Comparison.probe] at found
  | cons candidate later ih =>
    cases checked : test candidate with
    | error error => simp [Silmaril.Languages.Starlark.Lists.Comparison.probe, checked] at found
    | ok flag =>
      cases flag
      · exact List.mem_cons_of_mem _ (ih (by simpa [Silmaril.Languages.Starlark.Lists.Comparison.probe, checked] using found))
      · simp [Silmaril.Languages.Starlark.Lists.Comparison.probe, checked] at found
        exact found ▸ List.mem_cons_self ..

theorem lookup_hit_row (heap : Heap) (bucket : Bucket) (key : Value) (hash : UInt32)
    (hit : Row × Nat) (found : lookupWithHash heap bucket key = .ok (hash, some hit)) :
    bucket.rows[hit.2]? = some hit.1 := by
  let test := fun (candidate : Row × Nat) =>
    Silmaril.Languages.Starlark.Lists.Comparison.equalAt heap
      Silmaril.Languages.Starlark.Lists.Comparison.defaultDepth key candidate.1.key
  cases digest : hashKey heap key with
  | error error => simp [lookupWithHash, digest, bind, Except.bind] at found
  | ok word =>
    let candidates := bucket.candidates (storedHash word)
    cases ran : Silmaril.Languages.Starlark.Lists.Comparison.probe test candidates with
    | error error =>
      simp [lookupWithHash, digest, ran, test, candidates, bind, Except.bind, Except.mapError] at found
    | ok picked =>
      have data : (storedHash word, picked) = (hash, some hit) := by
        simpa [lookupWithHash, digest, ran, test, candidates, bind, Except.bind, Except.mapError,
          pure, Except.pure] using found
      rw [(Prod.mk.inj data).2] at ran
      have mem := probe_hit_mem test candidates hit ran
      rcases hit with ⟨row, index⟩
      exact List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp mem).1

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary
