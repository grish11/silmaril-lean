module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Growth.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Slots

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth

open Silmaril.Languages.Starlark.Lists.GoDictionary (Error Row hashKey storedHash)
open Silmaril.Languages.Starlark.Lists.GoDictionary.Growth
open Silmaril.Languages.Starlark.Lists (Heap Value)

private theorem occupied_suffix {α : Type} (entries : List α) (n : Nat) :
    ((List.replicate n none ++ entries.map some).filterMap id) = entries := by
  have empty : (id : Option α → Option α) none = none := rfl
  simp [List.filterMap_replicate_of_none empty, List.filterMap_map, Function.comp_def]

private theorem overflow_perm {α : Type} (entries : List α) :
    ((overflowSlots entries).filterMap id).Perm entries := by
  cases entries with
  | nil => simp [overflowSlots]
  | cons first later =>
    rw [overflowSlots, List.filterMap_append, overflowBlock, List.filterMap_cons]
    simp only [id_eq, occupied_suffix, List.cons_append]
    exact .cons first (by
      simpa only [List.take_append_drop] using
        (List.reverse_perm (later.take 7)).append (overflow_perm (later.drop 7)))
termination_by entries.length
decreasing_by simp; omega

theorem slot_order_perm {α : Type} (entries : List α) :
    (slotOrder entries).Perm entries := by
  rw [slotOrder, physicalChain, List.filterMap_append, primarySlots, occupied_suffix]
  simpa only [List.take_append_drop] using
    (List.reverse_perm (entries.take 8)).append (overflow_perm (entries.drop 8))

private theorem primary_size {α : Type} (entries : List α) : (primarySlots entries).length = 8 := by
  simp only [primarySlots, List.length_append, List.length_map, List.length_reverse,
    List.length_replicate, List.length_take]
  omega

private theorem overflow_size {α : Type} (entries : List α) :
    (overflowSlots entries).length = 8 * ((entries.length + 7) / 8) := by
  cases entries with
  | nil => simp [overflowSlots]
  | cons first later =>
    rw [overflowSlots, List.length_append, overflow_size (later.drop 7)]
    simp only [overflowBlock, List.length_cons, List.length_append, List.length_replicate, List.length_map,
      List.length_reverse, List.length_take, List.length_drop]
    omega
termination_by entries.length
decreasing_by simp; omega

theorem chain_size {α : Type} (entries : List α) :
    (physicalChain entries).length = 8 * max 1 ((entries.length + 7) / 8) := by
  rw [physicalChain, List.length_append, primary_size, overflow_size, List.length_drop]
  omega

theorem candidates_slots (table : Table) (hash : UInt32) :
    table.candidates hash = (table.slots hash).filterMap (fun cell =>
      cell.filter fun item => item.1.hash == hash) := by
  rw [Table.candidates, orderedCandidates, Table.slots, Table.homeEntries, slotOrder, List.filter_filterMap]
  rfl

theorem slots_wellFormed (table : Table) (hash : UInt32) :
    ((table.slots hash).filterMap id).Perm (table.homeEntries hash) ∧
    (table.slots hash).length = 8 * max 1 (((table.homeEntries hash).length + 7) / 8) :=
  ⟨slot_order_perm _, chain_size _⟩

theorem home_append (table : Table) (row : Row) (room : table.entries.length < table.width.limit)
    (hash : UInt32) :
    (table.insert row room).homeEntries hash = table.homeEntries hash ++
      (if table.width.home row.hash = table.width.home hash then [(row, table.entries.length)] else []) := by
  by_cases same : table.width.home row.hash = table.width.home hash <;>
    simp [Table.insert, Table.homeEntries, homeRows, List.zipIdx_append, same]

private theorem fill_suffix {α : Type} (entries : List α) (row : α) (slot : Nat) :
    (List.replicate (slot + 1) none ++ entries.map some).set slot (some row) =
      List.replicate slot none ++ some row :: entries.map some := by
  rw [List.replicate_succ', List.append_assoc, List.set_append_right (h := by simp)]
  simp

theorem append_primary {α : Type} (entries : List α) (row : α) (room : entries.length < 8) :
    physicalChain (entries ++ [row]) =
      (physicalChain entries).set (7 - entries.length) (some row) := by
  have before : entries.length ≤ 8 := by omega
  have after : (entries ++ [row]).length ≤ 8 := by simp; omega
  have vacant : 8 - entries.length = (7 - entries.length) + 1 := by omega
  have remaining : 8 - (entries.length + 1) = 7 - entries.length := by omega
  simp only [physicalChain, primarySlots, List.take_of_length_le before, List.take_of_length_le after,
    List.drop_of_length_le before, List.drop_of_length_le after, overflowSlots, List.append_nil,
    List.length_append, List.length_singleton, Nat.add_one, remaining, vacant, List.reverse_append,
    List.reverse_singleton, List.singleton_append, List.map_cons]
  exact (fill_suffix entries.reverse row (7 - entries.length)).symm

private theorem overflow_append {α : Type} (entries : List α) (row : α) :
    overflowSlots (entries ++ [row]) =
      if entries.length % 8 = 0 then overflowSlots entries ++ (some row :: List.replicate 7 none)
      else (overflowSlots entries).set (8 * (entries.length / 8) + (8 - entries.length % 8)) (some row) := by
  cases entries with
  | nil => simp [overflowSlots, overflowBlock]
  | cons first later =>
    simp only [List.cons_append]
    rw [overflowSlots, overflowSlots]
    by_cases full : 7 ≤ later.length
    · rw [List.take_append_of_le_length full, List.drop_append_of_le_length full]
      rw [overflow_append (later.drop 7) row]
      have size : (overflowBlock first (later.take 7)).length = 8 := by
        simp [overflowBlock, List.length_take, Nat.min_eq_left full]
      have rem : (later.drop 7).length % 8 = (first :: later).length % 8 := by
        simp only [List.length_drop, List.length_cons]
        omega
      rw [rem]
      split
      · simp only [List.append_assoc]
      · rw [List.set_append_right (h := by simp only [size, List.length_cons]; omega), size]
        simp only [List.length_drop, List.length_cons]
        congr 2
        omega
    · have before : later.length ≤ 7 := by omega
      have after : (later ++ [row]).length ≤ 7 := by simp; omega
      have vacant : 7 - later.length = (6 - later.length) + 1 := by omega
      have remaining : 7 - (later.length + 1) = 6 - later.length := by omega
      have block : (first :: later).length / 8 = 0 := by simp; omega
      have rem : (first :: later).length % 8 = later.length + 1 := by simp; omega
      have index : 8 - (later.length + 1) = (6 - later.length) + 1 := by omega
      simp only [List.take_of_length_le before, List.take_of_length_le after,
        List.drop_of_length_le before, List.drop_of_length_le after, overflowSlots, List.append_nil,
        overflowBlock, List.length_append, List.length_singleton, vacant, remaining, rem, block,
        Nat.mul_zero, Nat.zero_add, index, List.set_cons_succ, List.reverse_append, List.reverse_singleton]
      rw [fill_suffix]
      simp
termination_by entries.length
decreasing_by simp; omega

theorem append_overflow {α : Type} (entries : List α) (row : α) (full : 8 ≤ entries.length) :
    physicalChain (entries ++ [row]) =
      if entries.length % 8 = 0 then physicalChain entries ++ (some row :: List.replicate 7 none)
      else (physicalChain entries).set (8 * (entries.length / 8) + (8 - entries.length % 8)) (some row) := by
  unfold physicalChain
  simp only [primarySlots, List.take_append_of_le_length full, List.drop_append_of_le_length full]
  rw [overflow_append (entries.drop 8) row]
  have rem : (entries.drop 8).length % 8 = entries.length % 8 := by
    simp only [List.length_drop]
    omega
  rw [rem]
  split
  · simp only [List.append_assoc]
  · have size : (primarySlots entries).length = 8 := primary_size _
    change primarySlots entries ++ _ = (primarySlots entries ++ _).set _ _
    rw [List.set_append_right (h := by rw [size]; omega), size]
    simp only [List.length_drop]
    congr 2
    omega

theorem lookup_hit_row (heap : Heap) (table : Table) (key : Value) (hash : UInt32)
    (hit : Row × Nat) (found : lookupWithHash heap table key = .ok (hash, some hit)) :
    table.entries[hit.2]? = some hit.1 := by
  let test := fun (candidate : Row × Nat) =>
    Languages.Starlark.Lists.Comparison.equalAt heap
      Languages.Starlark.Lists.Comparison.defaultDepth key candidate.1.key
  cases digest : hashKey heap key with
  | error error => simp [lookupWithHash, digest, bind, Except.bind] at found
  | ok word =>
    let candidates := table.candidates (storedHash word)
    cases ran : Languages.Starlark.Lists.Comparison.probe test candidates with
    | error error =>
      dsimp [test, candidates, Table.candidates] at ran
      simp [lookupWithHash, probeTable, probeRows, digest, ran,
        bind, Except.bind, Except.mapError] at found
    | ok picked =>
      have data : (storedHash word, picked) = (hash, some hit) := by
        have checked := ran
        dsimp [test, candidates, Table.candidates] at checked
        simpa [lookupWithHash, probeTable, probeRows, digest, checked,
          bind, Except.bind, Except.mapError, pure, Except.pure] using found
      rw [(Prod.mk.inj data).2] at ran
      have mem := GoDictionary.probe_hit_mem test candidates hit ran
      have home : hit ∈ table.homeEntries (storedHash word) :=
        (slot_order_perm _).mem_iff.mp (List.mem_filter.mp mem).1
      rcases hit with ⟨row, index⟩
      exact List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp home).1

theorem replace_keeps_keys (table : Table) (hit : Row × Nat) (value : Value)
    (present : table.entries[hit.2]? = some hit.1) :
    (table.replace hit value).entries.map (fun row => (row.hash, row.key)) =
      table.entries.map (fun row => (row.hash, row.key)) := by
  obtain ⟨valid, same⟩ := List.getElem?_eq_some_iff.mp present
  have keyAt : (table.entries.map (fun row => (row.hash, row.key)))[hit.2]'(by simpa using valid) =
      (hit.1.hash, hit.1.key) := by simp [same]
  simp only [Table.replace, List.map_set]
  rw [← keyAt, List.set_getElem_self]

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth
