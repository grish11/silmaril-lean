module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Growth.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth.Layout
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth.Rehash

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Lists (Heap)
open Silmaril.Languages.Starlark.Lists.GoDictionary (Row hashKey storedHash)
open Silmaril.Languages.Starlark.Lists.GoDictionary.Growth

private theorem replayable_iff (heap : Heap) (rows : List Row) :
    Replayable heap rows ↔
      (∀ row ∈ rows, ∃ word, hashKey heap row.key = .ok word ∧ storedHash word = row.hash) ∧
      rows.Pairwise (fun earlier later => earlier.hash = later.hash →
        Lists.Comparison.equalAt heap Lists.Comparison.defaultDepth later.key earlier.key = .ok false) := by
  simp only [Replayable, List.forall_mem_map, List.pairwise_map]

theorem empty_replayable (heap : Heap) : Replayable heap Table.empty.entries := by
  simp [Replayable, Table.empty]

theorem reinserts_of_replayable (heap : Heap) (width : Width) (prefixRows remaining : List Row)
    (valid : Replayable heap (prefixRows ++ remaining)) (bound : (prefixRows ++ remaining).length ≤ width.limit) :
    Reinserts heap width prefixRows remaining := by
  induction remaining generalizing prefixRows with
  | nil => exact .done prefixRows
  | cons row later ih =>
    have facts := (replayable_iff ..).mp valid
    obtain ⟨word, hashed, stored⟩ := facts.1 row (List.mem_append_right _ (List.mem_cons_self ..))
    have cross := (List.pairwise_append.mp facts.2).2.2
    have miss := (probe_miss heap width prefixRows row.key row.hash).mpr
      (fun earlier mem same => cross earlier mem row (List.mem_cons_self ..) same)
    have room : prefixRows.length < width.limit := by
      simp only [List.length_append, List.length_cons] at bound
      omega
    refine .next hashed stored miss room (ih (prefixRows ++ [row]) ?_ ?_)
    · simpa only [List.append_assoc, List.singleton_append] using valid
    · simpa only [List.append_assoc, List.singleton_append] using bound

theorem rehash_run (heap : Heap) (table : Table) (valid : Replayable heap table.entries) :
    table.entries.foldlM (fun current row =>
      Languages.Starlark.Lists.GoDictionary.Growth.set heap current row.key row.value)
      (⟨table.width.double, [], by simp⟩ : Table) = .ok table.grow := by
  have original := reinserts_of_replayable heap table.width [] table.entries valid table.bounded
  simpa only [Table.grow, List.nil_append] using reinsert_run heap table.width.double [] table.entries
    (reinserts_double heap table.width [] table.entries original) table.grow.bounded

theorem replayable_sublist (heap : Heap) {rows survivors : List Row}
    (valid : Replayable heap rows) (kept : List.Sublist survivors rows) :
    Replayable heap survivors := by
  obtain ⟨hashed, pairwise⟩ := (replayable_iff ..).mp valid
  exact (replayable_iff ..).mpr ⟨fun row mem => hashed row (kept.mem mem), pairwise.sublist kept⟩

theorem replayable_append (heap : Heap) (rows : List Row) (row : Row) (word : UInt32)
    (valid : Replayable heap rows) (hashed : hashKey heap row.key = .ok word)
    (stored : storedHash word = row.hash)
    (miss : ∀ earlier ∈ rows, earlier.hash = row.hash →
      Lists.Comparison.equalAt heap Lists.Comparison.defaultDepth row.key earlier.key = .ok false) :
    Replayable heap (rows ++ [row]) := by
  have facts := (replayable_iff ..).mp valid
  apply (replayable_iff ..).mpr
  constructor
  · intro item mem
    rcases List.mem_append.mp mem with old | new
    · exact facts.1 item old
    · obtain rfl := List.mem_singleton.mp new
      exact ⟨word, hashed, stored⟩
  · exact List.pairwise_append.mpr ⟨facts.2, List.pairwise_singleton _ _, fun earlier mem item new => by
      obtain rfl := List.mem_singleton.mp new
      exact miss earlier mem⟩

private theorem append_replayable (heap : Heap) (table : Table) (key value : Lists.Value) (hash : UInt32)
    (valid : Replayable heap table.entries)
    (missing : lookupWithHash heap table key = .ok (hash, none)) :
    Replayable heap (table.entries ++ [⟨hash, key, value⟩]) := by
  obtain ⟨word, hashed, stored, probed⟩ := lookup_miss_parts heap table key hash missing
  exact replayable_append heap table.entries ⟨hash, key, value⟩ word valid hashed stored
    ((probe_miss ..).mp probed)

theorem set_replayable (heap : Heap) (table next : Table) (key value : Lists.Value)
    (valid : Replayable heap table.entries)
    (ran : Languages.Starlark.Lists.GoDictionary.Growth.set heap table key value = .ok next) :
    Replayable heap next.entries := by
  cases found : lookupWithHash heap table key with
  | error error => simp [set_error heap table key value error found] at ran
  | ok data =>
    obtain ⟨hash, hit⟩ := data
    cases hit with
    | some item =>
      have present := lookup_hit_row heap table key hash item found
      rw [set_hit heap table key value hash item found, Except.ok.injEq] at ran
      subst next
      unfold Replayable at valid ⊢
      rw [replace_keeps_keys table item value present]
      exact valid
    | none =>
      by_cases room : table.entries.length < table.width.limit
      · unfold Languages.Starlark.Lists.GoDictionary.Growth.set at ran
        rw [found] at ran
        simp only [bind, Except.bind, dite_eq_left room, pure, Except.pure, Except.ok.injEq] at ran
        subst next
        exact append_replayable heap table key value hash valid found
      · rw [set_grow heap table key value hash (Nat.not_lt.mp room) found, Except.ok.injEq] at ran
        subst next
        exact append_replayable heap table key value hash valid found

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth
