module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion.Defs
import Silmaril.Languages.Starlark.Lists.GoDictionary.Growth.Thms
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.Layout
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.Agreement

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Deletion

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Lists (Heap)
open Silmaril.Languages.Starlark.Lists.GoDictionary (Row hashKey storedHash)
open Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion
open Silmaril.Languages.Starlark.Lists.GoDictionary.Growth (Width Replayable Reinserts)

theorem delete_replayable (heap : Heap) (table next : Table) (key : Lists.Value) (removed : Option Lists.Value)
    (wf : WellFormed table) (valid : Replayable heap table.entries)
    (ran : delete heap table key = .ok (removed, next)) :
    Replayable heap next.entries :=
  Languages.Starlark.Lists.GoDictionary.Growth.replayable_sublist heap valid (delete_survivors heap table next key removed wf ran).2

private theorem append_all (table : Table) (rows : List Row) (wf : WellFormed table)
    (bound : table.order.length + rows.length ≤ table.width.limit) :
    let next := rows.foldl Table.append table
    next.width = table.width ∧ next.entries = table.entries ++ rows ∧ WellFormed next := by
  induction rows generalizing table with
  | nil => simp [wf]
  | cons row remaining ih =>
    have room : table.order.length < table.width.limit := by
      simp only [List.length_cons] at bound
      omega
    have next := ih (table.append row) (append_wellFormed table row wf room) (by
      rw [append_length, append_width]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using bound)
    simpa only [List.foldl_cons, append_width, append_entries table row wf,
      List.append_assoc, List.singleton_append] using next

theorem grow_wellFormed (table : Table) (wf : WellFormed table) :
    table.grow.width = table.width.double ∧ table.grow.entries = table.entries ∧ WellFormed table.grow := by
  have smaller := List.length_filterMap_le table.cells table.order
  have bound := Nat.le_trans (Nat.le_trans smaller wf.bounded) (Nat.le_of_lt table.width.limit_lt_double)
  simpa only [Table.grow, Table.emptyAt, Table.entries, List.filterMap_nil, List.nil_append] using
    append_all (Table.emptyAt table.width.double) table.entries (empty_wellFormed _) (by
      simpa only [Table.emptyAt, Table.entries, List.length_nil, Nat.zero_add] using bound)

private theorem entries_length (table : Table) (wf : WellFormed table) :
    table.entries.length = table.order.length := by
  have full : table.order.filter (fun address => (table.cells address).isSome) = table.order :=
    List.filter_eq_self.mpr fun address mem => (wf.linked address).mp mem
  have lengths := congrArg List.length
    (List.map_filterMap_some_eq_filter_map_isSome (f := table.cells) (l := table.order))
  simp only [List.filter_map, List.length_map] at lengths
  change table.entries.length = (table.order.filter (fun address => (table.cells address).isSome)).length at lengths
  rwa [full] at lengths

private theorem replay_steps (heap : Heap) (width : Width) (earlier remaining : List Row)
    (steps : Reinserts heap width earlier remaining) (table : Table) (wf : WellFormed table)
    (sameWidth : table.width = width) (sameRows : table.entries = earlier) :
    remaining.foldlM (fun current row =>
      Languages.Starlark.Lists.GoDictionary.Deletion.set heap current row.key row.value) table =
    .ok (remaining.foldl Table.append table) := by
  induction steps generalizing table with
  | done => rfl
  | @next prefixRows row later word hashed stored missed room _ ih =>
    have enough : table.order.length < table.width.limit := by
      rw [← entries_length table wf, sameWidth, sameRows]
      exact room
    have raw : probeTable heap table row.key row.hash = .ok none :=
      (probe_miss heap table row.key row.hash wf).mpr
        (sameRows ▸ (Languages.Starlark.Lists.GoDictionary.Growth.probe_miss ..).mp missed)
    have read : lookupWithHash heap table row.key = .ok (row.hash, none) := by
      simp [lookupWithHash, hashed, stored, bind, Except.bind, pure, Except.pure, raw]
    have write : Languages.Starlark.Lists.GoDictionary.Deletion.set heap table row.key row.value =
        .ok (table.append row) := by
      unfold Languages.Starlark.Lists.GoDictionary.Deletion.set
      rw [read]
      cases row
      simp [bind, Except.bind, enough, pure, Except.pure]
    rw [List.foldlM_cons, write, List.foldl_cons]
    change _ = _
    exact ih (table.append row) (append_wellFormed table row wf enough)
      ((append_width ..).trans sameWidth) (by rw [append_entries table row wf, sameRows])

theorem grow_replay (heap : Heap) (table : Table) (wf : WellFormed table)
    (valid : Replayable heap table.entries) :
    table.entries.foldlM (fun current row =>
      Languages.Starlark.Lists.GoDictionary.Deletion.set heap current row.key row.value)
      (Table.emptyAt table.width.double) = .ok table.grow := by
  have prior := Languages.Starlark.Lists.GoDictionary.Growth.reinserts_of_replayable heap table.width [] table.entries valid
    (by simpa [entries_length table wf] using wf.bounded)
  exact replay_steps heap table.width.double [] table.entries
    (Languages.Starlark.Lists.GoDictionary.Growth.reinserts_double heap table.width [] table.entries prior)
    _ (empty_wellFormed _) rfl rfl

theorem set_grows (heap : Heap) (table : Table) (key value : Lists.Value) (hash : UInt32)
    (wf : WellFormed table)
    (full : table.width.limit ≤ table.order.length)
    (missing : lookupWithHash heap table key = .ok (hash, none)) :
    Languages.Starlark.Lists.GoDictionary.Deletion.set heap table key value =
      .ok (table.grow.append ⟨hash, key, value⟩) := by
  obtain ⟨_, _, _, probed⟩ := lookup_miss_parts heap table key hash missing
  have ⟨_, entries, nextWf⟩ := grow_wellFormed table wf
  have same : probeTable heap table.grow key hash = .ok none := by
    apply (probe_miss heap table.grow key hash nextWf).mpr
    rw [entries]
    exact (probe_miss heap table key hash wf).mp probed
  unfold Languages.Starlark.Lists.GoDictionary.Deletion.set
  rw [missing]
  simp [bind, Except.bind, Nat.not_lt.mpr full, same, pure, Except.pure]

theorem set_valid (heap : Heap) (table next : Table) (key value : Lists.Value)
    (wf : WellFormed table) (valid : Replayable heap table.entries)
    (ran : Languages.Starlark.Lists.GoDictionary.Deletion.set heap table key value = .ok next) :
    WellFormed next ∧ Replayable heap next.entries := by
  cases found : lookupWithHash heap table key with
  | error error => simp [Languages.Starlark.Lists.GoDictionary.Deletion.set, found, bind, Except.bind] at ran
  | ok data =>
    obtain ⟨hash, hit⟩ := data
    cases hit with
    | some item =>
      obtain ⟨address, row⟩ := item
      have live := lookup_hit_cell heap table key hash address row found
      simp [Languages.Starlark.Lists.GoDictionary.Deletion.set, found, bind, Except.bind, pure, Except.pure] at ran
      subst next
      refine ⟨replace_wellFormed table address row value wf live, ?_⟩
      unfold Replayable at valid ⊢
      rw [replace_keys table address row value live]
      exact valid
    | none =>
      obtain ⟨word, hashed, stored, probed⟩ := lookup_miss_parts heap table key hash found
      let row : Row := ⟨hash, key, value⟩
      have after : Replayable heap (table.entries ++ [row]) :=
        Languages.Starlark.Lists.GoDictionary.Growth.replayable_append heap table.entries row word valid hashed stored
          ((probe_miss heap table key hash wf).mp probed)
      by_cases room : table.order.length < table.width.limit
      · simp [Languages.Starlark.Lists.GoDictionary.Deletion.set, found, bind, Except.bind,
          pure, Except.pure, room] at ran
        subst next
        refine ⟨append_wellFormed table row wf room, ?_⟩
        rwa [append_entries table row wf]
      · rw [set_grows heap table key value hash wf (Nat.not_lt.mp room) found, Except.ok.injEq] at ran
        subst next
        obtain ⟨wide, entries, nextWf⟩ := grow_wellFormed table wf
        have enough : table.grow.order.length < table.grow.width.limit := by
          rw [← entries_length table.grow nextWf, entries, entries_length table wf, wide]
          exact Nat.lt_of_le_of_lt wf.bounded table.width.limit_lt_double
        refine ⟨append_wellFormed table.grow row nextWf enough, ?_⟩
        rwa [append_entries table.grow row nextWf, entries]

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Deletion
