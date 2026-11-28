module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction.Defs
import Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion.Thms
import Silmaril.Languages.Starlark.Lists.Comparison.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Lists (State Heap Entry findEntry)
open Silmaril.Languages.Starlark.Lists.GoDictionary (Row hashKey storedHash)
open Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction
open Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion (Table Address WellFormed)

theorem observe_row {profile : KeyProfile} {row : Row} {entry : Entry}
    (observed : observeRow profile row = some entry) :
    ∃ obs, profile row.key = some obs ∧ row.hash = obs.hash ∧
      entry = ⟨row.key, obs.code, row.value⟩ := by
  cases admitted : profile row.key with
  | none => simp [observeRow, admitted] at observed
  | some obs =>
    by_cases good : row.hash = obs.hash
    · exact ⟨obs, rfl, good, (by simpa [observeRow, admitted, good] using observed.symm)⟩
    · simp [observeRow, admitted, good] at observed

theorem observe_cell {profile : KeyProfile} {table : Table} {address : Address} {entry : Entry}
    (observed : observeCell profile table address = some entry) :
    ∃ row, table.cells address = some row ∧ observeRow profile row = some entry := by
  cases read : table.cells address with
  | none => simp [observeCell, read] at observed
  | some row => exact ⟨row, rfl, by simpa [observeCell, read] using observed⟩

private theorem map_observations (profile : KeyProfile) (cells : Address → Option Row)
    (order : List Address) (live : ∀ address ∈ order, (cells address).isSome) :
    order.map (fun address => (cells address).bind (observeRow profile)) =
      (order.filterMap cells).map (observeRow profile) := by
  induction order with
  | nil => rfl
  | cons address rest ih =>
    cases read : cells address with
    | none => exact False.elim (by simpa [read] using live address (List.mem_cons_self ..))
    | some row =>
      simp [read, ih (fun other mem => live other (List.mem_cons_of_mem _ mem))]

theorem ordered_rows (profile : KeyProfile) (table : Table) (wf : WellFormed table) :
    table.order.map (observeCell profile table) = table.entries.map (observeRow profile) :=
  map_observations profile table.cells table.order (fun address mem => (wf.linked address).mp mem)

theorem related_rows (heap : Heap) (profile : KeyProfile) (table : Table) (entries : List Entry)
    (related : Related heap profile table entries) :
    table.entries.map (observeRow profile) = entries.map some :=
  (ordered_rows profile table related.layout).symm.trans related.ordered

theorem ordered_key_values (heap : Heap) (profile : KeyProfile) (table : Table) (entries : List Entry)
    (related : Related heap profile table entries) :
    table.entries.map (fun row => (row.key, row.value)) =
      entries.map (fun entry => (entry.key, entry.value)) := by
  have exactRows := related_rows heap profile table entries related
  generalize table.entries = rows at exactRows ⊢
  clear related table
  induction rows generalizing entries with
  | nil => cases entries <;> simp_all
  | cons row later ih =>
    cases entries with
    | nil => simp at exactRows
    | cons entry rest =>
      obtain ⟨picked, tail⟩ := List.cons.inj exactRows
      obtain ⟨_, _, _, rfl⟩ := observe_row picked
      simp [ih rest tail]

private theorem probe_total {α : Type} (items : List α) (test : α → Except Lists.Error Bool)
    (matching : α → Bool) (total : ∀ item ∈ items, test item = .ok (matching item)) :
    Lists.Comparison.probe test items = .ok (items.find? matching) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    cases decided : matching first
    · simpa only [Lists.Comparison.probe, List.find?_cons, total first (List.mem_cons_self ..),
        decided] using ih (fun item mem => total item (List.mem_cons_of_mem _ mem))
    · simp only [Lists.Comparison.probe, List.find?_cons, total first (List.mem_cons_self ..), decided]

theorem select_entry (heap : Heap) (profile : KeyProfile) (table : Table) (entries : List Entry)
    (key : Lists.Value) (query : KeyObservation) (laws : Coherent heap profile)
    (related : Related heap profile table entries) (admitted : profile key = some query) :
    ∃ picked, Lists.GoDictionary.Deletion.lookupWithHash heap table key = .ok (query.hash, picked) ∧
      match picked with
      | none => findEntry query.code entries = none
      | some (address, row) => ∃ entry,
          findEntry query.code entries = some entry ∧ table.cells address = some row ∧
          observeRow profile row = some entry := by
  let candidates := table.candidates query.hash
  let matching := fun item : Address × Row => (observeRow profile item.2).any (fun entry => query.code == entry.keyCode)
  have observed (address : Address) (row : Row) (mem : (address, row) ∈ candidates) :
      ∃ entry ∈ entries, observeRow profile row = some entry := by
    have read := ((Lists.GoDictionary.Deletion.candidate_mem ..).mp mem).2.2.1
    have linked := (related.layout.linked address).mpr (by simp [read])
    have present := List.mem_map_of_mem (f := observeCell profile table) linked
    rw [related.ordered] at present
    obtain ⟨entry, member, encoded⟩ := List.mem_map.mp present
    exact ⟨entry, member, by simpa [observeCell, read] using encoded.symm⟩
  have checked : Lists.Comparison.probe
      (fun item : Address × Row => Lists.Comparison.equalAt heap Lists.Comparison.defaultDepth key item.2.key)
      candidates = .ok (candidates.find? matching) := by
    apply probe_total
    rintro ⟨address, row⟩ mem
    obtain ⟨entry, _, encoded⟩ := observed address row mem
    obtain ⟨obs, obsOf, rowHash, rfl⟩ := observe_row encoded
    have fullHash := ((Lists.GoDictionary.Deletion.candidate_mem ..).mp mem).2.2.2
    simpa [matching, encoded] using laws.compares key row.key query obs admitted obsOf
      (fullHash.symm.trans rowHash)
  obtain ⟨word, hashed, stored⟩ := laws.hashes key query admitted
  have queried : Lists.GoDictionary.Deletion.lookupWithHash heap table key =
      .ok (query.hash, candidates.find? matching) := by
    simp [Lists.GoDictionary.Deletion.lookupWithHash, hashed, stored,
      Lists.GoDictionary.Deletion.probeTable, ← show candidates = table.candidates query.hash from rfl,
      checked, bind, Except.bind, Except.mapError, pure, Except.pure]
  refine ⟨candidates.find? matching, queried, ?_⟩
  cases found : candidates.find? matching with
  | some item =>
    rcases item with ⟨address, row⟩
    have member := List.mem_of_find?_eq_some found
    obtain ⟨entry, mem, encoded⟩ := observed address row member
    have passed := List.find?_some found
    have eq : query.code = entry.keyCode := by simpa [matching, encoded] using passed
    exact ⟨entry, (Lists.Comparison.findEntry_some_iff_of_unique query.code entries entry related.unique).mpr ⟨mem, eq.symm⟩,
      ((Lists.GoDictionary.Deletion.candidate_mem ..).mp member).2.2.1, encoded⟩
  | none =>
    cases canon : findEntry query.code entries with
    | none => rfl
    | some entry =>
      obtain ⟨mem, sameCode⟩ :=
        (Lists.Comparison.findEntry_some_iff_of_unique query.code entries entry related.unique).mp canon
      have present := List.mem_map_of_mem (f := some) mem
      rw [← related.ordered] at present
      obtain ⟨address, _, encoded⟩ := List.mem_map.mp present
      obtain ⟨row, read, projected⟩ := observe_cell encoded
      obtain ⟨obs, obsOf, rowHash, rfl⟩ := observe_row projected
      have sameHash : row.hash = query.hash :=
        rowHash.trans (laws.sameHash row.key key obs query obsOf admitted sameCode)
      obtain ⟨fits, home⟩ := related.layout.placed address row read
      have member : (address, row) ∈ candidates :=
        (Lists.GoDictionary.Deletion.candidate_mem ..).mpr ⟨sameHash ▸ home, fits, read, sameHash⟩
      have noMatch := List.find?_eq_none.mp found (address, row) member
      exact (noMatch (by simpa [matching, projected] using sameCode.symm)).elim

theorem lookup_agrees (heap : Heap) (profile : KeyProfile) (table : Table) (entries : List Entry)
    (key : Lists.Value) (query : KeyObservation) (laws : Coherent heap profile)
    (related : Related heap profile table entries) (admitted : profile key = some query) :
    lookupEntry heap profile table key = .ok (findEntry query.code entries) := by
  obtain ⟨picked, looked, observation⟩ := select_entry heap profile table entries key query laws related admitted
  cases picked with
  | none => simp [lookupEntry, looked, observation, Except.map]
  | some pair =>
    rcases pair with ⟨address, row⟩
    obtain ⟨entry, found, _, encoded⟩ := observation
    simp [lookupEntry, looked, found, encoded, Except.map]

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction
