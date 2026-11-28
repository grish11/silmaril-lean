module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Deletion

open Silmaril.Languages.Starlark.Lists (Heap Value)
open Silmaril.Languages.Starlark.Lists.GoDictionary (Row)
open Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion
open Silmaril.Languages.Starlark.Lists.GoDictionary.Growth (Width)

theorem empty_wellFormed (width : Width) : WellFormed (Table.emptyAt width) := by
  constructor <;> simp [Table.emptyAt]

theorem candidate_mem (table : Table) (hash : UInt32) (address : Address) (row : Row) :
    (address, row) ∈ table.candidates hash ↔
      address.home = table.width.home hash ∧ address.slot < table.extent address.home ∧
      table.cells address = some row ∧ row.hash = hash := by
  constructor
  · intro mem
    obtain ⟨index, inRange, ran⟩ := List.mem_filterMap.mp mem
    cases read : table.cells ⟨table.width.home hash, index⟩ with
    | none => simp [Table.candidate, read] at ran
    | some found =>
      by_cases same : found.hash = hash
      · simp [Table.candidate, read, same] at ran
        obtain ⟨rfl, rfl⟩ := ran
        exact ⟨rfl, List.mem_range.mp inRange, read, same⟩
      · simp [Table.candidate, read, same] at ran
  · rintro ⟨home, bound, read, same⟩
    rcases address with ⟨bucket, index⟩
    change bucket = _ at home
    subst bucket
    exact List.mem_filterMap.mpr ⟨index, List.mem_range.mpr bound, by simp [Table.candidate, read, same]⟩

private theorem candidate_index (table : Table) (hash : UInt32) (index : Nat) (item : Address × Row)
    (ran : table.candidate hash index = some item) : item.1.slot = index := by
  cases read : table.cells ⟨table.width.home hash, index⟩ with
  | none => simp [Table.candidate, read] at ran
  | some row =>
    by_cases same : row.hash = hash
    · have eq : (⟨table.width.home hash, index⟩, row) = item := by
        simpa [Table.candidate, read, same] using ran
      rw [← eq]
    · simp [Table.candidate, read, same] at ran

theorem candidates_ordered (table : Table) (hash : UInt32) :
    (table.candidates hash).Pairwise (fun first later => first.1.slot < later.1.slot) := by
  unfold Table.candidates
  apply List.pairwise_filterMap.mpr
  exact List.pairwise_lt_range.imp fun {a b} lt left ha right hb => by
    rw [candidate_index table hash a left ha, candidate_index table hash b right hb]
    exact lt

private theorem filterMap_eq_of_mem {α β : Type} {f g : α → Option β} {items : List α}
    (agree : ∀ item ∈ items, f item = g item) : items.filterMap f = items.filterMap g := by
  induction items with
  | nil => rfl
  | cons item later ih =>
    rw [List.filterMap_cons, List.filterMap_cons, agree item (List.mem_cons_self ..),
      ih (fun other mem => agree other (List.mem_cons_of_mem _ mem))]

theorem unlink_candidates (table : Table) (address : Address) (hash : UInt32) :
    (table.unlink address).candidates hash =
      (table.candidates hash).filter (fun item => item.1 != address) := by
  simp only [Table.candidates, Table.unlink, Table.write, List.filter_filterMap]
  apply filterMap_eq_of_mem
  intro index _
  by_cases same : (⟨table.width.home hash, index⟩ : Address) = address
  · subst address
    cases read : table.cells ⟨table.width.home hash, index⟩ with
    | none => simp [Table.candidate, read]
    | some row => by_cases picked : row.hash = hash <;> simp [Table.candidate, read, picked, Option.filter]
  · cases read : table.cells ⟨table.width.home hash, index⟩ with
    | none => simp [Table.candidate, same, read]
    | some row => by_cases picked : row.hash = hash <;> simp [Table.candidate, same, read, picked, Option.filter]


theorem unlink_entries (table : Table) (address : Address) (wf : WellFormed table) :
    (table.unlink address).entries = (table.order.erase address).filterMap table.cells := by
  simp only [Table.unlink, Table.entries, Table.write]
  apply filterMap_eq_of_mem
  intro other mem
  exact ite_eq_right ((wf.unique.mem_erase_iff.mp mem).1)

theorem unlink_wellFormed (table : Table) (address : Address) (wf : WellFormed table) :
    WellFormed (table.unlink address) := by
  refine ⟨wf.unique.erase address, ?_, ?_, Nat.le_trans (List.erase_sublist ..).length_le wf.bounded⟩
  · intro other
    by_cases same : other = address
    · subst other
      simp [Table.unlink, Table.write, wf.unique.not_mem_erase]
    · simpa [Table.unlink, Table.write, same] using wf.linked other
  · intro other row read
    by_cases same : other = address
    · simp [Table.unlink, Table.write, same] at read
    · exact wf.placed other row (by simpa [Table.unlink, Table.write, same] using read)

private theorem lastVacant_some {empty : Nat → Bool} {size index : Nat}
    (chosen : lastVacant empty size = some index) :
    index < size ∧ empty index ∧ ∀ other, other < size → empty other → other ≤ index := by
  induction size with
  | zero => simp [lastVacant] at chosen
  | succ size ih =>
    by_cases found : empty size
    · have eq : size = index := by simpa [lastVacant, found] using chosen
      subst index
      exact ⟨by omega, found, by omega⟩
    · obtain ⟨bound, vacant, last⟩ := ih (by simpa [lastVacant, found] using chosen)
      refine ⟨by omega, vacant, fun other fits hole => last other ?_ hole⟩
      have ne : other ≠ size := fun same => found (same ▸ hole)
      omega

private theorem lastVacant_none {empty : Nat → Bool} {size : Nat}
    (missing : lastVacant empty size = none) : ∀ index, index < size → ¬ empty index := by
  induction size with
  | zero => omega
  | succ size ih =>
    by_cases found : empty size
    · simp [lastVacant, found] at missing
    · intro index fits vacant
      by_cases same : index = size
      · exact found (same ▸ vacant)
      · exact ih (by simpa [lastVacant, found] using missing) index (by omega) vacant

theorem vacancy_some (table : Table) (home index : Nat) (chosen : table.vacancy home = some index) :
    index < table.extent home ∧ table.cells ⟨home, index⟩ = none ∧
      ∀ other, other < table.extent home → table.cells ⟨home, other⟩ = none → other ≤ index := by
  simpa [Option.isNone_iff_eq_none] using lastVacant_some chosen

theorem vacancy_none (table : Table) (home : Nat) (missing : table.vacancy home = none) :
    ∀ index, index < table.extent home → (table.cells ⟨home, index⟩).isSome := by
  simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] using lastVacant_none missing

private theorem link_wellFormed (table : Table) (address : Address) (row : Row)
    (wf : WellFormed table) (free : table.cells address = none)
    (fits : address.slot < table.extent address.home) (home : address.home = table.width.home row.hash)
    (room : table.order.length < table.width.limit) : WellFormed (table.link address row) := by
  have absent : address ∉ table.order := by simp [wf.linked, free]
  constructor
  · refine List.nodup_append.mpr ⟨wf.unique, by simp, ?_⟩
    intro other mem new selected same
    have eq := List.mem_singleton.mp selected
    exact absent ((same.trans eq) ▸ mem)
  · intro other
    by_cases same : other = address <;>
      simp [Table.link, Table.write, same, wf.linked]
  · intro other found read
    by_cases same : other = address
    · subst other
      have eq : row = found := by simpa [Table.link, Table.write] using read
      subst found
      exact ⟨fits, home⟩
    · exact wf.placed other found (by simpa [Table.link, Table.write, same] using read)
  · simpa [Table.link, Table.write] using Nat.succ_le_of_lt room

private theorem extend_wellFormed (table : Table) (home : Nat) (wf : WellFormed table) :
    WellFormed (table.extend home) := by
  refine ⟨wf.unique, wf.linked, ?_, wf.bounded⟩
  intro address row read
  obtain ⟨fits, belongs⟩ := wf.placed address row read
  refine ⟨?_, belongs⟩
  by_cases same : address.home = home <;> simp [Table.extent, Table.extend, same] at fits ⊢ <;> omega

private theorem free_at_extent (table : Table) (home : Nat) (wf : WellFormed table) :
    table.cells ⟨home, table.extent home⟩ = none := by
  cases read : table.cells ⟨home, table.extent home⟩ with
  | none => rfl
  | some entry => exact (Nat.lt_irrefl _ (wf.placed _ entry read).1).elim

theorem append_wellFormed (table : Table) (row : Row) (wf : WellFormed table)
    (room : table.order.length < table.width.limit) :
    WellFormed (table.append row) := by
  let home := table.width.home row.hash
  cases vacant : table.vacancy home with
  | some index =>
    obtain ⟨fits, free, _⟩ := vacancy_some table home index vacant
    simpa only [Table.append, ← show home = table.width.home row.hash from rfl, vacant] using
      link_wellFormed table ⟨home, index⟩ row wf free fits rfl room
  | none =>
    have free := free_at_extent table home wf
    have fits : table.extent home < (table.extend home).extent home := by
      simp [Table.extent, Table.extend]
    simpa only [Table.append, ← show home = table.width.home row.hash from rfl, vacant] using
      link_wellFormed (table.extend home) ⟨home, table.extent home⟩ row
        (extend_wellFormed table home wf) free fits rfl room

theorem replace_wellFormed (table : Table) (address : Address) (row : Row) (value : Value)
    (wf : WellFormed table) (live : table.cells address = some row) :
    WellFormed (table.replace (address, row) value) := by
  refine ⟨wf.unique, ?_, ?_, wf.bounded⟩
  · intro other
    by_cases same : other = address <;>
      simp [Table.replace, Table.write, same, wf.linked, live]
  · intro other found read
    by_cases same : other = address
    · subst other
      have eq : { row with value := value } = found := by simpa [Table.replace, Table.write] using read
      subst found
      exact wf.placed address row live
    · exact wf.placed other found (by simpa [Table.replace, Table.write, same] using read)

theorem unlink_survivors (table : Table) (address : Address) (wf : WellFormed table) :
    List.Sublist (table.unlink address).entries table.entries := by
  rw [unlink_entries table address wf]
  exact (List.erase_sublist ..).filterMap _

private theorem link_entries (table : Table) (address : Address) (row : Row)
    (wf : WellFormed table) (free : table.cells address = none) :
    (table.link address row).entries = table.entries ++ [row] := by
  simp [Table.link, Table.entries, Table.write, List.filterMap_append]
  apply filterMap_eq_of_mem
  intro other mem
  have absent : address ∉ table.order := by simp [wf.linked, free]
  exact ite_eq_right (show other ≠ address from fun same => absent (same ▸ mem))

theorem append_entries (table : Table) (row : Row) (wf : WellFormed table) :
    (table.append row).entries = table.entries ++ [row] := by
  let home := table.width.home row.hash
  cases vacant : table.vacancy home with
  | some index =>
    simpa only [Table.append, ← show home = table.width.home row.hash from rfl, vacant] using
      link_entries table ⟨home, index⟩ row wf (vacancy_some table home index vacant).2.1
  | none =>
    have free := free_at_extent table home wf
    have entries : (table.extend home).entries = table.entries := rfl
    simpa only [Table.append, ← show home = table.width.home row.hash from rfl, vacant, entries] using
      link_entries (table.extend home) ⟨home, table.extent home⟩ row (extend_wellFormed table home wf) free

theorem append_width (table : Table) (row : Row) :
    (table.append row).width = table.width := by
  cases vacant : table.vacancy (table.width.home row.hash) <;> simp [Table.append, vacant, Table.link, Table.write, Table.extend]

theorem append_length (table : Table) (row : Row) :
    (table.append row).order.length = table.order.length + 1 := by
  cases vacant : table.vacancy (table.width.home row.hash) <;>
    simp [Table.append, vacant, Table.link, Table.extend, Table.write]

theorem replace_keys (table : Table) (address : Address) (row : Row) (value : Value)
    (live : table.cells address = some row) :
    (table.replace (address, row) value).entries.map (fun item => (item.hash, item.key)) =
      table.entries.map (fun item => (item.hash, item.key)) := by
  simp only [Table.replace, Table.write, Table.entries, List.map_filterMap]
  apply filterMap_eq_of_mem
  intro other _
  by_cases same : other = address <;> simp [same, live]

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Deletion
