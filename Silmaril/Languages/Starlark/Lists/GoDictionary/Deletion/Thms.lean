module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.Layout
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.Agreement
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.Replay

public section

namespace Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion

open Growth (Width Replayable)

/-- Every home starts with an empty primary bucket. -/
theorem empty_wellFormed (width : Width) : WellFormed (Table.emptyAt width) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.empty_wellFormed width

/-- Candidates are the live slots with the full query hash. -/
theorem candidate_mem (table : Table) (hash : UInt32) (address : Address) (row : Row) :
    (address, row) ∈ table.candidates hash ↔
      address.home = table.width.home hash ∧ address.slot < table.extent address.home ∧
      table.cells address = some row ∧ row.hash = hash :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.candidate_mem table hash address row

/-- Candidates follow ascending slot order through the allocated chain. -/
theorem candidates_ordered (table : Table) (hash : UInt32) :
    (table.candidates hash).Pairwise (fun first later => first.1.slot < later.1.slot) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.candidates_ordered table hash

/-- Unlinking removes only that address from the existing candidate order. -/
theorem unlink_candidates (table : Table) (address : Address) (hash : UInt32) :
    (table.unlink address).candidates hash =
      (table.candidates hash).filter (fun item => item.1 != address) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.unlink_candidates table address hash

/-- Survivors retain their addresses, stored rows, and iteration order. -/
theorem unlink_entries (table : Table) (address : Address) (wf : WellFormed table) :
    (table.unlink address).entries = (table.order.erase address).filterMap table.cells :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.unlink_entries table address wf

/-- Independent ordered rules give the same delete result, first error, and reached table. -/
theorem deletes_iff (heap : Heap) (table : Table) (key : Value)
    (out : Except Error (Option Value × Table)) :
    Deletes heap table key out ↔ delete heap table key = out :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.deletes_iff heap table key out

/-- A successful delete preserves slot coherence and retains the surviving chronological subsequence. -/
theorem delete_survivors (heap : Heap) (table next : Table) (key : Value) (removed : Option Value)
    (wf : WellFormed table) (ran : delete heap table key = .ok (removed, next)) :
    WellFormed next ∧ List.Sublist next.entries table.entries :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.delete_survivors heap table next key removed wf ran

/-- The selected vacancy is the last one reached in the forward scan. -/
theorem vacancy_some (table : Table) (home index : Nat) (chosen : table.vacancy home = some index) :
    index < table.extent home ∧ table.cells ⟨home, index⟩ = none ∧
      ∀ other, other < table.extent home → table.cells ⟨home, other⟩ = none → other ≤ index :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.vacancy_some table home index chosen

/-- An overflow block is allocated only when every current slot is occupied. -/
theorem vacancy_none (table : Table) (home : Nat) (missing : table.vacancy home = none) :
    ∀ index, index < table.extent home → (table.cells ⟨home, index⟩).isSome :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.vacancy_none table home missing

/-- Append links the new row at the end, irrespective of its slot. -/
theorem append_entries (table : Table) (row : Row) (wf : WellFormed table) :
    (table.append row).entries = table.entries ++ [row] :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.append_entries table row wf

/-- Replacement preserves every stored key and its iteration position. -/
theorem replace_keys (table : Table) (address : Address) (row : Row) (value : Value)
    (live : table.cells address = some row) :
    (table.replace (address, row) value).entries.map (fun item => (item.hash, item.key)) =
      table.entries.map (fun item => (item.hash, item.key)) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.replace_keys table address row value live

/-- Survivors still satisfy the fixed-heap replay invariant. -/
theorem delete_replayable (heap : Heap) (table next : Table) (key : Value) (removed : Option Value)
    (wf : WellFormed table) (valid : Replayable heap table.entries)
    (ran : delete heap table key = .ok (removed, next)) :
    Replayable heap next.entries :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.delete_replayable heap table next key removed wf valid ran

/-- Growth doubles the width and preserves the ordered rows. -/
theorem grow_wellFormed (table : Table) (wf : WellFormed table) :
    table.grow.width = table.width.double ∧ table.grow.entries = table.entries ∧ WellFormed table.grow :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.grow_wellFormed table wf

/-- Fresh chronological replay reconstructs the exact rehashed table. -/
theorem grow_replay (heap : Heap) (table : Table) (wf : WellFormed table)
    (valid : Replayable heap table.entries) :
    table.entries.foldlM (fun current row =>
      Deletion.set heap current row.key row.value)
      (Table.emptyAt table.width.double) = .ok table.grow :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.grow_replay heap table wf valid

/-- An overloaded miss grows and retries. -/
theorem set_grows (heap : Heap) (table : Table) (key value : Value) (hash : UInt32)
    (wf : WellFormed table)
    (full : table.width.limit ≤ table.order.length)
    (missing : lookupWithHash heap table key = .ok (hash, none)) :
    Deletion.set heap table key value =
      .ok (table.grow.append ⟨hash, key, value⟩) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.set_grows heap table key value hash wf full missing

/-- Successful set preserves the coupled slot and replay invariants. -/
theorem set_valid (heap : Heap) (table next : Table) (key value : Value)
    (wf : WellFormed table) (valid : Replayable heap table.entries)
    (ran : Deletion.set heap table key value = .ok next) :
    WellFormed next ∧ Replayable heap next.entries :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.set_valid heap table next key value wf valid ran

/-- Clearing a slot preserves all other cells. -/
theorem unlink_cells (table : Table) (address other : Address) :
    (table.unlink address).cells other = (if other = address then none else table.cells other) :=
  rfl

theorem unlink_extent (table : Table) (address : Address) (home : Nat) :
    (table.unlink address).extent home = table.extent home := rfl

/-- Reusing a vacancy performs a single slot write and a tail link. -/
theorem append_reuses (table : Table) (row : Row) (index : Nat)
    (chosen : table.vacancy (table.width.home row.hash) = some index) :
    table.append row = table.link ⟨table.width.home row.hash, index⟩ row := by
  simp [Table.append, chosen]

/-- A new overflow block starts at slot zero immediately after the old chain. -/
theorem append_allocates (table : Table) (row : Row)
    (missing : table.vacancy (table.width.home row.hash) = none) :
    table.append row = (table.extend (table.width.home row.hash)).link
      ⟨table.width.home row.hash, table.extent (table.width.home row.hash)⟩ row := by
  simp [Table.append, missing]

end Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion
