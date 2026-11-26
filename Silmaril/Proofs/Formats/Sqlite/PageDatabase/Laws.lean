module

public import Silmaril.Formats.Sqlite.PageDatabase.Defs
import Silmaril.Semantics.BTreePages.Trace.Thms

public section
namespace Silmaril.Proofs.Formats.Sqlite.PageDatabase

open Silmaril.Semantics Silmaril.Formats.Sqlite.PageDatabase

variable {Key Kind Content : Type} {Cell : Kind → Type}

private theorem lookupList_eq [DecidableEq Key] (key : Key) {Row : Type} (entries : List (Key × Row)) :
    Silmaril.Formats.Sqlite.BTree.Abstract.lookupList key entries = entries.lookup key := by
  induction entries with
  | nil => rfl
  | cons pair _ ih =>
    rcases pair with ⟨k, v⟩
    by_cases h : key = k
    · subst k
      simp [Silmaril.Formats.Sqlite.BTree.Abstract.lookupList, List.lookup]
    · have other : k ≠ key := Ne.symm h
      have cmp : (key == k) = false := Bool.eq_false_iff.mpr fun eq => h (eq_of_beq eq)
      simp [Silmaril.Formats.Sqlite.BTree.Abstract.lookupList, List.lookup, cmp, other, ih]

variable [LinearOrder Key]
variable {n : Nat} {initial final : Page.UndefArray n Content} {trace : ReadWrite.Trace Nat Content}

theorem readModel_get (table : Table Key Kind Cell Content)
    (rep : table.Represents initial) (key : Key) :
    table.readModel.get key = table.tree.lookup? key := by
  change Silmaril.Formats.Sqlite.BTree.Abstract.lookupList key table.tree.entries = table.tree.lookup? key
  rw [lookupList_eq]
  exact (BTree.Node.lookup_eq_entries rep.1.1 key).symm

theorem table_frame {table : Table Key Kind Cell Content}
    (rep : table.Represents initial) (run : trace.Replays (Page.UndefArray.access n Content) initial final)
    (disjoint : ∀ p, table.Footprint p → ¬ trace.Defs p) :
    table.Represents final := by
  apply (BTreePages.represents_congr ?_).mp rep
  intro p inside
  have unchanged := (Page.UndefArray.replays_memory_iff.mpr run).frame
    (Page.mapStore Nat Content).access_frames (disjoint p inside)
  change final.toMemory p = initial.toMemory p at unchanged
  simp only [Page.mapStore, Table.decodedMemory, unchanged]

theorem database_frame {db : Database Key Kind Cell Content}
    (rep : db.Represents initial) (run : trace.Replays (Page.UndefArray.access n Content) initial final)
    (disjoint : ∀ p, db.Footprint p → ¬ trace.Defs p) :
    db.Represents final := by
  refine ⟨rep.1, rep.2.1, fun entry present => ?_⟩
  exact table_frame (rep.2.2 entry present) run (fun p inside => disjoint p ⟨entry, present, inside⟩)

end Silmaril.Proofs.Formats.Sqlite.PageDatabase
