module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Reopen.Thms

public section

open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile

namespace Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Checked.Canonical

private theorem ordered_strict (snapshot : Snapshot) :
    snapshot.orderedRows.Pairwise (fun a b => a.id.toInt < b.id.toInt) := by
  have sorted : snapshot.orderedRows.Pairwise (fun a b => a.id.toInt ≤ b.id.toInt) := by
    simpa only [Snapshot.orderedRows, decide_eq_true_eq] using
      List.pairwise_mergeSort (le := fun a b : Row => decide (a.id.toInt ≤ b.id.toInt))
        (by intro a b c; simp only [decide_eq_true_eq]; omega)
        (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) snapshot.rows
  have perm : snapshot.orderedRows.Perm snapshot.rows := List.mergeSort_perm _ _
  have distinct : (snapshot.orderedRows.map Row.id).Nodup :=
    (perm.map Row.id).nodup_iff.mpr snapshot.unique
  have distinctRows : snapshot.orderedRows.Pairwise (fun a b => a.id ≠ b.id) :=
    List.pairwise_map.mp distinct
  apply (sorted.and distinctRows).imp
  intro a b ⟨le, different⟩
  have unequal : a.id.toInt ≠ b.id.toInt := fun same => different (Int64.toInt_inj.mp same)
  omega

private theorem ordered_perm {left right : Snapshot} (rows : left.rows.Perm right.rows) :
    left.orderedRows = right.orderedRows := by
  have leftPerm : left.orderedRows.Perm left.rows := List.mergeSort_perm _ _
  have rightPerm : right.orderedRows.Perm right.rows := List.mergeSort_perm _ _
  apply List.Perm.eq_of_pairwise (le := fun a b : Row => a.id.toInt < b.id.toInt)
  · intro a b _ _ forward backward
    exact False.elim (by omega)
  · exact ordered_strict left
  · exact ordered_strict right
  · exact leftPerm.trans (rows.trans rightPerm.symm)

theorem encode_perm {left right : Snapshot} (rows : left.rows.Perm right.rows) :
    WriteProfile.Image.Checked.encode left = WriteProfile.Image.Checked.encode right := by
  rw [WriteProfile.Image.Checked.encode_eq_mapError left,
    WriteProfile.Image.Checked.encode_eq_mapError right]
  unfold WriteProfile.Image.encode WriteProfile.Image.tablePage
  rw [ordered_perm rows]

end Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Checked.Canonical
