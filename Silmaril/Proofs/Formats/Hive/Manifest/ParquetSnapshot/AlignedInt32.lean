module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.AlignedInt32.Defs
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Rows.Thms
import all Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Rows.Defs
import all Silmaril.Formats.Parquet.Snapshot.Defs
import Silmaril.Formats.Parquet.Reader.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.Manifest.AlignedInt32
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema partitionCells)

variable {Failure : Type} {target : Scan.Schema String Unit} {partitions : PartitionSchema Unit}

private theorem alignDecode_eq (wire : WireBinding Failure) (snapshot : Snapshot.Checked)
    (index : Nat) (group : Footer.RowGroup) :
    alignDecode target wire snapshot index group =
      (wire.decode snapshot index group).map (List.map (referenceRow target wire.names)) := by
  have alignRow :
      (fun (row : Scan.Row (wireSchema wire.names) Cell) (i : Fin target.width) =>
        ((Vector.ofFn fun j : Fin target.width => wireSlot wire.names (target.kind j).1).get i).bind
          (fun slot => row slot)) =
        referenceRow target wire.names := by
    funext row i
    change ((Vector.ofFn fun j : Fin target.width => wireSlot wire.names (target.kind j).1)[i.val]).bind (fun slot => row slot) = _
    rw [Vector.getElem_ofFn]
    simp only [referenceRow, List.head?_filter, wireSlot]
    cases (List.finRange wire.names.length).find? (fun slot => wire.names.get slot == (target.kind i).1) <;> rfl
  exact congrArg (fun align => (wire.decode snapshot index group).map (List.map align)) alignRow

/-- Neither the declared group length check nor an error depends on aligned columns. -/
theorem readGroup_alignDecode (wire : WireBinding Failure) (snapshot : Snapshot.Checked) (index : Nat) :
    snapshot.readGroup (alignDecode target wire) index =
      (snapshot.readGroup wire.decode index).map (List.map (referenceRow target wire.names)) := by
  cases found : snapshot.groupAt index with
  | none => simp [Snapshot.Checked.readGroup, found, Except.map]
  | some group =>
    simp only [Snapshot.Checked.readGroup, found, alignDecode_eq]
    cases decoded : wire.decode snapshot index group with
    | error error => rfl
    | ok rows =>
      by_cases count : rows.length = group.numRows.toNat <;> simp [Except.map, count]

private theorem denoteGroups_alignDecode (wire : WireBinding Failure) (snapshot : Snapshot.Checked)
    (indices : List Nat) :
    Reader.denoteGroups (snapshot.readGroup (alignDecode target wire)) indices =
      let wireGroups := Reader.denoteGroups (snapshot.readGroup wire.decode) indices
      (wireGroups.1.map (List.map (referenceRow target wire.names)), wireGroups.2) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp only [Reader.denoteGroups, readGroup_alignDecode, ih]
    cases decoded : snapshot.readGroup wire.decode index <;> rfl

theorem readAll_alignDecode (wire : WireBinding Failure) (snapshot : Snapshot.Checked) :
    snapshot.readAll (alignDecode target wire) =
      let wireGroups := Reader.denoteGroups (snapshot.readGroup wire.decode) (List.range snapshot.groupCount)
      .ok ⟨target, ⟨wireGroups.1.map (fun rows => AlignedColumns.ofRows
        (rows.map (referenceRow target wire.names))), wireGroups.2⟩⟩ := by
  rw [Snapshot.Checked.readAll, Reader.readAll_opened]
  simp only [Snapshot.Checked.source, denoteGroups_alignDecode, List.map_map, Function.comp_def]

private theorem denoteSnapshotFileRows_eq (limits : Snapshot.FlatInt32.Limits)
    (lookup : String → Except Failure Bytes) (allowMissing : AllowMissing target)
    (file : File partitions Cell) :
    denoteSnapshotFileRows limits.snapshot
      (fun path => (lookup path).mapError Error.lookup) (bind limits target allowMissing partitions) file =
      denoteFileRows limits lookup allowMissing file := by
  cases found : lookup file.path.declared with
  | error error =>
    simp only [denoteSnapshotFileRows, denoteFileRows, found, Except.mapError]
  | ok bytes =>
    simp only [denoteSnapshotFileRows, denoteFileRows, found, Except.mapError, Snapshot.openSource]
    cases checked : Snapshot.check (Failure := Error Failure) limits.snapshot bytes with
    | error error => rfl
    | ok snapshot =>
      simp only [AlignedInt32.bind]
      cases bound : bindWire (Failure := Failure) limits target allowMissing partitions snapshot.metadata with
      | error error => rfl
      | ok wire =>
        simp only [Except.map, Snapshot.Checked.source, denoteGroups_alignDecode, List.map_flatten,
          List.map_map, Function.comp_def]
        cases (Reader.denoteGroups (snapshot.readGroup wire.decode) (List.range snapshot.groupCount)).2 <;> rfl

private theorem denoteSnapshotRows_eq (limits : Snapshot.FlatInt32.Limits)
    (lookup : String → Except Failure Bytes) (allowMissing : AllowMissing target)
    (files : List (File partitions Cell)) :
    denoteSnapshotRows limits.snapshot
      (fun path => (lookup path).mapError Error.lookup) (bind limits target allowMissing partitions) files =
      denoteRows limits lookup allowMissing files := by
  induction files with
  | nil => rfl
  | cons file rest ih =>
    simp only [denoteSnapshotRows, denoteRows, denoteSnapshotFileRows_eq, ih]
    cases (denoteFileRows limits lookup allowMissing file).2 <;> rfl

theorem scanAlignedInt32Snapshots_collect_eq_rows (limits : Snapshot.FlatInt32.Limits)
    (lookup : String → Except Failure Bytes) (allowMissing : AllowMissing target)
    (projection : Scan.Projection (partitions.extend target))
    (predicate : Scan.Predicate partitions.toScan Cell) (files : List (File partitions Cell)) :
    (scan (alignedInt32SnapshotOpener limits partitions allowMissing lookup) projection predicate files).collect =
      let observed := denoteRows limits lookup allowMissing files
      ⟨⟨projection.schema, projection.scan (fun row => predicate (partitionCells row)) observed.1⟩,
        observed.2⟩ := by
  rw [alignedInt32SnapshotOpener, scanSnapshots_collect_eq_rows, denoteSnapshotRows_eq]

end Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot
