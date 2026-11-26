module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Defs
import all Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Defs
import Silmaril.Formats.Hive.ParquetScan.Thms
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Semantics.Relational.Scan.Thms
import Silmaril.Semantics.Relational.Table.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema extendRow)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Failure : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}

private theorem readFile_denote (source : Reader.Source Nat
    (Int32ByteArrayGroup.File.schema int32 byteArray) Value (Int32ByteArray.Error Failure)) :
    ParquetScan.readFile source (source.groups.length + 1) =
      let groups := Reader.denoteGroups source.readGroup source.groups
      ⟨groups.1.map AlignedColumns.ofRows, groups.2⟩ := by
  have read : Reader.readAll (.ok ⟨Int32ByteArrayGroup.File.schema int32 byteArray, source⟩) =
      .ok ⟨Int32ByteArrayGroup.File.schema int32 byteArray,
        ParquetScan.readFile source (source.groups.length + 1)⟩ :=
    ParquetScan.readFile_eq_reader source (source.groups.length + 1)
  have agree := read.symm.trans (Reader.readAll_opened source)
  simpa only [Except.ok.injEq, Sigma.mk.inj_iff, heq_iff_eq, true_and] using agree

private theorem assemble_singleton
    (trace : Events.Trace (Int32ByteArrayGroup.File.schema int32 byteArray) Value (Int32ByteArray.Error Failure)) :
    ParquetScan.assemble id [trace] = trace := by
  cases trace with
  | mk batches termination => cases termination <;> simp [ParquetScan.assemble]

private theorem project_group
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (cells : Scan.Row partitions.toScan Value)
    (rows : Scan.Table (Int32ByteArrayGroup.File.schema int32 byteArray) Value) :
    projection.projectColumns
        (AlignedColumns.ofRows ((AlignedColumns.ofRows rows).toRows.map fun row => extendRow row cells)) =
      AlignedColumns.ofRows (projection.project (rows.map fun row => extendRow row cells)) := by
  apply AlignedColumns.rowsEquiv.symm.injective
  rw [projection.rowsEquiv_projectColumns]
  change projection.project (AlignedColumns.ofRows _).toRows = (AlignedColumns.ofRows _).toRows
  simp only [AlignedColumns.toRows_ofRows]

private theorem scanFile_eq_denote (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (file : File partitions Value) :
    scanFile (int32ByteArraySnapshotOpener limits int32 byteArray partitions lookup) projection keep file =
      denoteInt32ByteArrayFile limits lookup projection keep file := by
  cases opened : Int32ByteArray.openChecked limits int32 byteArray partitions lookup file.path.declared with
  | error reason => simp [scanFile, int32ByteArraySnapshotOpener, denoteInt32ByteArrayFile, opened, Except.map]
  | ok checked =>
    simp only [scanFile, int32ByteArraySnapshotOpener, denoteInt32ByteArrayFile, opened, Except.map,
      readFile_denote, ParquetScan.scanPartition, assemble_singleton]
    simp only [ParquetScan.extendTrace, List.map_map, Function.comp_def, project_group]
    cases (keep file.cells).getD false <;> simp <;>
      cases (Reader.denoteGroups (Int32ByteArray.source checked (Failure := Failure)).readGroup
        (Int32ByteArray.source checked (Failure := Failure)).groups).2 <;> rfl

theorem scanInt32ByteArraySnapshots_eq_reference (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (files : List (File partitions Value)) :
    scan (int32ByteArraySnapshotOpener limits int32 byteArray partitions lookup) projection keep files =
      denoteInt32ByteArraySnapshots limits lookup projection keep files := by
  unfold scan
  induction files with
  | nil => rfl
  | cons file rest ih =>
    simp only [ParquetScan.assemble, denoteInt32ByteArraySnapshots, scanFile_eq_denote, ih]
    cases (denoteInt32ByteArrayFile limits lookup projection keep file).termination <;> rfl

end Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot
