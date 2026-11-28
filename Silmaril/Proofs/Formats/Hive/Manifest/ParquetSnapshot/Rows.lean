module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Rows.Defs
import all Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Rows.Defs
import Silmaril.Formats.Hive.ParquetScan.Thms
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Formats.Arrow.Events.Thms
import Silmaril.Semantics.Relational.Scan.Thms
import Silmaril.Semantics.Relational.Table.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema extendRow partitionCells)

variable {Kind Failure : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

private theorem readFile_rows (source : Reader.Source Nat physical Value (Snapshot.Error Failure)) :
    let trace := ParquetScan.readFile source (source.groups.length + 1)
    let observed := Reader.denoteGroups source.readGroup source.groups
    trace.rows = observed.1.flatten ∧ trace.termination = observed.2 := by
  let trace := ParquetScan.readFile source (source.groups.length + 1)
  let observed := Reader.denoteGroups source.readGroup source.groups
  let model : Events.Trace physical Value (Snapshot.Error Failure) :=
    ⟨observed.1.map AlignedColumns.ofRows, observed.2⟩
  have read : Reader.readAll (.ok ⟨physical, source⟩) = .ok ⟨physical, trace⟩ :=
    ParquetScan.readFile_eq_reader source (source.groups.length + 1)
  have observedTrace : Events.EventStream.Equivalent (.ok ⟨physical, trace⟩) (.ok ⟨physical, model⟩) :=
    congrArg Events.EventStream.collect (read.symm.trans (Reader.readAll_opened source))
  obtain ⟨rows, termination⟩ := Events.EventStream.equivalent_open_iff.mp observedTrace
  refine ⟨?_, termination⟩
  change trace.rows = observed.1.flatten
  simpa only [model, Events.Trace.rows, List.flatMap_map, Function.comp_def,
    AlignedColumns.toRows_ofRows, List.flatMap_id'] using rows

private theorem assemble_singleton (trace : Events.Trace physical Value (Snapshot.Error Failure)) :
    ParquetScan.assemble id [trace] = trace := by
  cases trace with
  | mk batches termination =>
    cases termination <;> simp [ParquetScan.assemble]

private theorem scanFile_rows (limits : Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (file : File schema Value) :
    let actual := scanFile (snapshotOpener limits lookup bind) projection predicate file
    let observed := denoteSnapshotFileRows limits lookup bind file
    actual.rows = projection.scan (fun row => predicate (partitionCells row)) observed.1 ∧
      actual.termination = observed.2 := by
  cases found : lookup file.path.declared with
  | error reason =>
    simp [scanFile, snapshotOpener, found, denoteSnapshotFileRows, Events.Trace.rows]
  | ok bytes =>
    cases opened : Snapshot.openSource limits bind bytes with
    | error reason =>
      simp [scanFile, snapshotOpener, found, opened, Except.map, denoteSnapshotFileRows, Events.Trace.rows]
    | ok source =>
      let trace := ParquetScan.readFile source (source.groups.length + 1)
      let observed := Reader.denoteGroups source.readGroup source.groups
      let part : ParquetScan.Partition physical schema Value (Snapshot.Error Failure) := ⟨file.cells, [trace]⟩
      let result := ParquetScan.scanPartition projection predicate part
      obtain ⟨rows, termination⟩ := readFile_rows source
      have augmentedRows : part.augmented.rows = observed.1.flatten.map (fun row => extendRow row file.cells) := by
        change (ParquetScan.extendTrace (ParquetScan.assemble id [trace]) file.cells).rows = _
        rw [assemble_singleton, ParquetScan.rows_extendTrace, rows]
      have augmentedTerm : part.augmented.termination = observed.2 := by
        change (ParquetScan.assemble id [trace]).termination = _
        rw [assemble_singleton, termination]
      obtain ⟨filtered, ended⟩ := ParquetScan.scanPartition_observation projection predicate part
      simp only [scanFile, snapshotOpener, found, opened, Except.map, denoteSnapshotFileRows]
      constructor
      · change result.rows = _
        rw [filtered, Events.Trace.rows_scan, augmentedRows]
      · rw [ended, Events.Trace.termination_scan, augmentedTerm]
        cases observed.2 <;> rfl

/-- The checked manifest scan observes the independently denoted ordered file
rows with typed partition cells, filtered and projected in row order. The
first terminal outcome retains its path, stage, and exact payload. -/
theorem scanSnapshots_collect_eq_rows (limits : Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (files : List (File schema Value)) :
    (scan (snapshotOpener limits lookup bind) projection predicate files).collect =
      let observed := denoteSnapshotRows limits lookup bind files
      ⟨⟨projection.schema, projection.scan (fun row => predicate (partitionCells row)) observed.1⟩,
        observed.2⟩ := by
  let traceOf := scanFile (snapshotOpener limits lookup bind) projection predicate
  let keep : Scan.Predicate (schema.extend physical) Value := fun row => predicate (partitionCells row)
  have agreement (files : List (File schema Value)) :
      (ParquetScan.assemble traceOf files).rows = projection.scan keep (denoteSnapshotRows limits lookup bind files).1 ∧
      (ParquetScan.assemble traceOf files).termination = (denoteSnapshotRows limits lookup bind files).2 := by
    induction files with
    | nil => exact ⟨rfl, rfl⟩
    | cons file rest ih =>
      obtain ⟨rows, termination⟩ := scanFile_rows limits lookup bind projection predicate file
      change (traceOf file).rows =
        projection.scan keep (denoteSnapshotFileRows limits lookup bind file).1 at rows
      change (traceOf file).termination = _ at termination
      by_cases eof : (denoteSnapshotFileRows limits lookup bind file).2 = .eos
      · obtain ⟨assembledRows, assembledTerm⟩ := ParquetScan.assemble_eof traceOf file rest (termination.trans eof)
        refine ⟨?_, ?_⟩
        · rw [assembledRows, rows, ih.1]
          simp only [denoteSnapshotRows, eof, Scan.Projection.scan_append]
        · simpa only [denoteSnapshotRows, eof] using assembledTerm.trans ih.2
      · have stopped := ParquetScan.assemble_stops traceOf file rest (by rwa [termination])
        rw [stopped]
        cases outcome : (denoteSnapshotFileRows limits lookup bind file).2 with
        | eos => exact (eof outcome).elim
        | closed | readError _ | closeError _ =>
          simpa only [denoteSnapshotRows, outcome] using And.intro rows termination
  obtain ⟨rows, termination⟩ := agreement files
  change Events.Observation.mk ⟨projection.schema, (ParquetScan.assemble traceOf files).rows⟩
    (ParquetScan.assemble traceOf files).termination = _
  rw [rows, termination]

end Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot
