module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Scan.Defs
import Silmaril.Formats.Hive.ParquetScan.Thms
import Silmaril.Formats.Arrow.Events.Thms
import Silmaril.Semantics.Relational.Scan.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Hive Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema partitionCells)
open Silmaril.Formats.Parquet

variable {Kind Failure : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

private theorem scanFile_observation {Group Error : Type*}
    (opener : Opener Group physical Value Error)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (file : File schema Value) :
    let strict := scanFile opener projection predicate file
    let full := scanFile opener (Scan.Projection.id (schema.extend physical)) (fun _ => some true) file
    let reference := full.scan projection (fun row => predicate (partitionCells row))
    strict.rows = reference.rows ∧ strict.termination = reference.termination := by
  dsimp only
  erw [Events.Trace.rows_scan, Events.Trace.termination_scan]
  cases opened : opener file.path.declared with
  | error reason =>
    simp only [scanFile, opened]
    exact ⟨rfl, trivial⟩
  | ok source =>
    let part : ParquetScan.Partition physical schema Value Error :=
      ⟨file.cells, [ParquetScan.readFile source.source source.fuel]⟩
    let strict := ParquetScan.scanPartition projection predicate part
    let full := ParquetScan.scanPartition (Scan.Projection.id (schema.extend physical)) (fun _ => some true) part
    have hoisted := ParquetScan.scanPartition_observation projection predicate part
    have identity := ParquetScan.scanPartition_observation
      (Scan.Projection.id (schema.extend physical)) (fun _ => some true) part
    have fullRows : full.rows = part.augmented.rows := by
      simpa [Events.Trace.rows_scan, Scan.Projection.scan, Scan.select] using identity.1
    have term : strict.termination = full.termination := hoisted.2.trans identity.2.symm
    have rows : strict.rows = projection.scan (fun row => predicate (partitionCells row)) full.rows := by
      rw [fullRows]
      simpa only [Events.Trace.rows_scan] using hoisted.1
    simp only [scanFile, opened]
    refine ⟨rows, ?_⟩
    let lift : Events.Termination Error → Events.Termination (FileError Error) := fun outcome =>
      match outcome with
      | .eos => .eos | .closed => .closed
      | .readError reason => .readError (.source file.path.declared reason)
      | .closeError reason => .closeError (.source file.path.declared reason)
    exact congrArg lift term

theorem scanSnapshots_equivalent_thenFilter (limits : Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (files : List (File schema Value)) :
    Events.EventStream.Equivalent
      (.ok ⟨projection.schema, scan (snapshotOpener limits lookup bind) projection predicate files⟩)
      (.ok ⟨projection.schema, scanSnapshotsThenFilter limits lookup bind projection predicate files⟩) := by
  apply Events.EventStream.equivalent_open_iff.mpr
  unfold scanSnapshotsThenFilter scan
  erw [ParquetScan.assemble_scan]
  exact ParquetScan.assemble_observation _ _ files
    (scanFile_observation (snapshotOpener limits lookup bind) projection predicate)

theorem scanFile_eof_of_snapshot (limits : Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (file : File schema Value) (clean : SnapshotReachesEOF limits lookup bind file.path.declared) :
    (scanFile (snapshotOpener limits lookup bind) projection predicate file).termination = .eos := by
  obtain ⟨bytes, found, exhausted⟩ := clean
  cases opened : Snapshot.openSource limits bind bytes with
  | error reason => simp [Snapshot.readAll, opened, Except.map, Parquet.Reader.readAll,
      Events.EventStream.collect] at exhausted
  | ok source =>
    have same := ParquetScan.readFile_eq_reader source (source.groups.length + 1)
    simp only [Snapshot.readAll, opened, Except.map, Parquet.Reader.readAll, same,
      Events.EventStream.collect, Events.Trace.collect, Except.ok.injEq] at exhausted
    cases keep : (predicate file.cells).getD false <;>
      simp [scanFile, snapshotOpener, found, opened, Except.map, ParquetScan.scanPartition,
        ParquetScan.assemble, exhausted, keep]

end Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot
