module

public import Silmaril.Formats.Hive.ParquetScan.Defs
import Silmaril.Formats.Arrow.Events.Thms
import Silmaril.Formats.Hive.TypedPartitions.Thms
import Silmaril.Semantics.Relational.Scan.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.ParquetScan

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Hive.ParquetScan
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema extendRow partitionCells)

variable {Kind Error : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

theorem rows_extendTrace (trace : Events.Trace physical Value Error)
    (cells : Scan.Row schema.toScan Value) :
    (extendTrace trace cells).rows = trace.rows.map (fun row => extendRow row cells) := by
  simp [extendTrace, Events.Trace.rows, List.flatMap_map, List.map_flatMap, Function.comp_def]
  rfl

private theorem rows_projectBatches {input : Scan.Schema String Kind}
    (projection : Scan.Projection input) (batches : List (Events.Batch input Value)) :
    (batches.map projection.projectColumns).flatMap AlignedColumns.toRows =
      projection.project (batches.flatMap AlignedColumns.toRows) := by
  induction batches with
  | nil => rfl
  | cons batch rest ih =>
    have localRows : (projection.projectColumns batch).toRows =
        projection.project batch.toRows := projection.rowsEquiv_projectColumns batch
    simpa [Scan.Projection.project, List.map_append] using congrArg₂ List.append localRows ih

private theorem scan_augmented (projection : Scan.Projection (schema.extend physical))
    (predicate : Scan.Predicate schema.toScan Value) (part : Partition physical schema Value Error) :
    projection.scan (fun row => predicate (partitionCells row)) part.augmented.rows =
      if (predicate part.cells).getD false then projection.project part.augmented.rows else [] := by
  cases keep : (predicate part.cells).getD false <;>
    simp [Partition.augmented, rows_extendTrace, Scan.Projection.scan, Scan.Projection.project,
      Scan.select, List.filter_map, Function.comp_def, Silmaril.Formats.Hive.TypedPartitions.partitionCells_extendRow, keep]

private theorem scanPartition_observation (projection : Scan.Projection (schema.extend physical))
    (predicate : Scan.Predicate schema.toScan Value) (part : Partition physical schema Value Error) :
    let rowwise := part.augmented.scan projection (fun row => predicate (partitionCells row))
    let hoisted := scanPartition projection predicate part
    hoisted.rows = rowwise.rows ∧ hoisted.termination = rowwise.termination := by
  dsimp only
  rw [Events.Trace.rows_scan, scan_augmented]
  cases keep : (predicate part.cells).getD false
  · simp [scanPartition, keep, Events.Trace.rows, Events.Trace.scan, Partition.augmented, extendTrace]
  · simp only [keep, ite_true, scanPartition, Events.Trace.rows, Partition.augmented]
    exact ⟨rows_projectBatches projection _, rfl⟩

private theorem assemble_scan {Item : Type*} {input : Scan.Schema String Kind}
    (traceOf : Item → Events.Trace input Value Error) (items : List Item)
    (projection : Scan.Projection input) (predicate : Scan.Predicate input Value) :
    (assemble traceOf items).scan projection predicate =
      assemble (fun item => (traceOf item).scan projection predicate) items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [Events.Trace.scan] at ih
    cases outcome : (traceOf item).termination <;>
      simp [assemble, Events.Trace.scan, outcome, List.map_append, ← ih]

private theorem assemble_observation {Item : Type*} {output : Scan.Schema String Kind}
    (left right : Item → Events.Trace output Value Error) (items : List Item)
    (equal : ∀ item, (left item).rows = (right item).rows ∧
      (left item).termination = (right item).termination) :
    (assemble left items).rows = (assemble right items).rows ∧
      (assemble left items).termination = (assemble right items).termination := by
  induction items with
  | nil => exact ⟨rfl, rfl⟩
  | cons item rest ih =>
    have h := equal item
    cases outcome : (left item).termination with
    | eos =>
      have rightEof := h.2.symm.trans outcome
      simp only [assemble, outcome, rightEof]
      exact ⟨by simpa only [Events.Trace.rows, List.flatMap_append] using
        congrArg₂ (· ++ ·) h.1 ih.1, ih.2⟩
    | closed | readError _ | closeError _ =>
      simpa only [assemble, ← h.2, outcome] using h

theorem scanHoisted_equivalent (manifest : List (Partition physical schema Value Error))
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value) :
    Events.EventStream.Equivalent (.ok ⟨projection.schema, scanHoisted manifest projection predicate⟩)
      (.ok ⟨projection.schema, scanRowwise manifest projection predicate⟩) := by
  apply Events.EventStream.equivalent_open_iff.mpr
  unfold scanHoisted scanRowwise materialize
  rw [assemble_scan]
  exact assemble_observation _ _ manifest (scanPartition_observation projection predicate)

end Silmaril.Proofs.Formats.Hive.ParquetScan
