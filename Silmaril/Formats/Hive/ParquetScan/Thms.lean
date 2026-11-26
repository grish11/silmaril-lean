module

public import Silmaril.Formats.Hive.ParquetScan.Defs
import Silmaril.Proofs.Formats.Hive.ParquetScan.Correctness

public section

namespace Silmaril.Formats.Hive.ParquetScan

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema extendRow partitionCells)

variable {Kind Error : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

/-- The fixed-schema adapter is exactly the Parquet Arrow reader after successful open. -/
theorem readFile_eq_reader {Group : Type*}
    (source : Parquet.Reader.Source Group physical Value Error) (fuel : Nat) :
    (Parquet.Reader.batchReader (id : Parquet.Reader.OpenResult Group String Value Error → _)).read
        fuel (.ok ⟨physical, source⟩) = .ok ⟨physical, readFile source fuel⟩ := rfl

/-- On EOF, keep the current ordered rows before all rows from the remaining items. -/
theorem assemble_eof {Item : Type*} {output : Scan.Schema String Kind}
    (traceOf : Item → Events.Trace output Value Error) (item : Item) (rest : List Item)
    (eof : (traceOf item).termination = .eos) :
    (assemble traceOf (item :: rest)).rows =
        (traceOf item).rows ++ (assemble traceOf rest).rows ∧
      (assemble traceOf (item :: rest)).termination = (assemble traceOf rest).termination := by
  simp [assemble, eof, Events.Trace.rows, List.flatMap_append]

/-- A close or failure returns the entire current prefix and leaves the tail unobserved. -/
theorem assemble_stops {Item : Type*} {output : Scan.Schema String Kind}
    (traceOf : Item → Events.Trace output Value Error) (item : Item) (rest : List Item)
    (stop : (traceOf item).termination ≠ .eos) :
    assemble traceOf (item :: rest) = traceOf item := by
  cases outcome : (traceOf item).termination <;> simp [assemble, outcome] at stop ⊢

theorem rows_extendTrace (trace : Events.Trace physical Value Error)
    (cells : Scan.Row schema.toScan Value) :
    (extendTrace trace cells).rows = trace.rows.map (fun row => extendRow row cells) :=
  Proofs.Formats.Hive.ParquetScan.rows_extendTrace trace cells

/-- Hoisting preserves the ordered rows and the terminal outcome of one partition. -/
theorem scanPartition_observation (projection : Scan.Projection (schema.extend physical))
    (predicate : Scan.Predicate schema.toScan Value) (part : Partition physical schema Value Error) :
    let rowwise := part.augmented.scan projection (fun row => predicate (partitionCells row))
    let hoisted := scanPartition projection predicate part
    hoisted.rows = rowwise.rows ∧ hoisted.termination = rowwise.termination :=
  Proofs.Formats.Hive.ParquetScan.scanPartition_observation projection predicate part

/-- Logical scanning commutes with ordered trace assembly. -/
theorem assemble_scan {Item : Type*} {input : Scan.Schema String Kind}
    (traceOf : Item → Events.Trace input Value Error) (items : List Item)
    (projection : Scan.Projection input) (predicate : Scan.Predicate input Value) :
    (assemble traceOf items).scan projection predicate =
      assemble (fun item => (traceOf item).scan projection predicate) items :=
  Proofs.Formats.Hive.ParquetScan.assemble_scan traceOf items projection predicate

/-- Matching per-item observations preserve ordered assembly, including its first terminal failure. -/
theorem assemble_observation {Item : Type*} {output : Scan.Schema String Kind}
    (left right : Item → Events.Trace output Value Error) (items : List Item)
    (equal : ∀ item, (left item).rows = (right item).rows ∧
      (left item).termination = (right item).termination) :
    (assemble left items).rows = (assemble right items).rows ∧
      (assemble left items).termination = (assemble right items).termination :=
  Proofs.Formats.Hive.ParquetScan.assemble_observation left right items equal

/-- Both scans observe ordered projected rows and the same terminal outcome.
Batch boundaries can differ. This compares supplied traces, with no open skipping. -/
theorem scanHoisted_equivalent (manifest : List (Partition physical schema Value Error))
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value) :
    Events.EventStream.Equivalent (.ok ⟨projection.schema, scanHoisted manifest projection predicate⟩)
      (.ok ⟨projection.schema, scanRowwise manifest projection predicate⟩) :=
  Proofs.Formats.Hive.ParquetScan.scanHoisted_equivalent manifest projection predicate

end Silmaril.Formats.Hive.ParquetScan
