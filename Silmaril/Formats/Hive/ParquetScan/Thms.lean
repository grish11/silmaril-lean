module

public import Silmaril.Formats.Hive.ParquetScan.Defs
import Silmaril.Proofs.Formats.Hive.ParquetScan.Correctness

public section

namespace Silmaril.Formats.Hive.ParquetScan

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema extendRow)

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

/-- Both scans observe ordered projected rows and the same terminal outcome.
Batch boundaries can differ. This compares supplied traces, with no open skipping. -/
theorem scanHoisted_equivalent (manifest : List (Partition physical schema Value Error))
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value) :
    Events.EventStream.Equivalent (.ok ⟨projection.schema, scanHoisted manifest projection predicate⟩)
      (.ok ⟨projection.schema, scanRowwise manifest projection predicate⟩) :=
  Proofs.Formats.Hive.ParquetScan.scanHoisted_equivalent manifest projection predicate

end Silmaril.Formats.Hive.ParquetScan
