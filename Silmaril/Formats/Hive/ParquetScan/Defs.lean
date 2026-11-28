module

public import Silmaril.Formats.Hive.TypedPartitions.Defs
public import Silmaril.Formats.Parquet.Reader.Defs

/-!
# Hive partition scans over Parquet Arrow events

A manifest supplies typed Hive partition tuples and Arrow traces at a fixed
physical schema. Within a partition, files are ordered. Only EOF advances to
the next file. Early close, read failure, and close failure end the manifest
after the emitted prefix. A partition filter controls rows, with every
reached file's terminal outcome still observed.
-/

@[expose] public section

namespace Silmaril.Formats.Hive.ParquetScan

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema extendRow partitionCells)

variable {Kind Error : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

/-- Use the Parquet Arrow reader on a source whose open already succeeded.
Use one pull beyond the group count for full consumption, or a smaller budget
to observe early close and its outcome. -/
def readFile {Group : Type*} (source : Parquet.Reader.Source Group physical Value Error)
    (fuel : Nat) : Events.Trace physical Value Error :=
  Events.BatchReader.read.pull
    (Parquet.Reader.batchReader (id : Parquet.Reader.OpenResult Group String Value Error → _))
    physical fuel source []

/-- A typed partition supplies a constant virtual tuple and an ordered list of
already supplied file traces at the common physical schema. -/
structure Partition (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (Value : Kind → Type*) (Error : Type*) where
  cells : Scan.Row schema.toScan Value
  files : List (Events.Trace physical Value Error)

/-- Concatenate successful prefixes in order and stop at the first non-EOF.
An empty list and a list of only exhausted traces end at EOF. -/
def assemble {Item : Type*} {output : Scan.Schema String Kind}
    (traceOf : Item → Events.Trace output Value Error) :
    List Item → Events.Trace output Value Error
  | [] => ⟨[], .eos⟩
  | item :: rest =>
    let current := traceOf item
    match current.termination with
    | .eos =>
      let tail := assemble traceOf rest
      ⟨current.batches ++ tail.batches, tail.termination⟩
    | .closed | .readError _ | .closeError _ => current

/-- Extend every row of an available trace, keeping the batches and terminal outcome. -/
def extendTrace (trace : Events.Trace physical Value Error) (cells : Scan.Row schema.toScan Value) :
    Events.Trace (schema.extend physical) Value Error :=
  ⟨trace.batches.map (fun batch =>
    AlignedColumns.ofRows (batch.toRows.map (fun row => extendRow row cells))), trace.termination⟩

def Partition.augmented (partition : Partition physical schema Value Error) :
    Events.Trace (schema.extend physical) Value Error :=
  extendTrace (assemble id partition.files) partition.cells

def materialize (manifest : List (Partition physical schema Value Error)) :
    Events.Trace (schema.extend physical) Value Error :=
  assemble Partition.augmented manifest

/-- Reference scan. Test the partition predicate through the virtual cells of
each augmented row and project the survivors. -/
def scanRowwise (manifest : List (Partition physical schema Value Error))
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value) :
    Events.Trace projection.schema Value Error :=
  (materialize manifest).scan projection (fun row => predicate (partitionCells row))

def scanPartition (projection : Scan.Projection (schema.extend physical))
    (predicate : Scan.Predicate schema.toScan Value) (partition : Partition physical schema Value Error) :
    Events.Trace projection.schema Value Error :=
  let trace := assemble id partition.files
  if (predicate partition.cells).getD false then
    ⟨(extendTrace trace partition.cells).batches.map projection.projectColumns, trace.termination⟩
  else
    ⟨[], trace.termination⟩

/-- Test the partition predicate once per reached partition. A discarded
partition still supplies its file traces and terminal outcome. -/
def scanHoisted (manifest : List (Partition physical schema Value Error))
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value) :
    Events.Trace projection.schema Value Error :=
  assemble (scanPartition projection predicate) manifest

end Silmaril.Formats.Hive.ParquetScan
