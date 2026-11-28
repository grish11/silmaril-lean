module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.AlignedInt32.Thms
import Silmaril.Formats.Hive.Manifest.Pruning.Defs
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.AlignedInt32.Defs
meta import Silmaril.Formats.Hive.Manifest.Pruning.Defs

namespace Silmaril.Formats.Hive.Manifest.AlignedInt32

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema Convert)

private def base : Bytes :=
  ⟨include_bytes "../../../../../../tools/parquet-flat-scan/fixtures/hive-int32-alignment/year=%37/base.parquet"⟩
private def added : Bytes :=
  ⟨include_bytes "../../../../../../tools/parquet-flat-scan/fixtures/hive-int32-alignment/year=__HIVE_DEFAULT_PARTITION__/added.parquet"⟩

-- PyArrow independently locates the group's first page header at byte 56.
private def damaged : Bytes := ⟨(added.data.extract 0 56).push 0 ++ added.data.extract 57 added.length⟩

private def basePath := "year=%37/base.parquet"
private def addedPath := "year=__HIVE_DEFAULT_PARTITION__/added.parquet"
private def latePath := "year=8/damaged.parquet"
private def unvisited := "year=9/unvisited.parquet"

private def lookup : String → Except String Bytes
  | "year=%37/base.parquet" => .ok base
  | "year=__HIVE_DEFAULT_PARTITION__/added.parquet" => .ok added
  | "year=8/damaged.parquet" => .ok damaged
  | _ => .error "missing literal snapshot"

private def partition (name : String) : PartitionSchema Unit := ⟨#[⟨name, (), .reject⟩]⟩
private def partitions := partition "year"

private def schema (fields : List String) : Scan.Schema String Unit :=
  ⟨fields.length, fun i => (fields.get i, ())⟩

private def target := schema ["id", "latency"]
private def allowLatency : AllowMissing target := fun i => i.val == 1
private def convert : Convert Cell String := fun _ text =>
  match text.toInt? with
  | some value => .ok (Int32.ofInt value)
  | none => .error "expected Int32"

private abbrev Failure := FileError (Snapshot.Error (Error String))
private structure Observed where
  batchSizes : List Nat
  rows : List (List (Option Int32))
  termination : Events.Termination Failure
  deriving DecidableEq

private def observe {out : Scan.Schema String Unit}
    (run : List (File partitions Cell) → Events.Trace out Cell Failure)
    (paths : List String) : Option Observed :=
  (Manifest.prepare target partitions {} convert paths).toOption.map fun files =>
    let trace := run files
    ⟨trace.batches.map (·.rowCount), trace.rows.map (fun row => List.ofFn fun i => row i), trace.termination⟩

private def opener (allow : AllowMissing target) :=
  alignedInt32SnapshotOpener {} partitions allow lookup

private def allColumns := Scan.Projection.id (partitions.extend target)
private def keepAll : Scan.Predicate partitions.toScan Cell := fun _ => some true
private def collect (allow : AllowMissing target) :=
  observe (scan (opener allow) allColumns keepAll)

private def baseRows : List (List (Option Int32)) := [[some 10, none, some 7], [some 11, none, some 7]]
private def addedRows : List (List (Option Int32)) := [[some 20, some 200, none], [some 21, none, none]]
private def clean := [basePath, addedPath, basePath]

#guard collect allowLatency clean = some ⟨[1, 1, 1, 1, 1, 1], baseRows ++ addedRows ++ baseRows, .eos⟩

#guard collect (fun _ => false) [basePath] =
  some ⟨[], [], .readError (.open basePath (.schema (.missingRequired "latency")))⟩

-- A physically nullable field remains nullable even if its presence is required.
#guard collect (fun _ => false) [addedPath, basePath, unvisited] =
  some ⟨[1, 1], addedRows, .readError (.open basePath (.schema (.missingRequired "latency")))⟩

private def lateError : Failure :=
  .source latePath (.decode 1 (.physical (.profile (.page (.header (.missingField 1))))))

#guard collect allowLatency [basePath, latePath, unvisited] =
  some ⟨[1, 1, 1], baseRows ++ [[some 20, some 200, some 8]], .readError lateError⟩

private def reference (allow : AllowMissing target) (paths : List String) :
    Option (List (List (Option Int32)) × Events.Termination Failure) :=
  (Manifest.prepare target partitions {} convert paths).toOption.map fun files =>
    let (rows, termination) := denoteRows {} lookup allow files
    (rows.map (fun row => List.ofFn fun i => row i), termination)

#guard reference allowLatency clean = some (baseRows ++ addedRows ++ baseRows, .eos)
#guard reference allowLatency [basePath, latePath, unvisited] =
  some (baseRows ++ [[some 20, some 200, some 8]], .readError lateError)

#guard reference (fun _ => false) [addedPath, basePath, unvisited] =
  some (addedRows, .readError (.open basePath (.schema (.missingRequired "latency"))))

private def strictOpenError (bytes : Bytes) : Option (Snapshot.Error (Snapshot.FlatInt32.Error Unit)) :=
  match Snapshot.FlatInt32.readAll {} target bytes with
  | .ok _ => none
  | .error reason => some reason

#guard strictOpenError base = some (.schema (.schemaNames ["id", "latency"] ["id"]))
#guard strictOpenError added = some (.schema (.schemaNames ["id", "latency"] ["latency", "id"]))

private def openError (fields : List String) (partitionName : String) (bytes : Bytes) :
    Option (Snapshot.Error (Error String)) :=
  match Snapshot.openSource {} (AlignedInt32.bind {} (schema fields) (fun _ => true)
      (partition partitionName)) bytes with
  | .ok _ => none
  | .error reason => some reason

#guard openError ["id", "id"] "year" added = some (.schema .duplicateTarget)
#guard openError ["id", "year"] "year" added = some (.schema (.reservedPartition "year"))
#guard openError ["id"] "latency" added = some (.schema (.reservedPartition "latency"))
#guard openError ["id"] "year" added = some (.schema (.unexpectedField "latency"))
#guard openError ["ID", "latency"] "year" added = some (.schema (.unexpectedField "id"))

-- Project repeated positions and keep null partitions. Strict scanning still
-- reaches a rejected file and reports its error. Skip-open pruning skips it.
private def repeated : Scan.Projection (partitions.extend target) := by
  have width : (partitions.extend target).width = 3 := rfl
  exact Scan.Projection.ofArray ((#[2, 1, 0, 1] : Array (Fin 3)).map (Fin.cast width.symm))
private def keepOutsideEight : Scan.Predicate partitions.toScan Cell :=
  fun cells => some (((cells (0 : Fin 1)).map (· != (8 : Int32))).getD true)

private def firstProjected : List (List (Option Int32)) :=
  [[some 7, none, some 10, none], [some 7, none, some 11, none]]

#guard observe (scan (opener allowLatency) repeated keepOutsideEight) [basePath, latePath, addedPath] =
  some ⟨[1, 1], firstProjected, .readError lateError⟩

#guard observe (scanSkippingRejected (opener allowLatency) repeated keepOutsideEight)
    [basePath, latePath, addedPath] =
  some ⟨[1, 1, 1, 1], firstProjected ++ [[none, some 200, some 20, some 200], [none, none, some 21, none]], .eos⟩

#print axioms Manifest.AlignedInt32.readGroup_alignDecode
#print axioms Manifest.AlignedInt32.readAll_alignDecode
#print axioms Manifest.scanAlignedInt32Snapshots_collect_eq_rows

end Silmaril.Formats.Hive.Manifest.AlignedInt32
