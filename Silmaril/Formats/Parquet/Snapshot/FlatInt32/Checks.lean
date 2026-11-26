module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.FlatInt32.Defs
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Scan.Thms
import Silmaril.Formats.Hive.ParquetScan.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.FlatInt32.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Scan.Defs

namespace Silmaril.Formats.Parquet.Snapshot.FlatInt32

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Hive

private def v1 : Bytes := ⟨include_bytes "../../../../../tools/parquet-flat-scan/fixtures/flat-plain-v1.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../../tools/parquet-flat-scan/fixtures/flat-plain-v2.parquet"⟩

-- The independently checked first V2 column chunk in the second group starts at 234.
-- Replace its first PageHeader field with STOP, leaving the footer untouched.
private def late : Bytes := ⟨(v2.data.extract 0 234).push 0 ++ v2.data.extract 235 v2.length⟩

private def physical : Scan.Schema String Unit :=
  ⟨2, fun i => (if i.val = 0 then "required_i32" else "optional_i32", ())⟩

private def reversed : Scan.Schema String Unit :=
  ⟨2, fun i => (if i.val = 0 then "optional_i32" else "required_i32", ())⟩

private def required (i : Nat) : Option Int32 := some (Int32.ofInt (10 * (i : Int) - 17))
private def optional (i : Nat) : Option Int32 := if i % 3 = 0 then none else some (Int32.ofInt (-3 * (i : Int)))

private def physicalRows (n : Nat) : List (List (Option Int32)) :=
  (List.range n).map fun i => [required i, optional i]

private def lateReason {ε : Type} : Snapshot.Error (Error ε) :=
  .decode 1 (.profile (.page (.header (.missingField 1))))

private def observeBatches (stream : Events.EventStream String Cell (Snapshot.Error (Error Unit))) :
    Except (Snapshot.Error (Error Unit))
      (List Nat × List (List (Option Int32)) × Events.Termination (Snapshot.Error (Error Unit))) :=
  stream.map fun ⟨_, trace⟩ =>
    (trace.batches.map (·.rowCount), trace.rows.map List.ofFn, trace.termination)

private def arrow (schema : Scan.Schema String Unit) (bytes : Bytes) :=
  observeBatches (readAll {} schema bytes)

private def bounded (fuel : Nat) (bytes : Bytes) :=
  observeBatches ((Snapshot.batchReader {} (bind {} physical)).read fuel bytes)

#guard arrow physical v1 = .ok ([12, 12], physicalRows 24, .eos)
#guard arrow physical v2 = .ok ([12, 12], physicalRows 24, .eos)
#guard arrow physical late = .ok ([12], physicalRows 12, .readError lateReason)
#guard arrow reversed v1 = .error (.schema (.schemaNames ["optional_i32", "required_i32"]
  ["required_i32", "optional_i32"]))

#guard bounded 0 v2 = .ok ([], [], .closed)
#guard bounded 2 v2 = .ok ([12, 12], physicalRows 24, .closed)
#guard bounded 3 v2 = .ok ([12, 12], physicalRows 24, .eos)
#guard bounded 1 late = .ok ([12], physicalRows 12, .closed)
#guard bounded 2 late = .ok ([12], physicalRows 12, .readError lateReason)

private def repeatReordered (schema : Scan.Schema String Unit) : Scan.Projection schema :=
  if bound : 1 < schema.width then
    Scan.Projection.ofArray #[⟨1, bound⟩, ⟨0, Nat.lt_trans (by decide) bound⟩, ⟨1, bound⟩]
  else Scan.Projection.id schema

private def keepOptionalBelow (schema : Scan.Schema String Unit) : Scan.Predicate schema Cell :=
  fun row => if bound : 1 < schema.width then (row ⟨1, bound⟩).map (· < -5) else none

private def postReadMatches (projection : (schema : Scan.Schema String Unit) → Scan.Projection schema)
    (bytes : Bytes) (names : List String) (count : Nat) (rows : List (List (Option Int32)))
    (termination : Events.Termination (Snapshot.Error (Error Unit))) : Bool :=
  match ((Snapshot.readAll {} (bind {} physical) bytes).scan projection keepOptionalBelow).collect with
  | .error _ => false
  | .ok result =>
    (List.ofFn fun index => (result.table.schema.kind index).1) == names &&
      result.table.rowCount == count && result.table.rows.map List.ofFn == rows &&
      decide (result.termination = termination)

private def kept (count : Nat) : List Nat :=
  (List.range count).filter fun i => 2 ≤ i && i % 3 != 0

private def logicalRows (count : Nat) : List (List (Option Int32)) :=
  (kept count).map fun i => [optional i, required i, optional i]

private def projectedNames : List String := ["optional_i32", "required_i32", "optional_i32"]

#guard postReadMatches repeatReordered v2 projectedNames 15 (logicalRows 24) .eos
#guard postReadMatches repeatReordered late projectedNames 7 (logicalRows 12) (.readError lateReason)
#guard postReadMatches (fun _ => Scan.Projection.ofArray #[]) late [] 7
  (List.replicate 7 []) (.readError lateReason)

private def partitions : TypedPartitions.PartitionSchema Unit := ⟨#[⟨"year", (), .asNull⟩]⟩
private def convert : TypedPartitions.Convert Cell String := fun _ text =>
  match text.toInt? with
  | none => .error "invalid year"
  | some year => .ok (Int32.ofInt year)

private def lookup : String → Except String Bytes
  | "year=%37/v1.parquet" => .ok v1
  | "year=9/v2.parquet" | "year=8/rejected.parquet" |
    "year=__HIVE_DEFAULT_PARTITION__/unknown.parquet" => .ok v2
  | "year=8/late.parquet" | "year=9/late.parquet" => .ok late
  | _ => .error "snapshot missing"

private def profileLookup (path : String) : Except (Error String) Bytes := (lookup path).mapError .lookup
private def binding : Snapshot.Bind physical Cell (Error String) := bind {} physical
private def opener := Manifest.flatInt32SnapshotOpener (physical := physical) {} lookup

private def projection : Scan.Projection (partitions.extend physical) :=
  Scan.Projection.ofArray (#[2, 1, 0, 1] : Array (Fin 3))

private def keep : Scan.Predicate partitions.toScan Cell := fun row =>
  (row (0 : Fin 1)).map (fun (year : Int32) => year != 8)

private abbrev Trace := Events.Trace projection.schema Cell (Manifest.FileError (Snapshot.Error (Error String)))

private def dataset (run : List (Manifest.File partitions Cell) → Trace) (paths : List String) :
    Option (List (List (Option Int32)) × Events.Termination (Manifest.FileError (Snapshot.Error (Error String)))) :=
  (Manifest.prepare physical partitions {} convert paths).toOption.map fun files =>
    let trace := run files
    (trace.rows.map List.ofFn, trace.termination)

private def strict := dataset (Manifest.scan opener projection keep)
private def pruned := dataset (Manifest.scanSkippingRejected opener projection keep)
private def reference := dataset (Manifest.scanSnapshotsThenFilter {} profileLookup binding projection keep)

private def projected (year : Int32) (n : Nat) : List (List (Option Int32)) :=
  (List.range n).map fun i => [some year, optional i, required i, optional i]

private def cleanPaths := ["year=%37/v1.parquet", "year=8/rejected.parquet",
  "year=__HIVE_DEFAULT_PARTITION__/unknown.parquet", "year=9/v2.parquet", "year=%37/v1.parquet"]

#guard cleanPaths.all (fun path =>
  match profileLookup path with
  | .error _ => false
  | .ok bytes => decide ((Snapshot.readAll {} binding bytes).collect.map Events.Observation.termination = .ok .eos))
#guard strict cleanPaths = some (projected 7 24 ++ projected 9 24 ++ projected 7 24, .eos)
#guard strict cleanPaths = reference cleanPaths
#guard pruned cleanPaths = reference cleanPaths

private def retainedLate := ["year=%37/v1.parquet", "year=9/late.parquet", "year=9/v2.parquet"]
#guard strict retainedLate =
  some (projected 7 24 ++ projected 9 12, .readError (.source "year=9/late.parquet" lateReason))
#guard reference retainedLate = strict retainedLate
#guard pruned retainedLate = strict retainedLate

private def rejectedLate := ["year=%37/v1.parquet", "year=8/late.parquet", "year=9/v2.parquet"]
#guard reference rejectedLate = some (projected 7 24, .readError (.source "year=8/late.parquet" lateReason))
#guard pruned rejectedLate = some (projected 7 24 ++ projected 9 24, .eos)

#print axioms Manifest.scanSnapshots_equivalent_thenFilter
#print axioms Manifest.scanFile_eof_of_snapshot
#print axioms Manifest.scanSnapshotsSkippingRejected_equivalent_thenFilter
#print axioms ParquetScan.scanPartition_observation
#print axioms ParquetScan.assemble_scan
#print axioms ParquetScan.assemble_observation

end Silmaril.Formats.Parquet.Snapshot.FlatInt32
