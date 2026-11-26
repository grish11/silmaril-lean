module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Bounded.Thms
import Silmaril.Formats.Parquet.Snapshot.FlatInt32.Defs
import Silmaril.Formats.Parquet.Snapshot.Pull.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Bounded.Defs
meta import Silmaril.Formats.Parquet.Snapshot.FlatInt32.Defs

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet Silmaril.Relational
open Silmaril.Formats.Hive
open Snapshot.FlatInt32 (Cell Error)

private def v1 : Bytes := ⟨include_bytes "../../../../../../tools/parquet-flat-scan/fixtures/flat-plain-v1.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../../../tools/parquet-flat-scan/fixtures/flat-plain-v2.parquet"⟩
private def emptyFile : Bytes := ⟨include_bytes "../../../../../../tools/parquet-flat-scan/fixtures/flat-empty-no-groups.parquet"⟩
private def late : Bytes := ⟨(v2.data.extract 0 234).push 0 ++ v2.data.extract 235 v2.length⟩

private def physical : Scan.Schema String Unit :=
  ⟨2, fun i => (if i.val = 0 then "required_i32" else "optional_i32", ())⟩
private def partitions : TypedPartitions.PartitionSchema Unit := ⟨#[⟨"year", (), .reject⟩]⟩

private def convert : TypedPartitions.Convert Cell String := fun _ text =>
  match text.toInt? with
  | none => .error "invalid year"
  | some year => .ok (Int32.ofInt year)

private def pathA := "year=%37/v1.parquet"
private def pathB := "year=9/v2.parquet"
private def emptyPath := "year=7/empty.parquet"
private def latePath := "year=%38/late.parquet"
private def missing := "year=7/not-present.parquet"

private def lookup : String → Except (Error String) Bytes
  | "year=%37/v1.parquet" => .ok v1
  | "year=9/v2.parquet" => .ok v2
  | "year=7/empty.parquet" => .ok emptyFile
  | "year=%38/late.parquet" => .ok late
  | _ => .error (.lookup "snapshot missing")

private abbrev Failure := FileError (Snapshot.Error (Error String))
private def keepAll : Scan.Predicate partitions.toScan Cell := fun _ => some true
private def keepOutsideEight : Scan.Predicate partitions.toScan Cell :=
  fun row => (row (0 : Fin 1)).map (· != (8 : Int32))

private def observe (projection : Scan.Projection (partitions.extend physical))
    (keep : Scan.Predicate partitions.toScan Cell) (budget : Nat) (paths : List String) :
    Option (Events.Trace projection.schema Cell Failure) :=
  (prepare physical partitions {} convert paths).toOption.map fun files =>
    scanSnapshotsBounded {} lookup (Snapshot.FlatInt32.bind {} physical) projection keep budget files

private def observesProjection (projection : Scan.Projection (partitions.extend physical))
    (keep : Scan.Predicate partitions.toScan Cell) (budget : Nat) (paths : List String)
    (expected : List (List (Option Int32))) (outcome : Events.Termination Failure) : Bool :=
  match observe projection keep budget paths with
  | none => false
  | some trace =>
    trace.rows.map (fun row => List.ofFn fun i => row i) == expected && decide (trace.termination = outcome)

private def observes := observesProjection (Scan.Projection.id _)

private def observesBatchCounts (projection : Scan.Projection (partitions.extend physical))
    (budget : Nat) (paths : List String) (expected : List Nat) (outcome : Events.Termination Failure) : Bool :=
  match observe projection keepAll budget paths with
  | none => false
  | some trace => trace.batches.map (·.rowCount) == expected && decide (trace.termination = outcome)

private def rows (count : Nat) (year : Int32) : List (List (Option Int32)) :=
  (List.range count).map fun (i : Nat) =>
    [some (Int32.ofInt (10 * (i : Int) - 17)), if i % 3 = 0 then none else some (Int32.ofInt (-3 * (i : Int))),
      some year]

private def missingError : Events.Termination Failure :=
  .readError (.open missing (.input (.lookup "snapshot missing")))

private def lateError : Events.Termination Failure :=
  .readError (.source latePath (.decode 1 (.profile (.page (.header (.missingField 1))))))

#guard observes keepAll 0 [] [] .eos
#guard observes keepAll 0 [missing] [] .closed
#guard observes keepAll 1 [missing] [] missingError

#guard observesBatchCounts (Scan.Projection.id _) 1 [emptyPath] [] .closed
#guard observesBatchCounts (Scan.Projection.id _) 2 [emptyPath] [] .eos
#guard observes keepAll 2 [emptyPath, missing] [] .closed
#guard observes keepAll 3 [emptyPath, missing] [] missingError

#guard observes keepAll 1 [pathA] [] .closed
#guard observes keepAll 3 [pathA] (rows 24 7) .closed
#guard observes keepAll 4 [pathA] (rows 24 7) .eos
#guard observes keepAll 4 [pathA, missing] (rows 24 7) .closed
#guard observes keepAll 5 [pathA, missing] (rows 24 7) missingError

#guard observes keepAll 6 [pathA, latePath, missing] (rows 24 7 ++ rows 12 8) .closed
#guard observes keepAll 7 [pathA, latePath, missing] (rows 24 7 ++ rows 12 8) lateError
#guard observes keepOutsideEight 6 [pathA, latePath, missing] (rows 24 7) .closed
#guard observes keepOutsideEight 7 [pathA, latePath, missing] (rows 24 7) lateError
#guard observes keepAll 7 [pathA, pathB] (rows 24 7 ++ rows 24 9) .closed
#guard observes keepAll 8 [pathA, pathB] (rows 24 7 ++ rows 24 9) .eos

#guard observes keepAll 10 [pathA, pathB, pathA] (rows 24 7 ++ rows 24 9 ++ rows 12 7) .closed
#guard observes keepAll 12 [pathA, pathB, pathA] (rows 24 7 ++ rows 24 9 ++ rows 24 7) .eos

#guard observesBatchCounts (Scan.Projection.ofArray #[]) 3 [pathA] [12, 12] .closed

private def reordered : Scan.Projection (partitions.extend physical) :=
  Scan.Projection.ofArray #[⟨2, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

#guard observesProjection reordered keepAll 2 [pathA]
  ((rows 12 7).map fun row => [some (7 : Int32), row[1]!, some 7]) .closed

#print axioms scanSnapshotsBounded_eq_reference
#print axioms Snapshot.openSource_close

end Silmaril.Formats.Hive.Manifest
