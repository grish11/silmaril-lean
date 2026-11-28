module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.FlatInt32.Defs
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.WritePlan.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.FlatInt32.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.WritePlan.Defs

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet Silmaril.Relational
open Silmaril.Formats.Hive Silmaril.Formats.Hive.Manifest
open Snapshot.FlatInt32 (Cell Error)

private def v1 : Bytes := ⟨include_bytes "../../../../../../tools/parquet-flat-scan/fixtures/flat-plain-v1.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../../../tools/parquet-flat-scan/fixtures/flat-plain-v2.parquet"⟩
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
private def aliasA := "year=7/v1.parquet"
private def latePath := "year=%38/late.parquet"
private def missing := "year=9/not-reached.parquet"
private def filtered := "year=8/filtered.parquet"
private def nullYear := "year=__HIVE_DEFAULT_PARTITION__/v1.parquet"

private def lookup : String → Except String Bytes
  | "year=%37/v1.parquet" | "year=7/v1.parquet" | "year=__HIVE_DEFAULT_PARTITION__/v1.parquet" => .ok v1
  | "year=9/v2.parquet" | "year=8/filtered.parquet" => .ok v2
  | "year=%38/late.parquet" => .ok late
  | _ => .error "snapshot missing"

private abbrev Result :=
  Except (SnapshotPlanError (partitions.extend physical) Cell (Error String) String)
    (List (WritePlan.Bucket physical Cell))

private def observe (keep : Scan.Predicate partitions.toScan Cell)
    (encode : WritePlan.Encode Cell String) (paths : List String) : Option Result :=
  (prepare physical partitions {} convert paths).toOption.map fun files =>
    planSnapshots {} (fun path => (lookup path).mapError Error.lookup)
      (Snapshot.FlatInt32.bind {} physical) keep files {} encode

private def encode : WritePlan.Encode Cell String := fun _ cell => .ok (toString cell.toInt)
private def refuse : WritePlan.Encode Cell String := fun _ _ => .error "blocked encoder"
private def keepAll : Scan.Predicate partitions.toScan Cell := fun _ => some true
private def keepOutsideEight : Scan.Predicate partitions.toScan Cell :=
  fun row => (row (0 : Fin 1)).map (· != (8 : Int32))

private def payload (count : Nat) : List (List (Option Int32)) :=
  (List.range count).map fun (i : Nat) =>
    [some (Int32.ofInt (10 * (i : Int) - 17)),
     if i % 3 = 0 then none else some (Int32.ofInt (-3 * (i : Int)))]

private def buckets (result : Option Result) : Option (List (String × List (List (Option Int32)))) :=
  match result with
  | some (.ok buckets) => some (buckets.map fun b => (b.directory, b.rows.map List.ofFn))
  | _ => none

#guard buckets (observe keepAll encode [pathA, pathB, aliasA]) ==
  some [("year=7", payload 24 ++ payload 24), ("year=9", payload 24)]
#guard buckets (observe keepOutsideEight encode [filtered, pathB, aliasA, pathA]) ==
  some [("year=9", payload 24), ("year=7", payload 24 ++ payload 24)]
#guard buckets (observe keepAll refuse [nullYear]) ==
  some [("year=__HIVE_DEFAULT_PARTITION__", payload 24)]

#guard buckets (observe keepAll refuse []) == some []
#guard buckets (observe (fun _ => some false) refuse [pathA, pathB]) == some []

private def observedRows (count : Nat) (year : Int32) : List (List (Option Int32)) :=
  (payload count).map fun cells => cells ++ [some year]

private def hasSource (result : Option Result) (expected : List (List (Option Int32))) : Bool :=
  match result with
  | some (.error (.scan termination keptRows)) =>
    decide (termination = .readError (.source latePath (.decode 1 (.profile (.page (.header (.missingField 1))))))) &&
      keptRows.map (fun row => List.ofFn fun i => row i) == expected
  | _ => false

#guard hasSource (observe keepAll encode [pathA, latePath, missing])
  (observedRows 24 7 ++ observedRows 12 8)
#guard hasSource (observe keepOutsideEight encode [pathA, latePath, missing]) (observedRows 24 7)
#guard hasSource (observe (fun _ => some false) refuse [pathA, latePath, missing]) []
#guard hasSource (observe keepAll refuse [pathA, latePath, missing])
  (observedRows 24 7 ++ observedRows 12 8)

#guard match observe keepAll encode [pathA, missing, pathB] with
  | some (.error (.scan outcome keptRows)) =>
    decide (outcome = .readError (.open missing (.input (.lookup "snapshot missing")))) &&
      keptRows.map (fun row => List.ofFn fun i => row i) == observedRows 24 7
  | _ => false

#guard match observe keepAll refuse [pathA] with
  | some (.error (.planning e)) => e == .row 0 (.encode "year" "blocked encoder")
  | _ => false

#print axioms planSnapshots_eq_reference

end Silmaril.Formats.Hive.Manifest
