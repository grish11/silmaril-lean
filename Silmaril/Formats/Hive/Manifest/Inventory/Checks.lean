module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Thms
import Silmaril.Formats.Hive.Manifest.Inventory.Thms
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Thms
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.FlatInt32.Defs
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Defs
meta import Silmaril.Formats.Hive.Manifest.Inventory.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.FlatInt32.Defs

namespace Silmaril.Formats.Hive.Manifest.Inventory

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet Silmaril.Relational
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema Convert)

local instance {E A : Type} [BEq E] [BEq A] : BEq (Except E A) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

private abbrev Cell := Snapshot.FlatInt32.Cell
private def physical : Scan.Schema String Unit := ⟨1, fun _ => ("value", ())⟩
private def schema : PartitionSchema Unit := ⟨#[⟨"year", (), .reject⟩]⟩
private def convert : Convert Cell String := fun _ text =>
  match text.toInt? with
  | some value => .ok (Int32.ofInt value)
  | none => .error "expected Int32"

private def escaped := "year=%37/part-a.parquet"
private def nullPartition := "year=__HIVE_DEFAULT_PARTITION__/part-null.parquet"
private def other := "year=9/part-b.parquet"
private def mixed := ["_SUCCESS", escaped, "_metadata", nullPartition, escaped, "_common_metadata", other]
private def limits : Limits := ⟨7, 128⟩

private def admit (paths : List String) (bounds : Limits := limits) :=
  prepareInventory physical schema bounds {} convert paths

private def paths (declared : List String) (bounds : Limits := limits) : Except (Error String) (List String) :=
  (admit declared bounds).map (List.map (·.path.declared))

#guard (admit mixed).map (List.map fun file =>
  (file.path.declared, file.path.canonicalDirectory, file.cells (0 : Fin 1))) ==
  .ok [(escaped, "year=7", some 7), (nullPartition, "year=__HIVE_DEFAULT_PARTITION__", none),
    (escaped, "year=7", some 7), (other, "year=9", some 9)]

-- The budget counts both the three controls and the repeated data file.
#guard paths mixed ⟨6, 128⟩ == .error (.entryLimit 6)
#guard paths [] ⟨0, 0⟩ == .ok []
#guard paths ["../_SUCCESS"] ⟨0, 0⟩ == .error (.entryLimit 0)
#guard (prepareInventory (⟨1, fun _ => ("year", ())⟩ : Scan.Schema String Unit)
  schema ⟨0, 0⟩ {} convert ["../_SUCCESS"]).map (List.map (·.path.declared)) ==
  .error (.schema (.physicalCollision "year"))

-- Classify literal leaf spelling. Controls skip parent parsing but pass
-- through whole-path lexical and UTF-8 byte checks first.
#guard paths ["layout/%GG/_metadata", "year=oops/_SUCCESS", "_common_metadata"] == .ok []
#guard paths ["é/_SUCCESS"] ⟨1, 11⟩ == .ok []
#guard paths ["é/_SUCCESS"] ⟨1, 10⟩ == .error (.pathByteLimit 0 11)
#guard paths ["../_SUCCESS"] ⟨1, 10⟩ == .error (.pathByteLimit 0 11)
#guard paths [escaped, "_SUCCESS", escaped, "../_metadata", other] ==
  .error (.entry 3 (.relativePath "../_metadata" .invalidSegment))
#guard paths ["_SUCCESS/part.parquet"] ==
  .error (.entry 0 (.partitionPath "_SUCCESS/part.parquet" (.missingEquals "_SUCCESS")))

private def nearMatches := ["year=7/_success", "year=7/_metadata.bak", "year=7/%5FSUCCESS",
  "year=7/_temporary", "year=7/.hidden"]

#guard paths nearMatches == .ok nearMatches
#guard paths ["_SUCCESS", "README", "../_metadata"] ==
  .error (.entry 1 (.binding "README" (.missingKey "year")))
#guard paths [escaped, "_metadata", "year=oops/part.parquet", "../_SUCCESS"] ⟨3, 128⟩ ==
  .error (.entry 2 (.binding "year=oops/part.parquet" (.conversion "year" "expected Int32")))
#guard paths [escaped, "year=%GG/part.parquet", "../_SUCCESS"] ==
  .error (.entry 1 (.partitionPath "year=%GG/part.parquet" .invalidEscape))

private def lookup : String → Except String Bytes
  | "year=%37/part-a.parquet" =>
    .ok ⟨include_bytes "../../../../../tools/parquet-flat-scan/fixtures/hive-inventory/year=%37/part-a.parquet"⟩
  | "year=__HIVE_DEFAULT_PARTITION__/part-null.parquet" =>
    .ok ⟨include_bytes "../../../../../tools/parquet-flat-scan/fixtures/hive-inventory/year=__HIVE_DEFAULT_PARTITION__/part-null.parquet"⟩
  | "year=9/part-b.parquet" =>
    .ok ⟨include_bytes "../../../../../tools/parquet-flat-scan/fixtures/hive-inventory/year=9/part-b.parquet"⟩
  | _ => .error "literal path missing"

private def observeFiles (files : List (File schema Cell)) :
    List (List (Option Int32)) ×
      Events.Termination (FileError (Snapshot.Error (Snapshot.FlatInt32.Error String))) :=
  let projection := Scan.Projection.id (schema.extend physical)
  let trace := scan (flatInt32SnapshotOpener (physical := physical) {} lookup)
    projection (fun _ => some true) files
  (trace.rows.map (fun row => List.ofFn fun i => (row i : Option Int32)), trace.termination)

private def observe (declared : List String) := (admit declared).toOption.map observeFiles

#guard observe mixed =
  some ([[some 10, some 7], [some 20, none], [some 10, some 7], [some 30, some 9]], .eos)

#guard observe ["year=7/part-a.parquet"] =
  some ([], .readError (.open "year=7/part-a.parquet" (.input (.lookup "literal path missing"))))

private def admitOrdered (declared : List String) (bounds : Limits := limits) :=
  prepareOrderedInventory physical schema bounds {} convert declared

private def orderedPaths (declared : List String) (bounds : Limits := limits) :=
  (admitOrdered declared bounds).map (List.map (·.path.declared))

#guard orderedPaths mixed == .ok [escaped, escaped, other, nullPartition]
#guard orderedPaths mixed.reverse == orderedPaths mixed
#guard (admitOrdered mixed.reverse).toOption.map observeFiles =
  some ([[some 10, some 7], [some 10, some 7], [some 30, some 9], [some 20, none]], .eos)
#guard (admitOrdered [other, "year=1/missing.parquet", escaped]).toOption.map observeFiles =
  some ([[some 10, some 7]],
    .readError (.open "year=1/missing.parquet" (.input (.lookup "literal path missing"))))
#guard orderedPaths ["year=7/part-a.parquet", escaped, "year=7/part-a.parquet"] ==
  .ok [escaped, "year=7/part-a.parquet", "year=7/part-a.parquet"]
#guard orderedPaths ["year=7/_success", "_SUCCESS", "year=7/%5FSUCCESS"] ==
  .ok ["year=7/%5FSUCCESS", "year=7/_success"]
#guard orderedPaths ["_SUCCESS", "_metadata", "_common_metadata"] == .ok []
#guard orderedPaths mixed.reverse ⟨6, 128⟩ == .error (.entryLimit 6)
#guard orderedPaths [nullPartition, "z//bad.parquet", "../a.parquet", escaped] ==
  .error (.entry 1 (.relativePath "z//bad.parquet" .invalidSegment))

example {int32 byteArray : Int32ByteArrayGroup.Field}
    {partitions : PartitionSchema Int32ByteArrayGroup.File.Kind} {options : PartitionPath.Options}
    {listing : List String} {files : List (File partitions Int32ByteArrayGroup.File.Value)}
    (admitted : Int32ByteArray.Ingress.preparePaths int32 byteArray partitions options listing = .ok files) :
    (orderFiles files).map (·.path.declared) =
      listing.mergeSort (fun a b => decide (a ≤ b)) := by
  rw [orderFiles_paths, Int32ByteArray.Ingress.preparePaths_preserves_paths int32 byteArray admitted]

#print axioms Manifest.prepareInventory_eq_reference
#print axioms orderFiles_perm
#print axioms orderFiles_paths
#print axioms orderFiles_paths_eq_of_perm
#print axioms Manifest.prepareOrderedInventory_eq_reference
#print axioms Manifest.prepareOrderedInventory_error_iff

end Silmaril.Formats.Hive.Manifest.Inventory
