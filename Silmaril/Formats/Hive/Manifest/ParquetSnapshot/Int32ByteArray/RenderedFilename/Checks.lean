module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedFilename.Thms
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedFilename.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs

namespace Silmaril.Formats.Hive.Manifest.RenderedFilename

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet Silmaril.Relational
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open TypedPartitions (PartitionSchema)

private def ordinal : Field := ⟨"ordinal", .required⟩
private def payload : Field := ⟨"payload", .optional⟩
private def physical := Int32ByteArrayGroup.File.schema ordinal payload
private def partitions : PartitionSchema Kind :=
  ⟨#[⟨"year", .int32 .optional, .reject⟩, ⟨"region", .byteArray .optional, .reject⟩]⟩
private def keys := ["region", "year"]
private def admission : Inventory.Limits := ⟨8, 128⟩
private def encodePath (entries : PartitionPath.Partition) (parent suffix : String) :=
  (PartitionPath.Filename.render 128 keys .uri {} entries suffix).map (fun leaf => parent ++ "/" ++ leaf)

private def retained := "literal=parent/a%5Fb_7_part-0.parquet"
private def rejected := "another/caf%C3%A9%2Fx%255F_8_part-1.parquet"
private def missing := "zz-later/a%5Fb_7_part-0.parquet"

private def listing : Except PartitionPath.Error (List String) := do
  let keep ← encodePath [("region", some "a_b"), ("year", some "7")] "literal=parent" "part-0.parquet"
  let skip ← encodePath [("region", some "café/x%5F"), ("year", some "8")] "another" "part-1.parquet"
  return [keep, "nested/_common_metadata", skip, keep, "_SUCCESS"]

private def fixture : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet"⟩

private def ordinals : List Int32 := [-2147483648, 0, 17, 2147483647, -1]

private def lookup (path : String) : Except String Bytes :=
  if path == retained then .ok fixture else .error "literal snapshot missing"

private def keep : Scan.Predicate partitions.toScan Value :=
  fun row => (row ⟨0, by decide⟩).map (· == (7 : Int32))
private def projection : Scan.Projection (partitions.extend physical) :=
  Scan.Projection.ofArray #[⟨3, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]
private def zero : Scan.Projection (partitions.extend physical) := Scan.Projection.ofArray #[]

private abbrev RuntimeError := FileError (Int32ByteArray.Error String)

private def run (budget : Nat) (paths : List String) :=
  scan (partitions := partitions) (int32 := ordinal) (byteArray := payload)
    admission 128 keys .uri {} Int32ByteArray.Ingress.convert paths {} lookup projection keep budget

private def observes (budget : Nat) (add : List String) (expected : Events.Termination RuntimeError) : Bool :=
  match listing with
  | .error _ => false
  | .ok paths =>
    match run budget (paths ++ add) with
    | .error _ => false
    | .ok trace =>
      let region : Option Bytes := some ⟨"a_b".toUTF8⟩
      let once := ordinals.map fun id => (region, some id, some (7 : Int32), region)
      trace.batches.map (·.rowCount) == [3, 0, 2, 3, 0, 2] &&
        trace.rows.map (fun row =>
          ((row ⟨0, by decide⟩ : Option Bytes), (row ⟨1, by decide⟩ : Option Int32),
            (row ⟨2, by decide⟩ : Option Int32), (row ⟨3, by decide⟩ : Option Bytes))) == once ++ once &&
        decide (trace.termination = expected)

#guard listing.toOption == some [retained, "nested/_common_metadata", rejected, retained, "_SUCCESS"]
#guard observes 9 [] .closed
#guard observes 10 [] .eos
#guard observes 11 [missing] (.readError (.open missing (.lookup "literal snapshot missing")))

#guard match listing with
  | .error _ => false
  | .ok paths =>
    match scan (partitions := partitions) (int32 := ordinal) (byteArray := payload)
        admission 128 keys .uri {} Int32ByteArray.Ingress.convert paths {} lookup zero keep 10 with
    | .error _ => false
    | .ok trace => trace.batches.map (·.rowCount) == [3, 0, 2, 3, 0, 2] &&
        trace.rows.length == 10 && decide (trace.termination = .eos)

#guard match listing with
  | .error _ => false
  | .ok paths =>
    match prepareOrderedInventoryWithFileParser physical partitions admission
        (PartitionPath.Filename.parse 128 keys .uri) {} Int32ByteArray.Ingress.convert paths with
    | .error _ => false
    | .ok files =>
      let trace := scanInt32ByteArraySnapshotsBounded {} lookup projection keep 10 files
      files.map (·.path.declared) == [rejected, retained, retained] &&
        trace.batches.isEmpty &&
        decide (trace.termination = .readError (.open rejected (.lookup "literal snapshot missing")))

#guard match listing with
  | .error _ => false
  | .ok paths =>
    let resolve path := if path == rejected then .ok fixture else lookup path
    match scan (partitions := partitions) (int32 := ordinal) (byteArray := payload)
        admission 128 keys .uri {} Int32ByteArray.Ingress.convert paths {} resolve projection
        (fun _ => some true) 15 with
    | .error _ => false
    | .ok trace =>
      trace.batches.map (·.rowCount) == [3, 0, 2, 3, 0, 2, 3, 0, 2] &&
      trace.rows.map (fun row => (row ⟨0, by decide⟩ : Option Bytes)) ==
        List.replicate 5 (some ⟨"café/x%5F".toUTF8⟩) ++ List.replicate 10 (some ⟨"a_b".toUTF8⟩) &&
      trace.rows.map (fun row => (row ⟨1, by decide⟩ : Option Int32)) == (ordinals ++ ordinals ++ ordinals).map some &&
      trace.rows.map (fun row => (row ⟨2, by decide⟩ : Option Int32)) ==
        List.replicate 5 (some 8) ++ List.replicate 10 (some 7) &&
      decide (trace.termination = .eos)

#guard
  let invalid := "a%5Fb_invalid_part-0.parquet"
  match run 0 [retained, "_metadata", invalid] with
  | .ok _ => false
  | .error reason => reason == .entry 2 (.binding invalid (.conversion "year" (.invalidInt32 "invalid")))

#guard match run 0 [retained, "nested/_common_metadata", "../_SUCCESS"] with
  | .ok _ => false
  | .error reason => reason == .entry 2 (.relativePath "../_SUCCESS" .invalidSegment)

#print axioms prepareFile_of_render
#print axioms scan_eq_reference
#print axioms scan_eq_denotation_of_cost

end Silmaril.Formats.Hive.Manifest.RenderedFilename
