module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.PartitionPath.Filename.Thms
import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Scan.Thms
import Silmaril.Formats.Hive.Manifest.Inventory.Thms
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Hive.PartitionPath.Filename.Defs
meta import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Pruning.Defs

namespace Silmaril.Formats.Hive.PartitionPath.Filename

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet Silmaril.Relational
open Manifest
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open TypedPartitions (PartitionSchema)

private def keys := ["region", "year"]
private def fails (leaf : String) (expected : Error) : Bool :=
  match parse 128 keys .uri {} "" leaf with
  | .ok _ => false
  | .error reason => reason == expected

#guard (parse 128 keys .uri {} "region=ignored" "caf%C3%A9%5fblue_7_A%2Eparquet").toOption ==
  some [("region", some "café_blue"), ("year", some "7")]
#guard (parse 128 keys .literal {} "" "caf%C3%A9%5fblue_7_A%2Eparquet").toOption ==
  some [("region", some "caf%C3%A9%5fblue"), ("year", some "7")]
#guard (parse 128 keys .uri {} "" "x%255Fy_7_tail%GG").toOption ==
  some [("region", some "x%5Fy"), ("year", some "7")]
#guard (parse 9 [] .literal {} "" "f.parquet").toOption == some []
#guard fails "f.parquet" (.segmentArity 2 0)
#guard fails "west_7" (.segmentArity 2 1)
#guard fails "west_7_" .missingFilenameSuffix
#guard fails "west_7_file_name.parquet" (.segmentArity 2 3)
#guard fails "raw_underscore_7_f.parquet" (.segmentArity 2 3)
#guard fails "_7_f.parquet" .emptySegment
#guard fails "%GG_7_f.parquet" .invalidEscape
#guard fails "%FF_7_f.parquet" .invalidUtf8
#guard match parse 5 keys .literal {} "" "é_7_f" with
  | .ok _ => false
  | .error reason => reason == .filenameByteLimit 5 6
#guard (parse 6 keys .literal {} "" "é_7_f").toOption ==
  some [("region", some "é"), ("year", some "7")]

private def ordinal : Field := ⟨"ordinal", .required⟩
private def payload : Field := ⟨"payload", .optional⟩
private def physical := Int32ByteArrayGroup.File.schema ordinal payload
private def partitions : PartitionSchema Kind :=
  ⟨#[⟨"year", .int32 .optional, .reject⟩, ⟨"region", .byteArray .optional, .reject⟩]⟩
private def admit (encoding : Positional.Encoding) :=
  prepareOrderedInventoryWithFileParser physical partitions ⟨8, 128⟩ (parse 64 keys encoding)
    {} Int32ByteArray.Ingress.convert

private def escaped := "ignored=8/caf%C3%A9%5fblue_7_A%2Eparquet"
private def assigned := "plain/region=west_7_B.parquet"
private def rejected := "raw/unused_8_C.parquet"
private def listing := [rejected, assigned, "nested/_SUCCESS", escaped, escaped, "_metadata", "_common_metadata"]

#guard (admit .uri listing).toOption.map (List.map fun file => file.path.declared) ==
  some [escaped, escaped, assigned, rejected]
#guard (admit .literal ["nested/_SUCCESS", "_metadata", "_common_metadata"]).toOption.map List.length == some 0
#guard match admit .uri [escaped, "nested/_SUCCESS", "dir//west_7_F.parquet", assigned] with
  | .ok _ => false
  | .error reason =>
    reason == .entry 2 (.relativePath "dir//west_7_F.parquet" .invalidSegment)
#guard match admit .uri [escaped, "nested/_SUCCESS", "plain/west_7_file_name.parquet", assigned] with
  | .ok _ => false
  | .error reason =>
    reason == .entry 2 (.partitionPath "plain/west_7_file_name.parquet" (.segmentArity 2 3))
#guard match admit .uri ["plain/%5FSUCCESS", escaped] with
  | .ok _ => false
  | .error reason => reason == .entry 0 (.partitionPath "plain/%5FSUCCESS" (.segmentArity 2 0))
#guard match admit .uri ["../_metadata", escaped] with
  | .ok _ => false
  | .error reason => reason == .entry 0 (.relativePath "../_metadata" .invalidSegment)

private def fixture : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet"⟩
private def lookup (path : String) : Except String Bytes :=
  if path == escaped || path == assigned then .ok fixture else .error "literal key missing"

private def projection : Scan.Projection (partitions.extend physical) :=
  Scan.Projection.ofArray #[⟨3, by decide⟩, ⟨2, by decide⟩]
private def keep : Scan.Predicate partitions.toScan Value :=
  fun row => (row ⟨0, by decide⟩).map (· == (7 : Int32))

private def observes (encoding : Positional.Encoding) (first : String) (budget : Nat)
    (termination : Events.Termination (FileError (Int32ByteArray.Error String))) : Bool :=
  match admit encoding listing with
  | .error _ => false
  | .ok files =>
    let trace := scanInt32ByteArraySnapshotsBoundedSkippingRejected {} lookup projection keep budget files
    trace.batches.map (·.rowCount) == [3, 0, 2, 3, 0, 2, 3, 0, 2] &&
      trace.rows.map (fun row =>
        ((row ⟨0, by decide⟩ : Option Bytes), (row ⟨1, by decide⟩ : Option Int32))) ==
        List.replicate 10 (some ⟨first.toUTF8⟩, some 7) ++ List.replicate 5 (some ⟨"region=west".toUTF8⟩, some 7) &&
      decide (trace.termination = termination)

#guard observes .uri "café_blue" 15 .eos
#guard observes .literal "caf%C3%A9%5fblue" 15 .eos
#guard observes .uri "café_blue" 14 .closed

#print axioms parse_ok_iff
#print axioms parse_keys_present
#print axioms parse_parent_irrel
#print axioms prepareInventory_eq_uri_fileParser
#print axioms checkEntryWithFileParser_control
#print axioms prepareInventoryWithFileParser_paths
#print axioms prepareInventoryWithFileParser_eq_reference
#print axioms prepareOrderedInventoryWithFileParser_scanSkippingRejected_eq_reference

end Silmaril.Formats.Hive.PartitionPath.Filename
