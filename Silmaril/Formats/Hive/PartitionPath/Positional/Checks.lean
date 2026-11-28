module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.PartitionPath.Positional.Thms
import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Scan.Thms
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Hive.PartitionPath.Positional.Defs
meta import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Pruning.Defs

namespace Silmaril.Formats.Hive.PartitionPath.Positional

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet Silmaril.Relational
open Manifest
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open TypedPartitions (PartitionSchema)

private def keys := ["region", "year"]
private def fails (encoding : Encoding) (directory : String) (expected : Error) : Bool :=
  match parse 128 keys encoding {} directory with
  | .ok _ => false
  | .error reason => reason == expected

#guard (parse 128 keys .uri {} "caf%C3%A9%2fblue/7").toOption ==
  some [("region", some "café/blue"), ("year", some "7")]
#guard (parse 128 keys .literal {} "caf%C3%A9%2fblue/7").toOption ==
  some [("region", some "caf%C3%A9%2fblue"), ("year", some "7")]
#guard (parse 128 keys .uri {} "region=west/7").toOption ==
  some [("region", some "region=west"), ("year", some "7")]
#guard fails .uri "west" (.segmentArity 2 1)
#guard fails .uri "west/7/ignored" (.segmentArity 2 3)
#guard fails .uri "/7" .emptySegment
#guard fails .uri "%GG/7" .invalidEscape
#guard fails .uri "%FF/7" .invalidUtf8
#guard (parse 128 keys .literal {} "%FF/7").toOption ==
  some [("region", some "%FF"), ("year", some "7")]
#guard (parse 0 [] .literal {} "").toOption == some []
#guard match parse 3 keys .literal {} "é/7" with
  | .ok _ => false
  | .error reason => reason == .directoryByteLimit 3 4
#guard (parse 4 keys .literal {} "é/7").toOption ==
  some [("region", some "é"), ("year", some "7")]
#guard match parse 128 ["region", "region"] .uri {} "west/7" with
  | .ok _ => false
  | .error reason => reason == .duplicateKey "region"
#guard (parse 128 keys .uri {} "%5f_HIVE_DEFAULT_PARTITION__/7").toOption ==
  some [("region", some "__HIVE_DEFAULT_PARTITION__"), ("year", some "7")]

private def ordinal : Field := ⟨"ordinal", .required⟩
private def payload : Field := ⟨"payload", .optional⟩
private def physical := Int32ByteArrayGroup.File.schema ordinal payload
private def partitions : PartitionSchema Kind :=
  ⟨#[⟨"year", .int32 .optional, .reject⟩, ⟨"region", .byteArray .optional, .reject⟩]⟩
private def admit (encoding : Encoding) (options : Options) :=
  prepareOrderedInventoryWith physical partitions ⟨6, 128⟩ (parse 128 keys encoding)
    options Int32ByteArray.Ingress.convert

private def escaped := "caf%C3%A9%2fblue/7/A%2Eparquet"
private def assigned := "region=west/7/B.parquet"
private def rejected := "z/8/C.parquet"
private def marker := "__HIVE_DEFAULT_PARTITION__/7/D.parquet"
private def listing := [rejected, assigned, "_metadata", escaped, escaped]

#guard (admit .uri {} listing).toOption.map (List.map (·.path.declared)) ==
  some [escaped, escaped, assigned, rejected]
#guard match admit .uri {} [escaped, "_metadata", "west/F.parquet", assigned] with
  | .ok _ => false
  | .error reason => reason == .entry 2 (.partitionPath "west/F.parquet" (.segmentArity 2 1))
#guard match admit .uri {} [marker] with
  | .ok _ => false
  | .error reason => reason == .entry 0 (.partitionPath marker (.nullMarkerCollision "region"))
#guard (admit .uri {nullMarker := "other marker"} [marker]).toOption.map
    (List.map fun file => (file.cells ⟨1, by decide⟩ : Option Bytes)) ==
  some [some ⟨"__HIVE_DEFAULT_PARTITION__".toUTF8⟩]

private def fixture : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet"⟩
private def lookup (path : String) : Except String Bytes :=
  if path == escaped || path == assigned then .ok fixture else .error "literal key missing"

private def projection : Scan.Projection (partitions.extend physical) :=
  Scan.Projection.ofArray #[⟨3, by decide⟩, ⟨2, by decide⟩]
private def keep : Scan.Predicate partitions.toScan Value :=
  fun row => (row ⟨0, by decide⟩).map (· == (7 : Int32))

private def observes (encoding : Encoding) (first : String) (budget : Nat)
    (termination : Events.Termination (FileError (Int32ByteArray.Error String))) : Bool :=
  match admit encoding {} listing with
  | .error _ => false
  | .ok files =>
    let trace := scanInt32ByteArraySnapshotsBoundedSkippingRejected {} lookup projection keep budget files
    trace.batches.map (·.rowCount) == [3, 0, 2, 3, 0, 2, 3, 0, 2] &&
      trace.rows.map (fun row =>
        ((row ⟨0, by decide⟩ : Option Bytes), (row ⟨1, by decide⟩ : Option Int32))) ==
        List.replicate 10 (some ⟨first.toUTF8⟩, some 7) ++ List.replicate 5 (some ⟨"region=west".toUTF8⟩, some 7) &&
      decide (trace.termination = termination)

#guard observes .uri "café/blue" 15 .eos
#guard observes .literal "caf%C3%A9%2fblue" 15 .eos
#guard observes .uri "café/blue" 14 .closed

#print axioms parse_ok_iff
#print axioms parse_keys_present

end Silmaril.Formats.Hive.PartitionPath.Positional
