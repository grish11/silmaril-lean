module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.PartitionPath.Positional.Render.Thms
import Silmaril.Formats.Hive.PartitionPath.Thms
import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Scan.Thms
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Hive.PartitionPath.Positional.Render.Defs
meta import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Pruning.Defs

namespace Silmaril.Formats.Hive.PartitionPath.Positional

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet Silmaril.Relational
open Manifest
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open TypedPartitions (PartitionSchema)

private def limits : RenderLimits := ⟨128, 64⟩
private def keys := ["region", "year"]
private def entries (region : String) : Partition := [("region", some region), ("year", some "7")]
private def uriValue := "café/blue=%5F:west\\x"
private def literalValue := "café=blue%5F_west"
private def uriDirectory := "caf%C3%A9%2Fblue%3D%255F%3Awest%5Cx/7"
private def lowerEscape := "caf%C3%A9%2fblue%3D%255F%3Awest%5Cx/7"
private def marker := "__HIVE_DEFAULT_PARTITION__"

private def fails (result : Except RenderError String) (expected : RenderError) : Bool :=
  match result with
  | .ok _ => false
  | .error reason => reason == expected

#guard (render limits keys .uri {} (entries uriValue)).toOption == some uriDirectory
#guard (render limits keys .literal {} (entries literalValue)).toOption == some (literalValue ++ "/7")
#guard (render ⟨0, 0⟩ [] .literal {} []).toOption == some ""
#guard (render ⟨4, 2⟩ keys .literal {} (entries "é")).toOption == some "é/7"
#guard fails (render ⟨3, 2⟩ keys .literal {} (entries "é")) (.partition (.directoryByteLimit 3 4))
#guard fails (render ⟨128, 5⟩ keys .uri {} (entries "é")) (.segmentByteLimit "region" 5 6)
#guard fails (render limits keys .uri {} (entries "")) (.partition .emptySegment)
#guard fails (render limits keys .literal {} (entries uriValue)) (.unsafeSegment "region")
#guard fails (render limits keys .uri {} (entries ".")) (.unsafeSegment "region")
#guard fails (render limits keys .literal {} (entries "..")) (.unsafeSegment "region")
#guard fails (render limits keys .literal {} (entries "raw:colon")) (.unsafeSegment "region")
#guard fails (render limits keys .literal {} (entries (String.singleton (Char.ofNat 0)))) (.unsafeSegment "region")
#guard fails (render limits keys .uri {} (entries "west").reverse) .keyOrder
#guard fails (render limits ["year", "year"] .uri {} [("year", some "7"), ("year", some "8")])
  (.partition (.duplicateKey "year"))
#guard fails (render limits keys .uri {requiredKeys := ["extra"]} (entries "west"))
  (.partition (.missingKey "extra"))
#guard fails (render limits keys .uri {} [("region", none), ("year", some "7")]) (.nullValue "region")
#guard fails (render limits keys .uri {} (entries marker)) (.partition (.nullMarkerCollision "region"))
#guard (render limits keys .uri {nullMarker := "different"} (entries marker)).toOption == some (marker ++ "/7")

private def ordinal : Field := ⟨"ordinal", .required⟩
private def payload : Field := ⟨"payload", .optional⟩
private def physical := Int32ByteArrayGroup.File.schema ordinal payload
private def partitions : PartitionSchema Kind :=
  ⟨#[⟨"year", .int32 .optional, .reject⟩, ⟨"region", .byteArray .optional, .reject⟩]⟩

private def fixture : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet"⟩

private def observes (encoding : Encoding) (region : String) (aliases : List String) : Bool := Id.run do
  let .ok directory := render limits keys encoding {} (entries region) | return false
  let generated := directory ++ "/part.parquet"
  let dataPaths := generated :: aliases
  let .ok files := prepareOrderedInventoryWith physical partitions ⟨4, 160⟩
    (parse limits.maxDirectoryBytes keys encoding) {} Int32ByteArray.Ingress.convert
      (generated :: "_SUCCESS" :: aliases) | return false
  let lookup path : Except String Bytes :=
    if dataPaths.contains path then .ok fixture else .error "literal key missing"
  let projection : Scan.Projection (partitions.extend physical) :=
    Scan.Projection.ofArray #[⟨3, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩]
  let trace := scanInt32ByteArraySnapshotsBoundedSkippingRejected {} lookup projection
    (fun _ => some true) (5 * dataPaths.length) files
  let ordinals : List Int32 := [-2147483648, 0, 17, 2147483647, -1]
  let expected := ordinals.map fun id => (some ⟨region.toUTF8⟩, some id, some (7 : Int32))
  return files.map (·.path.declared) == dataPaths &&
    trace.batches.map (·.rowCount) == (dataPaths.flatMap fun _ => [3, 0, 2]) &&
    trace.rows.map (fun row =>
      ((row ⟨0, by decide⟩ : Option Bytes), (row ⟨1, by decide⟩ : Option Int32),
        (row ⟨2, by decide⟩ : Option Int32))) == dataPaths.flatMap (fun _ => expected) &&
    decide (trace.termination = .eos)

#guard observes .uri uriValue [lowerEscape ++ "/B%2Eparquet"]
#guard observes .literal literalValue []

#print axioms Silmaril.Formats.Hive.PartitionPath.splitOn_slash_intercalate
#print axioms render_spec
#print axioms parse_render_of_ok

end Silmaril.Formats.Hive.PartitionPath.Positional
