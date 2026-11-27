module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedFilename.Defs
import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Scan.Thms
import Silmaril.Formats.Hive.Manifest.Inventory.Thms
import Silmaril.Formats.Hive.PartitionPath.Filename.Render.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedFilename

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Hive Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.Manifest.RenderedFilename (MatchesRender)
open TypedPartitions (PartitionSchema Convert)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Failure AdmissionError : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}

private theorem reference_eq_original
    (physical : Scan.Schema String Kind) (admission : Inventory.Limits)
    (maxFilenameBytes : Nat) (keys : List String) (encoding : PartitionPath.Positional.Encoding) (options : PartitionPath.Options)
    (convert : Convert Value AdmissionError) (listing : List String) (original : String → PartitionPath.Partition)
    (witness : MatchesRender admission maxFilenameBytes keys encoding options original listing) :
    prepareInventoryReferenceWithFileParser physical partitions admission (PartitionPath.Filename.parse maxFilenameBytes keys encoding)
        options convert listing =
      prepareInventoryReferenceWithFileParser physical partitions admission
        (fun _ _ leaf => .ok (original leaf)) options convert listing := by
  apply prepareInventoryReferenceWithFileParser_congr
  intro path included fits parent leaf lexical control
  obtain ⟨suffix, rendered⟩ := witness path included fits parent leaf lexical control
  exact PartitionPath.Filename.parse_render_of_ok rendered parent

theorem scan_eq_reference
    (admission : Inventory.Limits) (maxFilenameBytes : Nat) (keys : List String)
    (encoding : PartitionPath.Positional.Encoding) (options : PartitionPath.Options)
    (convert : Convert Value AdmissionError) (listing : List String)
    (original : String → PartitionPath.Partition)
    (witness : MatchesRender admission maxFilenameBytes keys encoding options original listing)
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) :
    Manifest.RenderedFilename.scan admission maxFilenameBytes keys encoding options convert listing
      limits lookup projection keep budget =
      (prepareInventoryReferenceWithFileParser (Int32ByteArrayGroup.File.schema int32 byteArray) partitions
        admission (fun _ _ leaf => .ok (original leaf)) options convert listing).map (fun files =>
          scanInt32ByteArraySnapshotsBounded limits lookup projection keep budget
            ((Inventory.orderFiles files).filter fun file => (keep file.cells).getD false)) := by
  unfold Manifest.RenderedFilename.scan
  rw [prepareOrderedInventoryWithFileParser_scanSkippingRejected_eq_reference,
    reference_eq_original _ admission maxFilenameBytes keys encoding options convert listing original witness]

end Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedFilename
