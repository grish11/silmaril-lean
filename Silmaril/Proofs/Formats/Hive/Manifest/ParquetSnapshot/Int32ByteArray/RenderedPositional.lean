module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedPositional.Defs
import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Scan.Thms
import Silmaril.Formats.Hive.Manifest.Inventory.Thms
import Silmaril.Formats.Hive.PartitionPath.Positional.Render.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedPositional

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Hive Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.Manifest.RenderedPositional (MatchesRender fromOriginal)
open TypedPartitions (PartitionSchema Convert)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open PartitionPath.Positional (Encoding RenderLimits)

variable {Failure AdmissionError : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}

theorem scan_eq_reference
    (admission : Inventory.Limits) (renderLimits : RenderLimits) (keys : List String)
    (encoding : Encoding) (options : PartitionPath.Options) (convert : Convert Value AdmissionError)
    (listing : List String) (original : String → PartitionPath.Partition)
    (witness : MatchesRender admission renderLimits keys encoding options original listing)
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) :
    Manifest.RenderedPositional.scan admission renderLimits.maxDirectoryBytes keys encoding options convert listing
      limits lookup projection keep budget =
      (prepareInventoryReferenceWith (Int32ByteArrayGroup.File.schema int32 byteArray) partitions
        admission (fromOriginal renderLimits.maxDirectoryBytes original) options convert listing).map (fun files =>
          scanInt32ByteArraySnapshotsBounded limits lookup projection keep budget
            ((Inventory.orderFiles files).filter fun file => (keep file.cells).getD false)) := by
  unfold Manifest.RenderedPositional.scan
  rw [prepareOrderedInventoryWith_scanSkippingRejected_eq_reference]
  congr 1
  unfold prepareInventoryReferenceWith
  apply prepareInventoryReferenceWithFileParser_congr
  intro path included pathFits directory leaf lexical control
  change PartitionPath.Positional.parse renderLimits.maxDirectoryBytes keys encoding options directory =
    fromOriginal renderLimits.maxDirectoryBytes original options directory
  by_cases fits : directory.utf8ByteSize ≤ renderLimits.maxDirectoryBytes
  · obtain ⟨canonical, rendered, spelling⟩ := witness path included pathFits directory leaf lexical control fits
    rw [PartitionPath.Positional.parse_of_rendered_spelling rendered fits spelling]
    simp [fromOriginal, Nat.not_lt.mpr fits]
  · simp [PartitionPath.Positional.parse, fromOriginal, Nat.lt_of_not_ge fits]

end Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedPositional
