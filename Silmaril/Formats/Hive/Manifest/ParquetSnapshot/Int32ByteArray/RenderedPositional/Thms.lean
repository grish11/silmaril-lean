module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedPositional.Defs
import Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedPositional

public section

namespace Silmaril.Formats.Hive.Manifest.RenderedPositional

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open PartitionPath.Positional (Encoding RenderLimits)

variable {Failure AdmissionError : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}

/-- Exact bounded trace or original-index admission error. The reference
binds the supplied entries directly before stably sorting and pruning
literal file occurrences. The full trace includes aligned batches,
cutoff, and the first reached retained error. -/
theorem scan_eq_reference
    (admission : Inventory.Limits) (renderLimits : RenderLimits) (keys : List String)
    (encoding : Encoding) (options : PartitionPath.Options) (convert : Convert Value AdmissionError)
    (listing : List String) (original : String → PartitionPath.Partition)
    (witness : MatchesRender admission renderLimits keys encoding options original listing)
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) :
    scan admission renderLimits.maxDirectoryBytes keys encoding options convert listing
      limits lookup projection keep budget =
      (prepareInventoryReferenceWith (Int32ByteArrayGroup.File.schema int32 byteArray) partitions
        admission (fromOriginal renderLimits.maxDirectoryBytes original) options convert listing).map (fun files =>
          scanInt32ByteArraySnapshotsBounded limits lookup projection keep budget
            ((Inventory.orderFiles files).filter fun file => (keep file.cells).getD false)) :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedPositional.scan_eq_reference
    admission renderLimits keys encoding options convert listing original witness limits lookup projection keep budget

end Silmaril.Formats.Hive.Manifest.RenderedPositional
