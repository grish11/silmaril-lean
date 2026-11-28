module

public import Silmaril.Formats.Hive.PartitionPath.Filename.Render.Defs
public import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Defs
public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Pruning.Defs

/-! Read rendered filename partitions through the shared ordered inventory. -/

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest.RenderedFilename

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Failure AdmissionError : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}

/-- Check the listing, bind filename cells and run the existing bounded
skip-open scan on the ordered manifest. -/
def scan (admission : Inventory.Limits) (maxFilenameBytes : Nat) (keys : List String)
    (encoding : PartitionPath.Positional.Encoding) (options : PartitionPath.Options)
    (convert : Convert Value AdmissionError) (listing : List String)
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) :
    Except (Inventory.Error AdmissionError)
      (Events.Trace projection.schema Value (FileError (Int32ByteArray.Error Failure))) :=
  (prepareOrderedInventoryWithFileParser (Int32ByteArrayGroup.File.schema int32 byteArray) partitions
    admission (PartitionPath.Filename.parse maxFilenameBytes keys encoding) options convert listing).map
      (scanInt32ByteArraySnapshotsBoundedSkippingRejected limits lookup projection keep budget)

/-- The source entries are supplied independently of filename decoding.
Only affordable, lexically valid data occurrences need a render witness. -/
def MatchesRender (admission : Inventory.Limits) (maxFilenameBytes : Nat) (keys : List String)
    (encoding : PartitionPath.Positional.Encoding) (options : PartitionPath.Options)
    (original : String → PartitionPath.Partition) (listing : List String) : Prop :=
  ∀ path ∈ listing.take admission.maxEntries, path.utf8ByteSize ≤ admission.maxPathBytes →
    ∀ parent leaf, splitFile path = .ok (parent, leaf) → Inventory.isControlLeaf leaf = false →
      ∃ suffix, PartitionPath.Filename.render maxFilenameBytes keys encoding options (original leaf) suffix = .ok leaf

end Silmaril.Formats.Hive.Manifest.RenderedFilename
