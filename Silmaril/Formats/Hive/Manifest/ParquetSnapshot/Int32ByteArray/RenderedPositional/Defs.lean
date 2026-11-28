module

public import Silmaril.Formats.Hive.PartitionPath.Positional.Render.Defs
public import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Defs
public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Pruning.Defs

/-! Ordered, bounded snapshot scans of positional directory listings. -/

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest.RenderedPositional

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open PartitionPath.Positional (Encoding RenderLimits SameDecodedSegments)

variable {Failure AdmissionError : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}

/-- Admit in original listing order, then order literal keys and scan the
retained occurrences with the shared paired Parquet reader. -/
def scan (admission : Inventory.Limits) (maxDirectoryBytes : Nat) (keys : List String)
    (encoding : Encoding) (options : PartitionPath.Options) (convert : Convert Value AdmissionError)
    (listing : List String) (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) :
    Except (Inventory.Error AdmissionError)
      (Events.Trace projection.schema Value (FileError (Int32ByteArray.Error Failure))) :=
  (prepareOrderedInventoryWith (Int32ByteArrayGroup.File.schema int32 byteArray) partitions
    admission (PartitionPath.Positional.parse maxDirectoryBytes keys encoding) options convert listing).map
      (scanInt32ByteArraySnapshotsBoundedSkippingRejected limits lookup projection keep budget)

/-- Each affordable data parent is either the rendering of its supplied
entries or another spelling with the same ordered segment decoding.
Controls, rejected lexical paths and oversized paths need no witness. -/
def MatchesRender (admission : Inventory.Limits) (renderLimits : RenderLimits)
    (keys : List String) (encoding : Encoding) (options : PartitionPath.Options)
    (original : String → PartitionPath.Partition) (listing : List String) : Prop :=
  ∀ path ∈ listing.take admission.maxEntries, path.utf8ByteSize ≤ admission.maxPathBytes →
    ∀ directory leaf, splitFile path = .ok (directory, leaf) → Inventory.isControlLeaf leaf = false →
      directory.utf8ByteSize ≤ renderLimits.maxDirectoryBytes →
        ∃ canonical, PartitionPath.Positional.render renderLimits keys encoding options (original directory) =
          .ok canonical ∧ SameDecodedSegments encoding directory canonical

/-- Reference admission takes the independently supplied entries after
checking the input directory cap. The shared binder still checks the schema. -/
def fromOriginal (maxDirectoryBytes : Nat) (original : String → PartitionPath.Partition) :
    DirectoryParser := fun _ directory =>
  if directory.utf8ByteSize > maxDirectoryBytes then
    .error (.directoryByteLimit maxDirectoryBytes directory.utf8ByteSize)
  else .ok (original directory)

end Silmaril.Formats.Hive.Manifest.RenderedPositional
