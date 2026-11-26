module

public import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Thms
public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Pruning.Thms
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Bounded.Thms
import Silmaril.Proofs.Formats.Hive.Manifest.Inventory.OrderedScan

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Failure AdmissionError : Type} {int32 byteArray : Field}
variable {partitions : PartitionSchema Kind}

/-- Admission keeps the original listing's typed errors. On success, the
existing bounded scan visits the stable sorted sequence of retained records.
The equality includes aligned batches, budget cutoff, and the first reached
terminal failure and original literal path. -/
theorem prepareOrderedInventoryWith_scanSkippingRejected_eq_reference
    (admission : Inventory.Limits) (parse : DirectoryParser) (options : PartitionPath.Options)
    (convert : Convert Value AdmissionError) (listing : List String)
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) :
    (prepareOrderedInventoryWith (Int32ByteArrayGroup.File.schema int32 byteArray) partitions
      admission parse options convert listing).map
        (scanInt32ByteArraySnapshotsBoundedSkippingRejected limits lookup projection keep budget) =
      (prepareInventoryReferenceWith (Int32ByteArrayGroup.File.schema int32 byteArray) partitions
        admission parse options convert listing).map (fun files =>
          scanInt32ByteArraySnapshotsBounded limits lookup projection keep budget
            ((Inventory.orderFiles files).filter fun file => (keep file.cells).getD false)) := by
  rw [prepareOrderedInventoryWith_eq_reference]
  cases prepareInventoryReferenceWith _ _ admission parse options convert listing <;> rfl

/-- Admission keeps the original listing's typed errors. On success, the
existing bounded scan visits the stable sorted sequence of retained records.
The equality includes aligned batches, budget cutoff, and the first reached
terminal failure and original literal path. -/
theorem prepareOrderedInventory_scanSkippingRejected_eq_reference
    (admission : Inventory.Limits) (options : PartitionPath.Options)
    (convert : Convert Value AdmissionError) (listing : List String)
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) :
    (prepareOrderedInventory (Int32ByteArrayGroup.File.schema int32 byteArray) partitions
      admission options convert listing).map
        (scanInt32ByteArraySnapshotsBoundedSkippingRejected limits lookup projection keep budget) =
      (prepareInventoryReference (Int32ByteArrayGroup.File.schema int32 byteArray) partitions
        admission options convert listing).map (fun files =>
          scanInt32ByteArraySnapshotsBounded limits lookup projection keep budget
            ((Inventory.orderFiles files).filter fun file => (keep file.cells).getD false)) := by
  exact prepareOrderedInventoryWith_scanSkippingRejected_eq_reference
    admission PartitionPath.parse options convert listing limits lookup projection keep budget

/-- On a successfully ordered manifest, resolving only retained literal keys
suffices. The scan passes just the filtered occurrences to bounded traversal.
When a key has both a retained and a rejected occurrence, agreement is still
required for the retained occurrence. -/
theorem scanOrderedSkippingRejected_congr_lookup
    (limits : Int32ByteArrayGroup.File.Limits) {left right : String → Except Failure Bytes}
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) (files : List (File partitions Value))
    (agree : ∀ file ∈ files, (keep file.cells).getD false = true →
      left file.path.declared = right file.path.declared) :
    scanInt32ByteArraySnapshotsBoundedSkippingRejected limits left projection keep budget
      (Inventory.orderFiles files) =
    scanInt32ByteArraySnapshotsBoundedSkippingRejected limits right projection keep budget
      (Inventory.orderFiles files) :=
  Proofs.Formats.Hive.Manifest.Inventory.scanOrderedSkippingRejected_congr_lookup
    limits projection keep budget files agree

end Silmaril.Formats.Hive.Manifest
