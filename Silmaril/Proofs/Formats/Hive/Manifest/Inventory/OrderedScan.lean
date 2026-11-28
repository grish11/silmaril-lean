module

public import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Defs
public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Pruning.Defs
import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Thms
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Bounded.Thms
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.Inventory

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Failure : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}

theorem scanOrderedSkippingRejected_congr_lookup
    (limits : Int32ByteArrayGroup.File.Limits) {left right : String → Except Failure Bytes}
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) (files : List (File partitions Value))
    (agree : ∀ file ∈ files, (keep file.cells).getD false = true →
      left file.path.declared = right file.path.declared) :
    scanInt32ByteArraySnapshotsBoundedSkippingRejected limits left projection keep budget
      (Inventory.orderFiles files) =
    scanInt32ByteArraySnapshotsBoundedSkippingRejected limits right projection keep budget
      (Inventory.orderFiles files) := by
  unfold scanInt32ByteArraySnapshotsBoundedSkippingRejected scanInt32ByteArraySnapshotsBounded
  apply scanBounded_congr_opener
  intro file retained
  obtain ⟨member, kept⟩ := List.mem_filter.mp retained
  exact int32ByteArraySnapshotOpener_congr_lookup limits int32 byteArray partitions
    (agree file ((Inventory.orderFiles_perm files).mem_iff.mp member) kept)

end Silmaril.Proofs.Formats.Hive.Manifest.Inventory
