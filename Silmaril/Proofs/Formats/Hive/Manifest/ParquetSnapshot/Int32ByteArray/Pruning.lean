module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Pruning.Defs
public import Silmaril.Formats.Hive.Manifest.Pruning.Defs
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Bounded.Thms
import Silmaril.Formats.Hive.Manifest.Pruning.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Failure : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}

theorem scanInt32ByteArraySnapshotsBoundedSkippingRejected_exact_boundary
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) {budget actions : Nat} {files : List (File partitions Value)}
    (cost : Int32ByteArrayPrunedScanCost limits int32 byteArray lookup keep files actions) :
    let bounded := scanInt32ByteArraySnapshotsBoundedSkippingRejected limits lookup projection keep budget files
    let complete := scanSkippingRejected
      (int32ByteArraySnapshotOpener limits int32 byteArray partitions lookup) projection keep files
    (bounded.termination = .closed ↔ budget < actions) ∧ List.IsPrefix bounded.batches complete.batches := by
  rw [scanSkippingRejected_eq_scan_filter, scanInt32ByteArraySnapshots_eq_reference]
  exact scanInt32ByteArraySnapshotsBounded_exact_boundary limits lookup projection keep cost

theorem scanInt32ByteArraySnapshotsBoundedSkippingRejected_eq_scan_of_cost
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) {budget actions : Nat} {files : List (File partitions Value)}
    (cost : Int32ByteArrayPrunedScanCost limits int32 byteArray lookup keep files actions)
    (enough : actions ≤ budget) :
    scanInt32ByteArraySnapshotsBoundedSkippingRejected limits lookup projection keep budget files =
      scanSkippingRejected (int32ByteArraySnapshotOpener limits int32 byteArray partitions lookup)
        projection keep files := by
  rw [scanSkippingRejected_eq_scan_filter, scanInt32ByteArraySnapshots_eq_reference]
  exact scanInt32ByteArraySnapshotsBounded_eq_reference_of_cost limits lookup projection keep cost enough

theorem scanInt32ByteArraySnapshotsBoundedSkippingRejected_eq_strict_of_reached_eof
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) {budget actions : Nat} {files : List (File partitions Value)}
    (safe : ReachedRejectedFilesReachEOF
      (int32ByteArraySnapshotOpener limits int32 byteArray partitions lookup) projection keep files)
    (cost : Int32ByteArrayPrunedScanCost limits int32 byteArray lookup keep files actions)
    (enough : actions ≤ budget) :
    scanInt32ByteArraySnapshotsBoundedSkippingRejected limits lookup projection keep budget files =
      denoteInt32ByteArraySnapshots limits lookup projection keep files := by
  rw [scanInt32ByteArraySnapshotsBoundedSkippingRejected_eq_scan_of_cost limits lookup projection keep cost enough,
    scanSkippingRejected_eq_scan_of_reached_eof _ projection keep files safe,
    scanInt32ByteArraySnapshots_eq_reference limits lookup projection keep]

end Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray
