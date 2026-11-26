module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Pruning.Defs
public import Silmaril.Formats.Hive.Manifest.Pruning.Defs
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Bounded.Thms
import Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Pruning

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Failure : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}

/-- The retained occurrences have a cost witness, even when one of them fails. -/
theorem int32ByteArrayPrunedScanCost_exists (limits : Int32ByteArrayGroup.File.Limits) (int32 byteArray : Field)
    (lookup : String → Except Failure Bytes) (keep : Scan.Predicate partitions.toScan Value)
    (files : List (File partitions Value)) :
    ∃ actions, Int32ByteArrayPrunedScanCost limits int32 byteArray lookup keep files actions :=
  int32ByteArrayScanCost_exists limits int32 byteArray lookup (files.filter fun file => (keep file.cells).getD false)

/-- The cutoff counts only retained actions. Emitted batches are a prefix of
the complete skip-open trace, including their row counts at zero width. -/
theorem scanInt32ByteArraySnapshotsBoundedSkippingRejected_exact_boundary
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) {budget actions : Nat} {files : List (File partitions Value)}
    (cost : Int32ByteArrayPrunedScanCost limits int32 byteArray lookup keep files actions) :
    let bounded := scanInt32ByteArraySnapshotsBoundedSkippingRejected limits lookup projection keep budget files
    let complete := scanSkippingRejected
      (int32ByteArraySnapshotOpener limits int32 byteArray partitions lookup) projection keep files
    (bounded.termination = .closed ↔ budget < actions) ∧ List.IsPrefix bounded.batches complete.batches :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.scanInt32ByteArraySnapshotsBoundedSkippingRejected_exact_boundary
    limits lookup projection keep cost

/-- Sufficient retained budget gives the complete skip-open trace. -/
theorem scanInt32ByteArraySnapshotsBoundedSkippingRejected_eq_scan_of_cost
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) {budget actions : Nat} {files : List (File partitions Value)}
    (cost : Int32ByteArrayPrunedScanCost limits int32 byteArray lookup keep files actions)
    (enough : actions ≤ budget) :
    scanInt32ByteArraySnapshotsBoundedSkippingRejected limits lookup projection keep budget files =
      scanSkippingRejected (int32ByteArraySnapshotOpener limits int32 byteArray partitions lookup)
        projection keep files :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.scanInt32ByteArraySnapshotsBoundedSkippingRejected_eq_scan_of_cost
    limits lookup projection keep cost enough

/-- With enough budget for the retained occurrences, recover the strict
trace when each reached rejected file would complete its checked read to EOS.
Retained typed failures and their exact preceding batches are preserved. -/
theorem scanInt32ByteArraySnapshotsBoundedSkippingRejected_eq_strict_of_reached_eof
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) {budget actions : Nat} {files : List (File partitions Value)}
    (safe : ReachedRejectedFilesReachEOF
      (int32ByteArraySnapshotOpener limits int32 byteArray partitions lookup) projection keep files)
    (cost : Int32ByteArrayPrunedScanCost limits int32 byteArray lookup keep files actions)
    (enough : actions ≤ budget) :
    scanInt32ByteArraySnapshotsBoundedSkippingRejected limits lookup projection keep budget files =
      denoteInt32ByteArraySnapshots limits lookup projection keep files :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.scanInt32ByteArraySnapshotsBoundedSkippingRejected_eq_strict_of_reached_eof
    limits lookup projection keep safe cost enough

end Silmaril.Formats.Hive.Manifest
