module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Bounded.Defs
public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Thms
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Bounded.Thms

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Failure : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}

/-- Every paired manifest has a witness through EOS or its first reached error. -/
theorem int32ByteArrayScanCost_exists (limits : Int32ByteArrayGroup.File.Limits) (int32 byteArray : Field)
    (lookup : String → Except Failure Bytes) (files : List (File partitions Value)) :
    ∃ actions, Int32ByteArrayScanCost limits int32 byteArray lookup files actions :=
  scanCost_exists _ (int32ByteArraySnapshotOpener_fullConsumption limits int32 byteArray partitions lookup) files

/-- Sufficient budget recovers the complete paired manifest denotation. -/
theorem scanInt32ByteArraySnapshotsBounded_eq_reference_of_cost (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) {budget actions : Nat} {files : List (File partitions Value)}
    (cost : Int32ByteArrayScanCost limits int32 byteArray lookup files actions) (enough : actions ≤ budget) :
    scanInt32ByteArraySnapshotsBounded limits lookup projection keep budget files =
      denoteInt32ByteArraySnapshots limits lookup projection keep files :=
  (scanBounded_eq_scan_of_cost _ (int32ByteArraySnapshotOpener_fullConsumption limits int32 byteArray partitions lookup)
    projection keep cost enough).trans (scanInt32ByteArraySnapshots_eq_reference limits lookup projection keep files)

/-- Below the witnessed cost the paired scan closes. Its aligned batches at
any budget are a prefix of the complete denotation, including zero widths. -/
theorem scanInt32ByteArraySnapshotsBounded_exact_boundary (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) {budget actions : Nat} {files : List (File partitions Value)}
    (cost : Int32ByteArrayScanCost limits int32 byteArray lookup files actions) :
    let bounded := scanInt32ByteArraySnapshotsBounded limits lookup projection keep budget files
    let strict := denoteInt32ByteArraySnapshots limits lookup projection keep files
    (bounded.termination = .closed ↔ budget < actions) ∧ List.IsPrefix bounded.batches strict.batches := by
  simpa only [scanInt32ByteArraySnapshotsBounded, scanInt32ByteArraySnapshots_eq_reference] using
    (scanBounded_exact_boundary _ (int32ByteArraySnapshotOpener_fullConsumption limits int32 byteArray partitions lookup)
      projection keep (budget := budget) cost)

end Silmaril.Formats.Hive.Manifest
