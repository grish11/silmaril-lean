module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Defs
import Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Failure : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}

/-- The strict scan agrees with the independent ordered group fold on exact
projected batches and the first reached typed outcome, including for filtered
files. Retained empty groups and zero-width batches keep their row counts. -/
theorem scanInt32ByteArraySnapshots_eq_reference (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (files : List (File partitions Value)) :
    scan (int32ByteArraySnapshotOpener limits int32 byteArray partitions lookup) projection keep files =
      denoteInt32ByteArraySnapshots limits lookup projection keep files :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.scanInt32ByteArraySnapshots_eq_reference
    limits lookup projection keep files

/-- The collected typed rows and termination agree with the group fold. -/
theorem scanInt32ByteArraySnapshots_collect_eq_rows (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (files : List (File partitions Value)) :
    (scan (int32ByteArraySnapshotOpener limits int32 byteArray partitions lookup) projection keep files).collect =
      (denoteInt32ByteArraySnapshots limits lookup projection keep files).collect :=
  congrArg Events.Trace.collect (scanInt32ByteArraySnapshots_eq_reference limits lookup projection keep files)

end Silmaril.Formats.Hive.Manifest
