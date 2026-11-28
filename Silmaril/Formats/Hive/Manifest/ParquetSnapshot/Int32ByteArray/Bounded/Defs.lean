module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Bounded.Defs
public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Defs

/-! One logical action budget for the checked mixed Hive snapshot profile. -/

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Failure : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}

/-- Use the paired source and the common manifest budget. Each attempted
literal open, group pull, and explicit file EOS pull consumes one action. -/
@[expose] def scanInt32ByteArraySnapshotsBounded (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) :
    Nat → List (File partitions Value) → Events.Trace projection.schema Value (FileError (Int32ByteArray.Error Failure)) :=
  scanBounded (int32ByteArraySnapshotOpener limits int32 byteArray partitions lookup) projection keep

/-- Count paired snapshot actions through manifest EOS or the first failure. -/
abbrev Int32ByteArrayScanCost (limits : Int32ByteArrayGroup.File.Limits) (int32 byteArray : Field)
    (lookup : String → Except Failure Bytes) :
    List (File partitions Value) → Nat → Prop :=
  ScanCost (int32ByteArraySnapshotOpener limits int32 byteArray partitions lookup)

end Silmaril.Formats.Hive.Manifest
