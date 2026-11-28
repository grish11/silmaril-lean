module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Bounded.Defs

/-! Opt-in skip-open pruning with one budget for a paired Hive manifest. -/

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Failure : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}

/-- Filter the pure manifest before any checked open. Rejected occurrences
spend no actions and supply no errors. Retained occurrences keep their order,
multiplicity, and the usual open, group, and explicit EOS charges. -/
@[expose] def scanInt32ByteArraySnapshotsBoundedSkippingRejected
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) (files : List (File partitions Value)) :
    Events.Trace projection.schema Value (FileError (Int32ByteArray.Error Failure)) :=
  scanInt32ByteArraySnapshotsBounded limits lookup projection keep budget
    (files.filter fun file => (keep file.cells).getD false)

/-- The charged cost of the retained manifest through EOS or its first failure. -/
abbrev Int32ByteArrayPrunedScanCost (limits : Int32ByteArrayGroup.File.Limits) (int32 byteArray : Field)
    (lookup : String → Except Failure Bytes) (keep : Scan.Predicate partitions.toScan Value)
    (files : List (File partitions Value)) (actions : Nat) : Prop :=
  Int32ByteArrayScanCost limits int32 byteArray lookup (files.filter fun file => (keep file.cells).getD false) actions

end Silmaril.Formats.Hive.Manifest
