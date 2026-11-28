module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs
public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Pruning.Defs

/-! Checked ingress followed by a separately budgeted paired Hive scan. -/

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest.Int32ByteArray.Ingress

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open TypedPartitions (PartitionSchema)

inductive OpenPolicy where
  | strict
  | skipRejected
  deriving Repr

variable {Failure : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}

/-- Admit every declaration before choosing which files to open. An ingress
error leaves no trace. A successful admission yields the original bounded
trace, including lookup, Parquet, or close outcomes. The action budget
applies only to the traversal after admission. -/
def scanPaths (policy : OpenPolicy) (options : PartitionPath.Options)
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) (paths : List String) :
    Except Error (Events.Trace projection.schema Value (FileError (Int32ByteArray.Error Failure))) :=
  (preparePaths int32 byteArray partitions options paths).map fun files =>
    match policy with
    | .strict => scanInt32ByteArraySnapshotsBounded limits lookup projection keep budget files
    | .skipRejected =>
      scanInt32ByteArraySnapshotsBoundedSkippingRejected limits lookup projection keep budget files

end Silmaril.Formats.Hive.Manifest.Int32ByteArray.Ingress
