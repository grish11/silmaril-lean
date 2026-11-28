module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Scan.Defs
import Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.IngressScan

public section

namespace Silmaril.Formats.Hive.Manifest.Int32ByteArray.Ingress

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open TypedPartitions (PartitionSchema)

variable {Failure : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}
variable {options : PartitionPath.Options} {limits : Int32ByteArrayGroup.File.Limits}
variable {lookup : String → Except Failure Bytes}
variable {projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray))}
variable {keep : Scan.Predicate partitions.toScan Value} {budget : Nat} {paths : List String}

/-- Ingress errors are independent of the predicate, lookup, and budget,
including for declarations whose partition would otherwise be rejected. -/
theorem scanPaths_error_iff (policy : OpenPolicy) (error : Error) :
    scanPaths policy options limits lookup projection keep budget paths = .error error ↔
      preparePaths int32 byteArray partitions options paths = .error error := by
  cases admitted : preparePaths int32 byteArray partitions options paths <;> simp [scanPaths, Except.map, admitted]

/-- The scan uses the exact admitted occurrence list, with a stable predicate
filter only in skip-open mode. Both modes use the original action budget. -/
theorem scanPaths_ok_iff (policy : OpenPolicy)
    (trace : Events.Trace projection.schema Value (FileError (Int32ByteArray.Error Failure))) :
    scanPaths policy options limits lookup projection keep budget paths = .ok trace ↔
      ∃ files, preparePaths int32 byteArray partitions options paths = .ok files ∧
        files.map (fun file => file.path.declared) = paths ∧
        trace = scanInt32ByteArraySnapshotsBounded limits lookup projection keep budget
          (match policy with
          | .strict => files
          | .skipRejected => files.filter fun file => (keep file.cells).getD false) :=
  Proofs.Formats.Hive.Manifest.Int32ByteArray.Ingress.scanPaths_ok_iff policy trace

end Silmaril.Formats.Hive.Manifest.Int32ByteArray.Ingress
