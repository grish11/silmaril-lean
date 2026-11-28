module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Scan.Defs
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.Int32ByteArray.Ingress

open Silmaril.Formats Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.Manifest.Int32ByteArray.Ingress
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Failure : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}
variable {options : Silmaril.Formats.Hive.PartitionPath.Options} {limits : Int32ByteArrayGroup.File.Limits}
variable {lookup : String → Except Failure Bytes}
variable {projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray))}
variable {keep : Scan.Predicate partitions.toScan Value} {budget : Nat} {paths : List String}

theorem scanPaths_ok_iff (policy : OpenPolicy)
    (trace : Events.Trace projection.schema Value (FileError (Int32ByteArray.Error Failure))) :
    scanPaths policy options limits lookup projection keep budget paths = .ok trace ↔
      ∃ files, preparePaths int32 byteArray partitions options paths = .ok files ∧
        files.map (fun file => file.path.declared) = paths ∧
        trace = scanInt32ByteArraySnapshotsBounded limits lookup projection keep budget
          (match policy with
          | .strict => files
          | .skipRejected => files.filter fun file => (keep file.cells).getD false) := by
  cases admitted : preparePaths int32 byteArray partitions options paths with
  | error error => simp [scanPaths, Except.map, admitted]
  | ok files =>
    have paths_eq := preparePaths_preserves_paths int32 byteArray admitted
    cases policy <;>
      simp [scanPaths, Except.map, admitted, paths_eq, scanInt32ByteArraySnapshotsBoundedSkippingRejected, eq_comm]

end Silmaril.Proofs.Formats.Hive.Manifest.Int32ByteArray.Ingress
