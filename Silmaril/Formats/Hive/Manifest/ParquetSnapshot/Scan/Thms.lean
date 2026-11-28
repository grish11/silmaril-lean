module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Scan.Defs
import Silmaril.Formats.Hive.Manifest.Pruning.Thms
import Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Scan.Correctness

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)
open Silmaril.Formats.Parquet

variable {Kind Failure : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

/-- The strict snapshot scan agrees with filtering and projecting the full
ordered Arrow observation, including its successful prefix after failure. -/
theorem scanSnapshots_equivalent_thenFilter (limits : Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (files : List (File schema Value)) :
    Events.EventStream.Equivalent
      (.ok ⟨projection.schema, scan (snapshotOpener limits lookup bind) projection predicate files⟩)
      (.ok ⟨projection.schema, scanSnapshotsThenFilter limits lookup bind projection predicate files⟩) :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.scanSnapshots_equivalent_thenFilter
    limits lookup bind projection predicate files

/-- Successful standalone full consumption implies that the manifest file
adapter will reach EOF with the same snapshot and binder. -/
theorem scanFile_eof_of_snapshot (limits : Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (file : File schema Value) (clean : SnapshotReachesEOF limits lookup bind file.path.declared) :
    (scanFile (snapshotOpener limits lookup bind) projection predicate file).termination = .eos :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.scanFile_eof_of_snapshot limits lookup bind
    projection predicate file clean

/-- Skip-open pruning agrees with the full-open reference when standalone
reads of rejected files would reach EOF. Retained files may still fail. -/
theorem scanSnapshotsSkippingRejected_equivalent_thenFilter (limits : Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (files : List (File schema Value))
    (clean : ∀ file ∈ files, (predicate file.cells).getD false = false →
      SnapshotReachesEOF limits lookup bind file.path.declared) :
    Events.EventStream.Equivalent
      (.ok ⟨projection.schema, scanSkippingRejected (snapshotOpener limits lookup bind) projection predicate files⟩)
      (.ok ⟨projection.schema, scanSnapshotsThenFilter limits lookup bind projection predicate files⟩) :=
  (scanSkippingRejected_equivalent _ projection predicate files (fun file member reject =>
      scanFile_eof_of_snapshot limits lookup bind projection predicate file (clean file member reject))).trans
    (scanSnapshots_equivalent_thenFilter limits lookup bind projection predicate files)

end Silmaril.Formats.Hive.Manifest
