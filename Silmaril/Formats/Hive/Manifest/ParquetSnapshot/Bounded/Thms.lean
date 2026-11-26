module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Bounded.Defs
import Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Bounded

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)

variable {Kind Failure : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

/-- Exact trace equality with the budgeted group-prefix denotation. It
includes ordered selected batches and their counts, and the first reached
failure with its literal path and original typed payload. -/
theorem scanSnapshotsBounded_eq_reference (limits : Snapshot.Limits) (lookup : String → Except Failure Bytes)
    (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (keep : Scan.Predicate schema.toScan Value)
    (budget : Nat) (files : List (File schema Value)) :
    scanSnapshotsBounded limits lookup bind projection keep budget files =
      scanSnapshotsBoundedReference limits lookup bind projection keep budget files :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.scanSnapshotsBounded_eq_reference
    limits lookup bind projection keep budget files

/-- With enough actions to reach manifest EOS or the first failed action,
the bounded scan returns exactly the strict full trace. -/
theorem scanSnapshotsBounded_eq_scan_of_cost (limits : Snapshot.Limits) (lookup : String → Except Failure Bytes)
    (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (keep : Scan.Predicate schema.toScan Value)
    {budget actions : Nat} {files : List (File schema Value)}
    (cost : SnapshotScanCost limits lookup bind files actions) (enough : actions ≤ budget) :
    scanSnapshotsBounded limits lookup bind projection keep budget files =
      scan (snapshotOpener limits lookup bind) projection keep files :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.scanSnapshotsBounded_eq_scan_of_cost
    limits lookup bind projection keep cost enough

/-- Every finite strict snapshot scan has a cost witness, including scans
that reach checked-open or row-group failures. -/
theorem snapshotScanCost_exists (limits : Snapshot.Limits) (lookup : String → Except Failure Bytes)
    (bind : Snapshot.Bind physical Value Failure) (files : List (File schema Value)) :
    ∃ actions, SnapshotScanCost limits lookup bind files actions :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.snapshotScanCost_exists limits lookup bind files

end Silmaril.Formats.Hive.Manifest
