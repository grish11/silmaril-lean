module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Bounded.Defs
import Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Bounded

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)

variable {Kind Failure : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

variable {Group ReadError : Type*}

/-- Full-consumption openers admit a cost witness for every finite manifest. -/
theorem scanCost_exists (opener : Opener Group physical Value ReadError)
    (admitted : opener.FullConsumption) (files : List (File schema Value)) :
    ∃ actions, ScanCost opener files actions :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.scanCost_exists opener admitted files

/-- A budget covering the witnessed actions recovers exactly the strict trace. -/
theorem scanBounded_eq_scan_of_cost (opener : Opener Group physical Value ReadError)
    (admitted : opener.FullConsumption)
    (projection : Scan.Projection (schema.extend physical)) (keep : Scan.Predicate schema.toScan Value)
    {budget actions : Nat} {files : List (File schema Value)}
    (cost : ScanCost opener files actions) (enough : actions ≤ budget) :
    scanBounded opener projection keep budget files = scan opener projection keep files :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.scanBounded_eq_scan_of_cost
    opener admitted projection keep cost enough

/-- The bounded trace closes exactly below the witnessed cost. Its aligned
batches form an ordered prefix of the strict trace at every budget. -/
theorem scanBounded_exact_boundary (opener : Opener Group physical Value ReadError)
    (admitted : opener.FullConsumption)
    (projection : Scan.Projection (schema.extend physical)) (keep : Scan.Predicate schema.toScan Value)
    {budget actions : Nat} {files : List (File schema Value)}
    (cost : ScanCost opener files actions) :
    let bounded := scanBounded opener projection keep budget files
    let strict := scan opener projection keep files
    (bounded.termination = .closed ↔ budget < actions) ∧ List.IsPrefix bounded.batches strict.batches :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.scanBounded_exact_boundary opener admitted projection keep cost

/-- Appending occurrences after a stopped trace cannot affect that trace. -/
theorem scanBounded_append_of_stopped (opener : Opener Group physical Value ReadError)
    (projection : Scan.Projection (schema.extend physical)) (keep : Scan.Predicate schema.toScan Value)
    (budget : Nat) (files suffix : List (File schema Value))
    (stopped : (scanBounded opener projection keep budget files).termination ≠ .eos) :
    scanBounded opener projection keep budget (files ++ suffix) = scanBounded opener projection keep budget files :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.scanBounded_append_of_stopped
    opener projection keep budget files suffix stopped

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

/-- An immutable snapshot scan closes exactly below the witnessed action
cost. Its emitted aligned batches are always a prefix of the strict trace,
including explicit batch counts at zero projected width. -/
theorem scanSnapshotsBounded_exact_boundary (limits : Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (keep : Scan.Predicate schema.toScan Value)
    {budget actions : Nat} {files : List (File schema Value)}
    (cost : SnapshotScanCost limits lookup bind files actions) :
    let bounded := scanSnapshotsBounded limits lookup bind projection keep budget files
    let strict := scan (snapshotOpener limits lookup bind) projection keep files
    (bounded.termination = .closed ↔ budget < actions) ∧ List.IsPrefix bounded.batches strict.batches :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.scanSnapshotsBounded_exact_boundary
    limits lookup bind projection keep cost

/-- A trace stopped before manifest EOS is unchanged by appending later
literal occurrences. This is exact equality of pure snapshot traces. -/
theorem scanSnapshotsBounded_append_of_stopped (limits : Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (keep : Scan.Predicate schema.toScan Value)
    (budget : Nat) (files suffix : List (File schema Value))
    (stopped : (scanSnapshotsBounded limits lookup bind projection keep budget files).termination ≠ .eos) :
    scanSnapshotsBounded limits lookup bind projection keep budget (files ++ suffix) =
      scanSnapshotsBounded limits lookup bind projection keep budget files :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.scanSnapshotsBounded_append_of_stopped
    limits lookup bind projection keep budget files suffix stopped

end Silmaril.Formats.Hive.Manifest
