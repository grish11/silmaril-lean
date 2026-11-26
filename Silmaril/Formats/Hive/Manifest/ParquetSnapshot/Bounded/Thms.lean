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

end Silmaril.Formats.Hive.Manifest
