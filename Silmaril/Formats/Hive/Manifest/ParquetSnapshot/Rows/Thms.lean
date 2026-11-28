module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Rows.Defs
import Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Rows

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema partitionCells)

variable {Kind Failure : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

/-- The checked manifest scan observes the independently denoted ordered file
rows with typed partition cells, filtered and projected in row order. The
first terminal outcome retains its path, stage, and exact payload. -/
theorem scanSnapshots_collect_eq_rows (limits : Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (files : List (File schema Value)) :
    (scan (snapshotOpener limits lookup bind) projection predicate files).collect =
      let observed := denoteSnapshotRows limits lookup bind files
      ⟨⟨projection.schema, projection.scan (fun row => predicate (partitionCells row)) observed.1⟩,
        observed.2⟩ :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.scanSnapshots_collect_eq_rows limits lookup bind projection predicate files

end Silmaril.Formats.Hive.Manifest
