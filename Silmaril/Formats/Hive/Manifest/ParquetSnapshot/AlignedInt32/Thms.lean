module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.AlignedInt32.Defs
import Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.AlignedInt32

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.Manifest.AlignedInt32
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema partitionCells)

variable {Failure : Type} {target : Scan.Schema String Unit} {partitions : PartitionSchema Unit}

/-- Each checked group keeps its row count, order and exact read failure. -/
theorem AlignedInt32.readGroup_alignDecode (wire : WireBinding Failure) (snapshot : Snapshot.Checked)
    (index : Nat) :
    snapshot.readGroup (alignDecode target wire) index =
      (snapshot.readGroup wire.decode index).map (List.map (referenceRow target wire.names)) :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.readGroup_alignDecode wire snapshot index

/-- Full consumption emits one aligned batch for each completed wire group,
including empty ones, then reports the wire outcome. -/
theorem AlignedInt32.readAll_alignDecode (wire : WireBinding Failure) (snapshot : Snapshot.Checked) :
    snapshot.readAll (alignDecode target wire) =
      let wireGroups := Reader.denoteGroups (snapshot.readGroup wire.decode) (List.range snapshot.groupCount)
      .ok ⟨target, ⟨wireGroups.1.map (fun rows => AlignedColumns.ofRows
        (rows.map (referenceRow target wire.names))), wireGroups.2⟩⟩ :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.readAll_alignDecode wire snapshot

/-- Collection agrees with the ordered wire-row reference fold, including
the first typed error and all selected rows from preceding batches. -/
theorem scanAlignedInt32Snapshots_collect_eq_rows (limits : Snapshot.FlatInt32.Limits)
    (lookup : String → Except Failure Bytes) (allowMissing : AllowMissing target)
    (projection : Scan.Projection (partitions.extend target))
    (predicate : Scan.Predicate partitions.toScan Cell) (files : List (File partitions Cell)) :
    (scan (alignedInt32SnapshotOpener limits partitions allowMissing lookup) projection predicate files).collect =
      let observed := denoteRows limits lookup allowMissing files
      ⟨⟨projection.schema, projection.scan (fun row => predicate (partitionCells row)) observed.1⟩,
        observed.2⟩ :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.scanAlignedInt32Snapshots_collect_eq_rows limits lookup
    allowMissing projection predicate files

end Silmaril.Formats.Hive.Manifest
