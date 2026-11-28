module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Defs
public import Silmaril.Formats.Hive.Manifest.Pruning.Defs

/-! Logical scan observations across immutable Parquet snapshots. -/

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema partitionCells)

variable {Kind Failure : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

/-- The reference opens files in manifest order and keeps each available row
through the first terminal failure. It filters and projects afterward. -/
def scanSnapshotsThenFilter (limits : Parquet.Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Parquet.Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (files : List (File schema Value)) :
    Events.Trace projection.schema Value (FileError (Parquet.Snapshot.Error Failure)) :=
  let full := scan (snapshotOpener limits lookup bind) (Scan.Projection.id (schema.extend physical))
    (fun _ => some true) files
  full.scan projection (fun row => predicate (partitionCells row))

/-- Independent full-read evidence for a declared snapshot. This includes
successful lookup and open, and successful exhaustion of all row groups. -/
def SnapshotReachesEOF (limits : Parquet.Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Parquet.Snapshot.Bind physical Value Failure)
    (path : String) : Prop :=
  ∃ bytes, lookup path = .ok bytes ∧
    ((Parquet.Snapshot.readAll limits bind bytes).collect.map Events.Observation.termination) = .ok .eos

end Silmaril.Formats.Hive.Manifest
