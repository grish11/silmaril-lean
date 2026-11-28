module

public import Silmaril.Formats.Hive.TypedPartitions.Defs
import Silmaril.Proofs.Formats.Hive.TypedPartitions.Correctness

public section

namespace Silmaril.Formats.Hive.TypedPartitions

open Silmaril.Relational

variable {Kind : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

@[simp] theorem physicalCells_extendRow (row : Scan.Row physical Value)
    (cells : Scan.Row schema.toScan Value) :
    physicalCells (extendRow row cells) = row :=
  Proofs.Formats.Hive.TypedPartitions.physicalCells_extendRow row cells

@[simp] theorem partitionCells_extendRow (row : Scan.Row physical Value)
    (cells : Scan.Row schema.toScan Value) :
    partitionCells (extendRow row cells) = cells :=
  Proofs.Formats.Hive.TypedPartitions.partitionCells_extendRow row cells

/-- Successful validation and conversion preserve the physical table of
every manifest entry, in manifest order. -/
theorem prepare_preserves_rows {Failure : Type*} (convert : Convert Value Failure)
    {manifest : List (InputPartition physical Value)}
    {typed : List (TypedPartition physical schema Value)}
    (h : prepare schema convert manifest = .ok typed) :
    typed.map TypedPartition.rows = manifest.map InputPartition.rows :=
  Proofs.Formats.Hive.TypedPartitions.prepare_preserves_rows convert h

/-- Recover the original rows in manifest order and in each partition's row order. -/
theorem materialize_preserves_order (manifest : List (TypedPartition physical schema Value)) :
    (materialize manifest).map physicalCells = manifest.flatMap TypedPartition.rows :=
  Proofs.Formats.Hive.TypedPartitions.materialize_preserves_order manifest

/-- Materialization yields one augmented row for each physical row. -/
theorem materialize_rowCount (manifest : List (TypedPartition physical schema Value)) :
    (materialize manifest).length = (manifest.map fun partition => partition.rows.length).sum :=
  Proofs.Formats.Hive.TypedPartitions.materialize_rowCount manifest

/-- The partition-level predicate yields the same ordered logical scan as
testing every augmented row. The manifest already supplies the physical rows. -/
theorem scanPartitions_eq_scan (projection : Scan.Projection (schema.extend physical))
    (predicate : Scan.Predicate schema.toScan Value)
    (manifest : List (TypedPartition physical schema Value)) :
    scanPartitions projection predicate manifest =
      projection.scan (fun row => predicate (partitionCells row)) (materialize manifest) :=
  Proofs.Formats.Hive.TypedPartitions.scanPartitions_eq_scan projection predicate manifest

end Silmaril.Formats.Hive.TypedPartitions
