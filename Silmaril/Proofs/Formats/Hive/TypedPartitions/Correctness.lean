module

public import Silmaril.Formats.Hive.TypedPartitions.Defs
import Silmaril.Semantics.Relational.Scan.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.TypedPartitions

open Silmaril.Relational Silmaril.Formats.Hive.TypedPartitions

variable {Kind : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

theorem physicalCells_extendRow (row : Scan.Row physical Value)
    (cells : Scan.Row schema.toScan Value) :
    physicalCells (extendRow row cells) = row := by
  funext i
  simp [physicalCells, extendRow]

theorem partitionCells_extendRow (row : Scan.Row physical Value)
    (cells : Scan.Row schema.toScan Value) :
    partitionCells (extendRow row cells) = cells := by
  funext i
  simp [partitionCells, extendRow]

theorem prepare_preserves_rows {Failure : Type*} (convert : Convert Value Failure)
    {manifest : List (InputPartition physical Value)}
    {typed : List (TypedPartition physical schema Value)}
    (h : prepare schema convert manifest = .ok typed) :
    typed.map TypedPartition.rows = manifest.map InputPartition.rows := by
  unfold prepare at h
  split at h
  · contradiction
  · induction manifest generalizing typed with
    | nil =>
      change Except.ok [] = Except.ok typed at h
      cases h
      rfl
    | cons partition rest ih =>
      rw [List.mapM_cons] at h
      cases hd : decode schema convert partition.entries with
      | error reason => simp [hd, bind, Except.bind] at h
      | ok cells =>
        simp only [bind, Except.bind, hd, pure, Except.pure] at h
        split at h
        · contradiction
        · rename_i hm
          cases h
          simp [ih hm]

theorem materialize_preserves_order (manifest : List (TypedPartition physical schema Value)) :
    (materialize manifest).map physicalCells = manifest.flatMap TypedPartition.rows := by
  induction manifest with
  | nil => rfl
  | cons partition rest ih =>
    change (partition.materialize ++ materialize rest).map physicalCells =
      partition.rows ++ rest.flatMap TypedPartition.rows
    simp [TypedPartition.materialize, List.map_map, Function.comp_def, physicalCells_extendRow, ih]

theorem materialize_rowCount (manifest : List (TypedPartition physical schema Value)) :
    (materialize manifest).length = (manifest.map fun partition => partition.rows.length).sum := by
  simp [materialize, List.length_flatMap, TypedPartition.materialize, Function.comp_def]

private theorem scan_partition (projection : Scan.Projection (schema.extend physical))
    (predicate : Scan.Predicate schema.toScan Value)
    (partition : TypedPartition physical schema Value) :
    projection.scan (fun row => predicate (partitionCells row)) partition.materialize =
      if (predicate partition.cells).getD false then projection.project partition.materialize
      else [] := by
  cases keep : (predicate partition.cells).getD false <;>
    simp [Scan.Projection.scan, Scan.Projection.project, Scan.select, TypedPartition.materialize,
      List.filter_map, Function.comp_def, partitionCells_extendRow, keep]

theorem scanPartitions_eq_scan (projection : Scan.Projection (schema.extend physical))
    (predicate : Scan.Predicate schema.toScan Value)
    (manifest : List (TypedPartition physical schema Value)) :
    scanPartitions projection predicate manifest =
      projection.scan (fun row => predicate (partitionCells row)) (materialize manifest) := by
  induction manifest with
  | nil => rfl
  | cons partition rest ih =>
    simp only [scanPartitions, List.flatMap_cons, materialize, Scan.Projection.scan_append,
      scan_partition] at *
    rw [ih]

end Silmaril.Proofs.Formats.Hive.TypedPartitions
