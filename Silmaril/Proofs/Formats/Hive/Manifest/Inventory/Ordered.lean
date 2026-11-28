module

public import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Defs

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.Inventory

open Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.Manifest.Inventory (orderFiles)
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)

variable {Kind : Type*} {Value : Kind → Type*} {schema : PartitionSchema Kind}

theorem orderFiles_paths_eq_of_perm {left right : List (File schema Value)}
    (same : (left.map (·.path.declared)).Perm (right.map (·.path.declared))) :
    (orderFiles left).map (·.path.declared) = (orderFiles right).map (·.path.declared) := by
  have sorted (files : List (File schema Value)) :
      ((orderFiles files).map (·.path.declared)).Pairwise (· ≤ ·) := by
    have ordered : (orderFiles files).Pairwise (fun a b => decide (a.path.declared ≤ b.path.declared)) :=
      List.pairwise_mergeSort (le := fun a b => decide (a.path.declared ≤ b.path.declared))
        (fun _ _ _ ab bc => decide_eq_true (Std.le_trans (of_decide_eq_true ab) (of_decide_eq_true bc)))
        (fun _ _ => by
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact Std.le_total) files
    exact List.pairwise_map.mpr (ordered.imp fun h => of_decide_eq_true h)
  have filePerm (files : List (File schema Value)) : (orderFiles files).Perm files := List.mergeSort_perm _ _
  have keyPerm := ((filePerm left).map (·.path.declared)).trans
    (same.trans ((filePerm right).map (·.path.declared)).symm)
  exact keyPerm.eq_of_pairwise (fun _ _ _ _ => Std.le_antisymm) (sorted left) (sorted right)

end Silmaril.Proofs.Formats.Hive.Manifest.Inventory
