module

public import Silmaril.Formats.Hive.Manifest.Inventory.Defs

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.Inventory

open Silmaril.Relational Silmaril.Formats.Hive
open Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema Convert)

variable {Kind : Type*} {Value : Kind → Type*} {Failure : Type*}
variable {schema : PartitionSchema Kind}

private theorem walk_eq_reference (maxPathBytes : Nat) (options : PartitionPath.Options)
    (convert : Convert Value Failure) (remaining index : Nat) (paths : List String)
    (files : List (File schema Value)) :
    Manifest.Inventory.walk maxPathBytes options convert remaining index paths files =
      (Manifest.Inventory.referenceFrom maxPathBytes options convert remaining index paths).map
        (fun selected => files.reverse ++ selected) := by
  induction paths generalizing remaining index files with
  | nil =>
    simp [Manifest.Inventory.walk, Manifest.Inventory.referenceFrom, pure, bind, Except.pure, Except.bind,
      Except.map]
  | cons path paths ih =>
    cases remaining with
    | zero => rfl
    | succ remaining =>
      rw [Manifest.Inventory.walk]
      simp only [Manifest.Inventory.referenceFrom, List.take_succ_cons, List.zipIdx_cons, List.mapM_cons,
        List.drop_succ_cons]
      generalize Manifest.Inventory.checkEntry (schema := schema) maxPathBytes options convert index path =
        head
      cases head with
      | error reason => rfl
      | ok head =>
        rw [show index + remaining.succ = index + 1 + remaining by omega]
        simp only [bind, Except.bind, pure, Except.pure]
        cases head <;> rw [ih] <;>
          simp only [Manifest.Inventory.referenceFrom, bind, Except.bind, pure, Except.pure] <;>
          split
        all_goals first
          | rfl
          | split <;> first | rfl | simp [Except.map, List.reverse_cons, List.append_assoc]

theorem prepareInventory_eq_reference (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Manifest.Inventory.Limits) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (paths : List String) :
    prepareInventory physical schema limits options convert paths =
      prepareInventoryReference physical schema limits options convert paths := by
  unfold prepareInventory prepareInventoryReference
  split
  · rfl
  · rw [walk_eq_reference]
    cases Manifest.Inventory.referenceFrom (schema := schema) limits.maxPathBytes options convert
      limits.maxEntries 0 paths <;> rfl

end Silmaril.Proofs.Formats.Hive.Manifest.Inventory
