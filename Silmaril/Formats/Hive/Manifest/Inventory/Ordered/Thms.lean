module

public import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Defs
import Silmaril.Formats.Hive.Manifest.Inventory.Thms
import Silmaril.Proofs.Formats.Hive.Manifest.Inventory.Ordered

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational
open TypedPartitions (PartitionSchema Convert)

variable {Kind : Type*} {Value : Kind → Type*} {Failure : Type*}
variable {schema : PartitionSchema Kind}

namespace Inventory

/-- Ordering preserves the complete typed occurrences, including multiplicities. -/
theorem orderFiles_perm (files : List (File schema Value)) : (orderFiles files).Perm files :=
  List.mergeSort_perm _ _

/-- Sorting typed files is compatible with taking their literal lookup keys. -/
theorem orderFiles_paths (files : List (File schema Value)) :
    (orderFiles files).map (·.path.declared) =
      (files.map (·.path.declared)).mergeSort fun a b => decide (a ≤ b) :=
  List.map_mergeSort (fun _ _ _ _ => rfl)

/-- The ordered lookup list is determined by the multiset of literal keys. -/
theorem orderFiles_paths_eq_of_perm {left right : List (File schema Value)}
    (same : (left.map (·.path.declared)).Perm (right.map (·.path.declared))) :
    (orderFiles left).map (·.path.declared) = (orderFiles right).map (·.path.declared) :=
  Proofs.Formats.Hive.Manifest.Inventory.orderFiles_paths_eq_of_perm same

end Inventory

theorem prepareOrderedInventoryWith_eq_reference (physical : Scan.Schema String Kind)
    (schema : PartitionSchema Kind) (limits : Inventory.Limits) (parse : DirectoryParser)
    (options : PartitionPath.Options) (convert : Convert Value Failure) (listing : List String) :
    prepareOrderedInventoryWith physical schema limits parse options convert listing =
      (prepareInventoryReferenceWith physical schema limits parse options convert listing).map Inventory.orderFiles := by
  rw [prepareOrderedInventoryWith, prepareInventoryWith_eq_reference]

/-- Keep the indexed admission reference's outcome and order only its successful file list. -/
theorem prepareOrderedInventory_eq_reference (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (listing : List String) :
    prepareOrderedInventory physical schema limits options convert listing =
      (prepareInventoryReference physical schema limits options convert listing).map Inventory.orderFiles := by
  exact prepareOrderedInventoryWith_eq_reference physical schema limits PartitionPath.parse options convert listing

/-- Admission failures keep the same typed cause and original listing index. -/
theorem prepareOrderedInventory_error_iff (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (listing : List String) (reason : Inventory.Error Failure) :
    prepareOrderedInventory physical schema limits options convert listing = .error reason ↔
      prepareInventory physical schema limits options convert listing = .error reason := by
  change ((prepareInventory physical schema limits options convert listing).map Inventory.orderFiles = .error reason) ↔
    prepareInventory physical schema limits options convert listing = .error reason
  cases prepareInventory physical schema limits options convert listing <;> simp [Except.map]

end Silmaril.Formats.Hive.Manifest
