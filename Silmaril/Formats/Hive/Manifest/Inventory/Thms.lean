module

public import Silmaril.Formats.Hive.Manifest.Inventory.Defs
import Silmaril.Proofs.Formats.Hive.Manifest.Inventory.Correctness

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema Convert)

variable {Kind : Type*} {Value : Kind → Type*} {Failure : Type*}

/-- Bounded admission returns exactly the reference traversal's typed file list
or first error, including the original occurrence index. -/
theorem prepareInventory_eq_reference (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (paths : List String) :
    prepareInventory physical schema limits options convert paths =
      prepareInventoryReference physical schema limits options convert paths :=
  Proofs.Formats.Hive.Manifest.Inventory.prepareInventory_eq_reference physical schema limits options convert paths

end Silmaril.Formats.Hive.Manifest
