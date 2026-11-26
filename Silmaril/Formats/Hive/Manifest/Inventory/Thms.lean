module

public import Silmaril.Formats.Hive.Manifest.Inventory.Defs
import Silmaril.Proofs.Formats.Hive.Manifest.Inventory.Correctness

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema Convert)

variable {Kind : Type*} {Value : Kind → Type*} {Failure : Type*}

/-- The shared walker agrees with the original-index reference for each
directory profile, including the first failure and its exact type. -/
theorem prepareInventoryWith_eq_reference (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (parse : DirectoryParser) (options : PartitionPath.Options)
    (convert : Convert Value Failure) (paths : List String) :
    prepareInventoryWith physical schema limits parse options convert paths =
      prepareInventoryReferenceWith physical schema limits parse options convert paths :=
  Proofs.Formats.Hive.Manifest.Inventory.prepareInventoryWith_eq_reference physical schema limits parse options convert paths

/-- Successful admission preserves the exact data paths and their original
occurrence order, including duplicates. -/
theorem prepareInventoryWith_paths (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (parse : DirectoryParser) (options : PartitionPath.Options)
    (convert : Convert Value Failure) {paths : List String} {files : List (File schema Value)}
    (admitted : prepareInventoryWith physical schema limits parse options convert paths = .ok files) :
    files.map (·.path.declared) = paths.filter Inventory.isDataPath :=
  Proofs.Formats.Hive.Manifest.Inventory.prepareInventoryWith_paths physical schema limits parse options convert admitted

/-- Bounded admission returns exactly the reference traversal's typed file list
or first error, including the original occurrence index. -/
theorem prepareInventory_eq_reference (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (paths : List String) :
    prepareInventory physical schema limits options convert paths =
      prepareInventoryReference physical schema limits options convert paths :=
  prepareInventoryWith_eq_reference physical schema limits PartitionPath.parse options convert paths

end Silmaril.Formats.Hive.Manifest
