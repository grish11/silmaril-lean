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
theorem prepareInventoryWithFileParser_eq_reference (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (parse : FileParser) (options : PartitionPath.Options)
    (convert : Convert Value Failure) (paths : List String) :
    prepareInventoryWithFileParser physical schema limits parse options convert paths =
      prepareInventoryReferenceWithFileParser physical schema limits parse options convert paths :=
  Proofs.Formats.Hive.Manifest.Inventory.prepareInventoryWithFileParser_eq_reference physical schema limits parse options convert paths

/-- Successful admission preserves the exact data paths and their original
occurrence order, including duplicates. -/
theorem prepareInventoryWithFileParser_paths (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (parse : FileParser) (options : PartitionPath.Options)
    (convert : Convert Value Failure) {paths : List String} {files : List (File schema Value)}
    (admitted : prepareInventoryWithFileParser physical schema limits parse options convert paths = .ok files) :
    files.map (·.path.declared) = paths.filter Inventory.isDataPath :=
  Proofs.Formats.Hive.Manifest.Inventory.prepareInventoryWithFileParser_paths physical schema limits parse options convert admitted

theorem prepareInventoryWith_eq_reference (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (parse : DirectoryParser) (options : PartitionPath.Options)
    (convert : Convert Value Failure) (paths : List String) :
    prepareInventoryWith physical schema limits parse options convert paths =
      prepareInventoryReferenceWith physical schema limits parse options convert paths :=
  prepareInventoryWithFileParser_eq_reference physical schema limits parse.asFileParser options convert paths

theorem prepareInventoryWith_paths (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (parse : DirectoryParser) (options : PartitionPath.Options)
    (convert : Convert Value Failure) {paths : List String} {files : List (File schema Value)}
    (admitted : prepareInventoryWith physical schema limits parse options convert paths = .ok files) :
    files.map (·.path.declared) = paths.filter Inventory.isDataPath :=
  prepareInventoryWithFileParser_paths physical schema limits parse.asFileParser options convert admitted

/-- The original URI entry uses only the checked parent directory. -/
theorem prepareInventory_eq_uri_fileParser (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (listing : List String) :
    prepareInventory physical schema limits options convert listing =
      prepareInventoryWithFileParser physical schema limits
        (fun opts directory _ => PartitionPath.parse opts directory) options convert listing := rfl

/-- A lexically valid and affordable control bypasses the selected parser. -/
theorem checkEntryWithFileParser_control {schema : PartitionSchema Kind} (parse : FileParser)
    (limit index : Nat) (options : PartitionPath.Options) (convert : Convert Value Failure)
    {path directory leaf : String} (fits : path.utf8ByteSize ≤ limit)
    (split : splitFile path = .ok (directory, leaf)) (control : Inventory.isControlLeaf leaf = true) :
    Inventory.checkEntryWithFileParser (schema := schema) parse limit options convert index path = .ok none := by
  simp [Inventory.checkEntryWithFileParser, Nat.not_lt.mpr fits, split, control]

/-- Bounded admission returns exactly the reference traversal's typed file list
or first error, including the original occurrence index. -/
theorem prepareInventory_eq_reference (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (paths : List String) :
    prepareInventory physical schema limits options convert paths =
      prepareInventoryReference physical schema limits options convert paths :=
  prepareInventoryWith_eq_reference physical schema limits PartitionPath.parse options convert paths

end Silmaril.Formats.Hive.Manifest
