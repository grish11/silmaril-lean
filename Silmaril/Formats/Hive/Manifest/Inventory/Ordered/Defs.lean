module

public import Silmaril.Formats.Hive.Manifest.Inventory.Defs

/-! Order a caller-supplied listing after ordinary bounded admission. -/

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational
open TypedPartitions (PartitionSchema Convert)

variable {Kind : Type*} {Value : Kind → Type*} {Failure : Type*}
variable {schema : PartitionSchema Kind}

namespace Inventory

/-- Stable ascending string order of the complete literal lookup keys.
Equal keys keep every occurrence. The directory and cells travel with the file. -/
def orderFiles (files : List (File schema Value)) : List (File schema Value) :=
  files.mergeSort fun a b => decide (a.path.declared ≤ b.path.declared)

end Inventory

/-- Admit with the chosen directory profile and order successful data files. -/
def prepareOrderedInventoryWith (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (parse : DirectoryParser) (options : PartitionPath.Options)
    (convert : Convert Value Failure) (listing : List String) :
    Except (Inventory.Error Failure) (List (File schema Value)) :=
  (prepareInventoryWith physical schema limits parse options convert listing).map Inventory.orderFiles

/-- Admit a supplied listing using its original order and limits, then order
the admitted data files by their literal lookup keys. -/
def prepareOrderedInventory (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (listing : List String) : Except (Inventory.Error Failure) (List (File schema Value)) :=
  prepareOrderedInventoryWith physical schema limits PartitionPath.parse options convert listing

end Silmaril.Formats.Hive.Manifest
