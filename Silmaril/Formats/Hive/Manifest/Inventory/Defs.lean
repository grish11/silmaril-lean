module

public import Silmaril.Formats.Hive.Manifest.Defs

/-!
# Bounded Hive manifest admission

The inventory is supplied in caller order. Every entry is a relative file
declaration. Only the three literal Parquet control leaves are skipped, after
lexical validation of the whole path and before Hive parsing of the parent.
Data declarations use the same typed preparation as the ordinary manifest.
-/

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest.Inventory

open Silmaril.Relational
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema Convert)

variable {Kind : Type*} {Value : Kind → Type*} {Failure : Type*}
variable {schema : PartitionSchema Kind}

/-- Count all occurrences, including controls and repeats. The byte limit is
per occurrence and measures its entire original UTF-8 path. -/
structure Limits where
  maxEntries : Nat
  maxPathBytes : Nat

/-- Indices are zero-based positions in the original inventory. -/
inductive Error (Failure : Type*) where
  | schema (reason : TypedPartitions.Error Failure)
  | entryLimit (index : Nat)
  | pathByteLimit (index : Nat) (actualBytes : Nat)
  | entry (index : Nat) (reason : PrepareError Failure)
  deriving BEq, Repr

/-- Compare the opaque leaf byte spelling without percent decoding or case folding. -/
def isControlLeaf (leaf : String) : Bool :=
  leaf == "_SUCCESS" || leaf == "_metadata" || leaf == "_common_metadata"

/-- Retain lexically valid file paths whose literal leaf is data. On
successful admission all other occurrences are recognized controls. -/
def isDataPath (path : String) : Bool :=
  match splitFile path with
  | .error _ => false
  | .ok (_, leaf) => !isControlLeaf leaf

def checkEntryWith (parse : DirectoryParser) (maxPathBytes : Nat) (options : PartitionPath.Options)
    (convert : Convert Value Failure) (index : Nat) (path : String) :
    Except (Error Failure) (Option (File schema Value)) :=
  if path.utf8ByteSize > maxPathBytes then .error (.pathByteLimit index path.utf8ByteSize)
  else
    match splitFile path with
    | .error reason => .error (.entry index (.relativePath path reason))
    | .ok (_, leaf) =>
      if isControlLeaf leaf then .ok none
      else ((prepareFileWith schema parse options convert path).mapError (Error.entry index)).map some

/-- Walk the inventory once in order, accumulating file occurrences in reverse. -/
def walkWith (parse : DirectoryParser) (maxPathBytes : Nat) (options : PartitionPath.Options) (convert : Convert Value Failure) :
    Nat → Nat → List String → List (File schema Value) → Except (Error Failure) (List (File schema Value))
  | _, _, [], files => .ok files.reverse
  | 0, index, _ :: _, _ => .error (.entryLimit index)
  | remaining + 1, index, path :: paths, files => do
    let selected ← checkEntryWith parse maxPathBytes options convert index path
    let files := match selected with
      | none => files
      | some file => file :: files
    walkWith parse maxPathBytes options convert remaining (index + 1) paths files

/-- Independently traverse the indexed prefix. Check the suffix only after
the entire prefix succeeds. -/
def referenceFromWith (parse : DirectoryParser) (maxPathBytes : Nat) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (remaining index : Nat) (paths : List String) : Except (Error Failure) (List (File schema Value)) := do
  let entries ← ((paths.take remaining).zipIdx index).mapM fun (path, position) =>
    checkEntryWith parse maxPathBytes options convert position path
  match paths.drop remaining with
  | [] => return entries.filterMap id
  | _ :: _ => throw (.entryLimit (index + remaining))


abbrev checkEntry (maxPathBytes : Nat) (options : PartitionPath.Options)
    (convert : Convert Value Failure) (index : Nat) (path : String) :
    Except (Error Failure) (Option (File schema Value)) :=
  checkEntryWith PartitionPath.parse maxPathBytes options convert index path

abbrev walk (maxPathBytes : Nat) (options : PartitionPath.Options) (convert : Convert Value Failure) :
    Nat → Nat → List String → List (File schema Value) → Except (Error Failure) (List (File schema Value)) :=
  walkWith PartitionPath.parse maxPathBytes options convert

abbrev referenceFrom (maxPathBytes : Nat) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (remaining index : Nat) (paths : List String) : Except (Error Failure) (List (File schema Value)) :=
  referenceFromWith PartitionPath.parse maxPathBytes options convert remaining index paths

end Silmaril.Formats.Hive.Manifest.Inventory

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema Convert)

variable {Kind : Type*} {Value : Kind → Type*} {Failure : Type*}

/-- Check the schema first. For each occurrence check remaining entry budget,
path byte size, lexical validity, and then typed preparation if it is data.
Report the first error and return a manifest only on complete success. -/
def prepareInventoryWith (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (parse : DirectoryParser) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (paths : List String) : Except (Inventory.Error Failure) (List (File schema Value)) :=
  match TypedPartitions.checkSchema physical schema with
  | .error reason => .error (.schema reason)
  | .ok () => Inventory.walkWith parse limits.maxPathBytes options convert limits.maxEntries 0 paths []

/-- Reference contract for bounded admission, using a list prefix and suffix. -/
def prepareInventoryReferenceWith (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (parse : DirectoryParser) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (paths : List String) : Except (Inventory.Error Failure) (List (File schema Value)) :=
  match TypedPartitions.checkSchema physical schema with
  | .error reason => .error (.schema reason)
  | .ok () => Inventory.referenceFromWith parse limits.maxPathBytes options convert limits.maxEntries 0 paths

def prepareInventory (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (paths : List String) : Except (Inventory.Error Failure) (List (File schema Value)) :=
  prepareInventoryWith physical schema limits PartitionPath.parse options convert paths

def prepareInventoryReference (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Inventory.Limits) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (paths : List String) : Except (Inventory.Error Failure) (List (File schema Value)) :=
  prepareInventoryReferenceWith physical schema limits PartitionPath.parse options convert paths

end Silmaril.Formats.Hive.Manifest
