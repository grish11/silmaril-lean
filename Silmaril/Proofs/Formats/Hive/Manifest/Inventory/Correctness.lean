module

public import Silmaril.Formats.Hive.Manifest.Inventory.Defs
import Silmaril.Formats.Hive.Manifest.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.Inventory

open Silmaril.Relational Silmaril.Formats.Hive
open Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema Convert)

variable {Kind : Type*} {Value : Kind → Type*} {Failure : Type*}
variable {schema : PartitionSchema Kind}

private theorem walk_eq_reference (parse : FileParser) (maxPathBytes : Nat) (options : PartitionPath.Options)
    (convert : Convert Value Failure) (remaining index : Nat) (paths : List String)
    (files : List (File schema Value)) :
    Manifest.Inventory.walkWithFileParser parse maxPathBytes options convert remaining index paths files =
      (Manifest.Inventory.referenceFromWithFileParser parse maxPathBytes options convert remaining index paths).map
        (fun selected => files.reverse ++ selected) := by
  induction paths generalizing remaining index files with
  | nil =>
    simp [Manifest.Inventory.walkWithFileParser, Manifest.Inventory.referenceFromWithFileParser, pure, bind, Except.pure, Except.bind,
      Except.map]
  | cons path paths ih =>
    cases remaining with
    | zero => rfl
    | succ remaining =>
      rw [Manifest.Inventory.walkWithFileParser]
      simp only [Manifest.Inventory.referenceFromWithFileParser, List.take_succ_cons, List.zipIdx_cons, List.mapM_cons,
        List.drop_succ_cons]
      generalize Manifest.Inventory.checkEntryWithFileParser (schema := schema) parse maxPathBytes options convert index path =
        head
      cases head with
      | error reason => rfl
      | ok head =>
        rw [show index + remaining.succ = index + 1 + remaining by omega]
        simp only [bind, Except.bind, pure, Except.pure]
        cases head <;> rw [ih] <;>
          simp only [Manifest.Inventory.referenceFromWithFileParser, bind, Except.bind, pure, Except.pure] <;>
          split
        all_goals first
          | rfl
          | split <;> first | rfl | simp [Except.map, List.reverse_cons, List.append_assoc]

theorem prepareInventoryWithFileParser_eq_reference (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Manifest.Inventory.Limits) (parse : FileParser) (options : PartitionPath.Options) (convert : Convert Value Failure)
    (paths : List String) :
    prepareInventoryWithFileParser physical schema limits parse options convert paths =
      prepareInventoryReferenceWithFileParser physical schema limits parse options convert paths := by
  unfold prepareInventoryWithFileParser prepareInventoryReferenceWithFileParser
  split
  · rfl
  · rw [walk_eq_reference]
    cases Manifest.Inventory.referenceFromWithFileParser (schema := schema) parse limits.maxPathBytes options convert
      limits.maxEntries 0 paths <;> rfl

private theorem checkEntryWithFileParser_path (parse : FileParser) (limit : Nat)
    (options : PartitionPath.Options) (convert : Convert Value Failure)
    (index : Nat) (path : String) {entry : Option (File schema Value)}
    (checked : Manifest.Inventory.checkEntryWithFileParser parse limit options convert index path = .ok entry) :
    (entry.toList.map (·.path.declared)) = [path].filter Manifest.Inventory.isDataPath := by
  unfold Manifest.Inventory.checkEntryWithFileParser at checked
  split at checked
  · contradiction
  · cases lexical : splitFile path with
    | error reason => simp [lexical] at checked
    | ok parts =>
      obtain ⟨directory, leaf⟩ := parts
      cases control : Manifest.Inventory.isControlLeaf leaf
      · cases prepared : prepareFileWithFileParser schema parse options convert path with
        | error reason => simp [lexical, control, prepared, Except.mapError, Except.map] at checked
        | ok file =>
          simp [lexical, control, prepared, Except.mapError, Except.map] at checked
          subst entry
          simp [Manifest.Inventory.isDataPath, lexical, control,
            prepareFileWithFileParser_declared parse options convert prepared]
      · simp [lexical, control] at checked
        subst entry
        simp [Manifest.Inventory.isDataPath, lexical, control]

private theorem walkWithFileParser_paths (parse : FileParser) (limit : Nat)
    (options : PartitionPath.Options) (convert : Convert Value Failure)
    (remaining index : Nat) (paths : List String) (acc : List (File schema Value))
    {files : List (File schema Value)}
    (admitted : Manifest.Inventory.walkWithFileParser parse limit options convert remaining index paths acc = .ok files) :
    files.map (·.path.declared) = acc.reverse.map (·.path.declared) ++ paths.filter Manifest.Inventory.isDataPath := by
  induction paths generalizing remaining index acc with
  | nil =>
    simp only [Manifest.Inventory.walkWithFileParser, Except.ok.injEq] at admitted
    subst files
    simp
  | cons path rest ih =>
    cases remaining with
    | zero => contradiction
    | succ remaining =>
      rw [Manifest.Inventory.walkWithFileParser] at admitted
      cases checked : Manifest.Inventory.checkEntryWithFileParser (schema := schema) parse limit options convert index path with
      | error reason => simp [checked, bind, Except.bind] at admitted
      | ok entry =>
        have key := checkEntryWithFileParser_path parse limit options convert index path checked
        simp only [checked, bind, Except.bind] at admitted
        have filterCons :
            (path :: rest).filter Manifest.Inventory.isDataPath =
              [path].filter Manifest.Inventory.isDataPath ++ rest.filter Manifest.Inventory.isDataPath :=
          List.filter_append [path] rest
        rw [filterCons, ← key]
        cases entry with
        | none => simpa using ih remaining (index + 1) acc admitted
        | some file =>
          simpa [List.reverse_cons, List.append_assoc] using
            ih remaining (index + 1) (file :: acc) admitted

theorem prepareInventoryWithFileParser_paths (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (limits : Manifest.Inventory.Limits) (parse : FileParser) (options : PartitionPath.Options)
    (convert : Convert Value Failure) {paths : List String} {files : List (File schema Value)}
    (admitted : prepareInventoryWithFileParser physical schema limits parse options convert paths = .ok files) :
    files.map (·.path.declared) = paths.filter Manifest.Inventory.isDataPath := by
  unfold prepareInventoryWithFileParser at admitted
  split at admitted
  · contradiction
  · simpa using walkWithFileParser_paths parse limits.maxPathBytes options convert limits.maxEntries 0 paths [] admitted

end Silmaril.Proofs.Formats.Hive.Manifest.Inventory
