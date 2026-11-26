module

public import Silmaril.Formats.Hive.Manifest.Literal.Defs

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.Literal

open Silmaril.Formats.Hive Silmaril.Formats.Hive.Manifest
open TypedPartitions (PartitionSchema Convert)

theorem prepareFile_path {Kind : Type*} {Value : Kind → Type*} {Failure : Type*}
    (schema : PartitionSchema Kind) (maxPathBytes : Nat) (options : PartitionPath.Options)
    (convert : Convert Value Failure) {declared : String} {file : File schema Value}
    (prepared : Silmaril.Formats.Hive.Manifest.Literal.prepareFile schema maxPathBytes options convert declared = .ok file) :
    file.path.declared = declared ∧ declared.utf8ByteSize ≤ maxPathBytes := by
  unfold Silmaril.Formats.Hive.Manifest.Literal.prepareFile at prepared
  split at prepared
  · contradiction
  · rename_i fits
    have bound : declared.utf8ByteSize ≤ maxPathBytes := Nat.le_of_not_gt fits
    cases split : splitFile declared with
    | error reason => simp [split, Except.mapError, Except.bind] at prepared
    | ok parts =>
      obtain ⟨directory, leaf⟩ := parts
      cases parsed : Silmaril.Formats.Hive.Manifest.Literal.parse options directory with
      | error reason => simp [split, parsed, Except.mapError, Except.bind] at prepared
      | ok entries =>
        cases rendered : PartitionPath.render options entries with
        | error reason => simp [split, parsed, rendered, Except.mapError, Except.bind] at prepared
        | ok canonical =>
          cases boundCells : TypedPartitions.decode schema convert entries with
          | error reason => simp [split, parsed, rendered, boundCells, Except.mapError, Except.bind, Except.map] at prepared
          | ok cells =>
            simp [split, parsed, rendered, boundCells, Except.mapError, Except.bind, Except.map]
              at prepared
            subst file
            exact ⟨rfl, bound⟩

end Silmaril.Proofs.Formats.Hive.Manifest.Literal
