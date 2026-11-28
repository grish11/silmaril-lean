module

public import Silmaril.Formats.Hive.Manifest.Literal.Defs
import Silmaril.Formats.Hive.Manifest.Thms

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
    cases admitted : prepareFileWith schema Silmaril.Formats.Hive.Manifest.Literal.parse options convert declared with
    | error reason => simp [admitted, Except.mapError] at prepared
    | ok result =>
      simp [admitted, Except.mapError] at prepared
      subst file
      exact ⟨prepareFileWith_declared _ options convert admitted, bound⟩

end Silmaril.Proofs.Formats.Hive.Manifest.Literal
