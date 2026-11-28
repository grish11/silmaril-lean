module

public import Silmaril.Formats.Hive.Manifest.Literal.Defs
import Silmaril.Proofs.Formats.Hive.Manifest.Literal

public section

namespace Silmaril.Formats.Hive.Manifest.Literal

open TypedPartitions (PartitionSchema Convert)

theorem value_eq_none_iff (options : PartitionPath.Options) (raw : String) :
    value options raw = none ↔ raw = options.nullMarker := by
  by_cases equal : raw = options.nullMarker <;> simp [value, equal]

/-- A spelling that URI-decodes to the marker is still present text in the
literal profile whenever its raw spelling differs from the marker. -/
theorem value_of_uri_marker_alias {options : PartitionPath.Options} {raw : String}
    (decoded : PartitionPath.Percent.decode raw = .ok options.nullMarker)
    (distinct : raw ≠ options.nullMarker) :
    value options raw = some raw ∧
      (PartitionPath.Percent.decode raw).map (value options) = .ok none := by
  simp [value, distinct, decoded, Except.map]

/-- Bound and bind the original lookup path without rewriting any byte. -/
theorem prepareFile_path {Kind : Type*} {Value : Kind → Type*} {Failure : Type*}
    (schema : PartitionSchema Kind) (maxPathBytes : Nat) (options : PartitionPath.Options)
    (convert : Convert Value Failure) {declared : String} {file : File schema Value}
    (prepared : prepareFile schema maxPathBytes options convert declared = .ok file) :
    file.path.declared = declared ∧ declared.utf8ByteSize ≤ maxPathBytes :=
  Proofs.Formats.Hive.Manifest.Literal.prepareFile_path schema maxPathBytes options convert prepared

end Silmaril.Formats.Hive.Manifest.Literal
