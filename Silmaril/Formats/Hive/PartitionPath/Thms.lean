module

public import Silmaril.Formats.Hive.PartitionPath.Defs
import Silmaril.Proofs.Formats.Hive.PartitionPath.Correctness
import Silmaril.Proofs.Formats.Hive.PartitionPath.Render

public section

namespace Silmaril.Formats.Hive.PartitionPath

namespace Percent

/-- Percent escaping and unescaping preserve all octets. -/
theorem unescape_escape (bytes : List UInt8) : unescape (escape bytes) = .ok bytes :=
  Proofs.Formats.Hive.PartitionPath.Percent.unescape_escape bytes

/-- Escaped components contain only ASCII and no literal directory or key separators. -/
theorem escape_safe {bytes : List UInt8} {c : UInt8} (h : c ∈ escape bytes) :
    c.toNat < 128 ∧ c ≠ 47 ∧ c ≠ 61 :=
  Proofs.Formats.Hive.PartitionPath.Percent.escape_safe h

theorem decode_encode (value : String) : decode (encode value) = .ok value :=
  Proofs.Formats.Hive.PartitionPath.Percent.decode_encode value

theorem decode_encodeWith (escapeUnderscore : Bool) (value : String) :
    decode (encodeWith escapeUnderscore value) = .ok value :=
  Proofs.Formats.Hive.PartitionPath.Percent.decode_encodeWith escapeUnderscore value

theorem encodeWith_avoids_underscore (value : String) : '_' ∉ (encodeWith true value).toList :=
  Proofs.Formats.Hive.PartitionPath.Percent.encodeWith_avoids_underscore value

end Percent

/-- Lookup exactly represents membership when decoded keys are unique. -/
theorem lookup_eq_some_iff {entries : Partition} {key : String} {value : Option String}
    (h : (entries.map Prod.fst).Nodup) : lookup key entries = some value ↔ (key, value) ∈ entries :=
  Proofs.Formats.Hive.PartitionPath.lookup_eq_some_iff h

/-- A successful parse has unique keys and a lookup result for every required key.
A required key may be present with a null value. -/
theorem parse_lookup {options : Options} {path : String} {entries : Partition}
    (h : parse options path = .ok entries) :
    (entries.map Prod.fst).Nodup ∧
      ∀ key ∈ options.requiredKeys, ∃ value, lookup key entries = some value :=
  Proofs.Formats.Hive.PartitionPath.parse_lookup h

/-- Joining slash-free segments and splitting on slash recovers every component. -/
theorem splitOn_slash_intercalate (first : String) (rest : List String)
    (safe : ∀ segment ∈ first :: rest, '/' ∉ segment.toList) :
    (String.intercalate "/" (first :: rest)).splitOn "/" = first :: rest :=
  Proofs.Formats.Hive.PartitionPath.splitOn_slash_intercalate first rest safe

/-- A successfully rendered directory parses back to the exact ordered entries
under the same path options, including explicit nulls and empty text. -/
theorem parse_render_of_ok {options : Options} {entries : Partition} {directory : String}
    (rendered : render options entries = .ok directory) : parse options directory = .ok entries :=
  Proofs.Formats.Hive.PartitionPath.parse_render_of_ok rendered

end Silmaril.Formats.Hive.PartitionPath
