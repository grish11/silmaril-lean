module

public import Silmaril.Formats.Hive.PartitionPath.Positional.Defs
import Silmaril.Proofs.Formats.Hive.PartitionPath.Positional

public section

namespace Silmaril.Formats.Hive.PartitionPath.Positional

theorem parseSegments_ok_iff (keys : List String) (encoding : Encoding)
    (options : Options) (raw : List String) (entries : Partition) :
    parseSegments keys encoding options raw = .ok entries ↔
      raw.length = keys.length ∧
        ∃ values, raw.mapM (decodeSegment encoding) = .ok values ∧
          entries = keys.zip (values.map some) ∧ validate options entries = .ok () :=
  Proofs.Formats.Hive.PartitionPath.Positional.parseSegments_ok_iff keys encoding options raw entries

theorem parseSegments_keys_present {keys : List String} {encoding : Encoding}
    {options : Options} {raw : List String} {entries : Partition}
    (parsed : parseSegments keys encoding options raw = .ok entries) :
    entries.map Prod.fst = keys ∧ ∀ entry ∈ entries, entry.2.isSome = true :=
  Proofs.Formats.Hive.PartitionPath.Positional.parseSegments_keys_present parsed

/-- Successful parsing uses exactly the declared arity, binds decoded
values left to right, and admits the resulting partition keys. -/
theorem parse_ok_iff (maxDirectoryBytes : Nat) (keys : List String) (encoding : Encoding)
    (options : Options) (directory : String) (entries : Partition) :
    parse maxDirectoryBytes keys encoding options directory = .ok entries ↔
      directory.utf8ByteSize ≤ maxDirectoryBytes ∧ (segments directory).length = keys.length ∧
        ∃ values, (segments directory).mapM (decodeSegment encoding) = .ok values ∧
          entries = keys.zip (values.map some) ∧ validate options entries = .ok () :=
  Proofs.Formats.Hive.PartitionPath.Positional.parse_ok_iff maxDirectoryBytes keys encoding options directory entries

/-- Successful parsing preserves the full ordered key declaration and can
only produce present values. -/
theorem parse_keys_present {maxDirectoryBytes : Nat} {keys : List String} {encoding : Encoding}
    {options : Options} {directory : String} {entries : Partition}
    (parsed : parse maxDirectoryBytes keys encoding options directory = .ok entries) :
    entries.map Prod.fst = keys ∧ ∀ entry ∈ entries, entry.2.isSome = true :=
  Proofs.Formats.Hive.PartitionPath.Positional.parse_keys_present parsed

end Silmaril.Formats.Hive.PartitionPath.Positional
