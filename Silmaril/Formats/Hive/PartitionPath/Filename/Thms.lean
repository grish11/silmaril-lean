module

public import Silmaril.Formats.Hive.PartitionPath.Filename.Defs
import Silmaril.Proofs.Formats.Hive.PartitionPath.Filename

public section

namespace Silmaril.Formats.Hive.PartitionPath.Filename

/-- Exact success means an affordable leaf and an admitted declared prefix. -/
theorem parse_ok_iff (maxFilenameBytes : Nat) (keys : List String) (encoding : Positional.Encoding)
    (options : Options) (directory leaf : String) (entries : Partition) :
    parse maxFilenameBytes keys encoding options directory leaf = .ok entries ↔
      leaf.utf8ByteSize ≤ maxFilenameBytes ∧
        ∃ raw, prefixTokens leaf = .ok raw ∧ Positional.parseSegments keys encoding options raw = .ok entries :=
  Proofs.Formats.Hive.PartitionPath.Filename.parse_ok_iff maxFilenameBytes keys encoding options directory leaf entries

/-- Binding is independent of the already checked parent. -/
theorem parse_parent_irrel (maxFilenameBytes : Nat) (keys : List String) (encoding : Positional.Encoding)
    (options : Options) (left right leaf : String) :
    parse maxFilenameBytes keys encoding options left leaf =
      parse maxFilenameBytes keys encoding options right leaf := rfl

theorem parse_keys_present {maxFilenameBytes : Nat} {keys : List String} {encoding : Positional.Encoding}
    {options : Options} {directory leaf : String} {entries : Partition}
    (parsed : parse maxFilenameBytes keys encoding options directory leaf = .ok entries) :
    entries.map Prod.fst = keys ∧ ∀ entry ∈ entries, entry.2.isSome = true :=
  Proofs.Formats.Hive.PartitionPath.Filename.parse_keys_present parsed

end Silmaril.Formats.Hive.PartitionPath.Filename
