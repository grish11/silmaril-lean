module

public import Silmaril.Formats.Hive.PartitionPath.Filename.Defs
import Silmaril.Formats.Hive.PartitionPath.Positional.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.PartitionPath.Filename

open Silmaril.Formats.Hive.PartitionPath
open Silmaril.Formats.Hive.PartitionPath.Filename

theorem parse_ok_iff (maxFilenameBytes : Nat) (keys : List String) (encoding : Positional.Encoding)
    (options : Options) (directory leaf : String) (entries : Partition) :
    Filename.parse maxFilenameBytes keys encoding options directory leaf = .ok entries ↔
      leaf.utf8ByteSize ≤ maxFilenameBytes ∧
        ∃ raw, prefixTokens leaf = .ok raw ∧ Positional.parseSegments keys encoding options raw = .ok entries := by
  by_cases bytes : leaf.utf8ByteSize ≤ maxFilenameBytes
  · cases tokenized : prefixTokens leaf <;> simp [Filename.parse, Nat.not_lt.mpr bytes, bytes, tokenized, Except.bind]
  · simp [Filename.parse, Nat.lt_of_not_ge bytes, bytes]

theorem parse_keys_present {maxFilenameBytes : Nat} {keys : List String} {encoding : Positional.Encoding}
    {options : Options} {directory leaf : String} {entries : Partition}
    (parsed : Filename.parse maxFilenameBytes keys encoding options directory leaf = .ok entries) :
    entries.map Prod.fst = keys ∧ ∀ entry ∈ entries, entry.2.isSome = true := by
  obtain ⟨_, _, _, bound⟩ := (parse_ok_iff _ _ _ _ _ _ _).mp parsed
  exact Positional.parseSegments_keys_present bound

end Silmaril.Proofs.Formats.Hive.PartitionPath.Filename
