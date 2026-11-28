module

public import Silmaril.Formats.Compression.Brotli.ContextMap.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.ContextMap.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.ContextMap

/-- An implicit map supplies exactly the zero indices of its declared extent. -/
theorem Prefix.implicitIndex_iff {entries index tree : Nat} :
    (Prefix.implicit entries).implicitIndex? index = some tree ↔ index < entries ∧ tree = 0 := by
  by_cases fits : index < entries <;> simp [Prefix.implicitIndex?, fits, eq_comm]

theorem Wire.implicit_bits {entries : Nat} {bits : List Bool}
    (wire : Wire entries bits (.implicit entries)) : bits = [false] := by
  cases wire
  rfl

/-- A coded prefix validates its alphabet without decoding map entries. -/
theorem Wire.coded_bounds {entries trees rleMax : Nat} {bits : List Bool}
    {table : Huffman.Description.Table} (wire : Wire entries bits (.coded entries trees rleMax table)) :
    2 ≤ trees ∧ trees ≤ 256 ∧ trees ≤ entries ∧ rleMax ≤ 16 ∧
      table.alphabetSize = trees + rleMax ∧ table.alphabetSize ≤ 272 :=
  Proofs.Formats.Compression.Brotli.ContextMap.Wire.coded_bounds wire

/-- Success preserves untouched following bits under one cap for the
    count, RLE flag and optional prefix-code description. -/
theorem read_sound {kind : Kind} {types : Nat} {limits : Limits} {before after : LSBReader}
    {input : List Bool} {result : Prefix} (rep : before.Rep input) (count : before.count < 8)
    (read : read kind types limits before = .ok (result, after)) :
    1 ≤ types ∧ types ≤ 256 ∧ kind.extent types ≤ limits.entries ∧
    ∃ used suffix, Wire (kind.extent types) used result ∧ input = used ++ suffix ∧
      after.Rep suffix ∧ after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧
      used.length ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.ContextMap.read_sound rep count read

end Silmaril.Formats.Compression.Brotli.ContextMap
