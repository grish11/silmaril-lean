module

public import Silmaril.Formats.Compression.Brotli.Huffman.Description.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Huffman.Description.Contracts
import Silmaril.Proofs.Formats.Compression.Brotli.Huffman.Description.Symbol

public section

namespace Silmaril.Formats.Compression.Brotli.Huffman.Description

/-- Success accounts for the complete original description and leaves
    its exact suffix, with both alphabet bounds and the shared bit cap. -/
theorem read_sound {limits : MainLengths.Limits} {alphabet : Nat}
    {before after : LSBReader} {input : List Bool} {table : Table}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read limits alphabet before = .ok (table, after)) :
    0 < alphabet ∧ alphabet ≤ 704 ∧ alphabet ≤ limits.alphabet ∧ table.alphabetSize = alphabet ∧
    ∃ used suffix, Wire alphabet used table ∧ input = used ++ suffix ∧ after.Rep suffix ∧
      after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧ used.length ≤ limits.bits ∧
      used.length ≤ 74 + 8 * alphabet :=
  Proofs.Formats.Compression.Brotli.Huffman.Description.read_sound rep count read

/-- The selector in the original wire picks the simple body or a valid
    complex HSKIP value. -/
theorem Wire.selector {alphabet : Nat} {used : List Bool} {table : Table}
    (wire : Wire alphabet used table) :
    ∃ selector rest, used = natBits selector 2 ++ rest ∧
      ((selector = 1 ∧ ∃ shape, Simple.Wire alphabet rest shape ∧ SimpleTableWire alphabet shape table) ∨
        selector ∈ [0, 2, 3]) :=
  Proofs.Formats.Compression.Brotli.Huffman.Description.Wire.selector wire

/-- A simple singleton succeeds even on an empty input and leaves all
    cursor fields unchanged. -/
theorem Table.singleton_read {alphabet only : Nat} (bound : only < alphabet) (before : LSBReader) :
    (Table.singleton alphabet only bound).readSymbol before = some (only, before) :=
  rfl

/-- A singleton's sole ordinal is present with a zero-bit code. -/
theorem Table.singleton_code {alphabet only : Nat} (bound : only < alphabet) (symbol : Nat) :
    (Table.singleton alphabet only bound).codeFor symbol =
      if symbol = only then some (0, 0) else none :=
  rfl

/-- The committed original bits are exactly the selected Huffman code. -/
theorem Table.readBounded_sound {table : Table} {bitLimit symbol : Nat}
    {before after : LSBReader} {input : List Bool} (rep : before.Rep input)
    (count : before.count < 8) (read : table.readBounded bitLimit before = .ok (symbol, after)) :
    ∃ code width suffix, table.codeFor symbol = some (code, width) ∧
      width ≤ 15 ∧ width ≤ bitLimit ∧ input = msbBits code width ++ suffix ∧
      after.Rep suffix ∧ after.count < 8 ∧ after.totalRead = before.totalRead + width :=
  Proofs.Formats.Compression.Brotli.Huffman.Description.readBounded_sound rep count read

end Silmaril.Formats.Compression.Brotli.Huffman.Description
