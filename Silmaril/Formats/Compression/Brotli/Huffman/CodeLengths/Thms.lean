module

public import Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Huffman.CodeLengths.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths

/-- Positive remaining Kraft space means every transmitted slot was read.
    This is the only way the singleton description can finish. -/
theorem LengthsWire.exhausts_slots {slots space final : Nat} {lengths : List Length} {bits : List Bool}
    (wire : LengthsWire slots space lengths final bits) (incomplete : 0 < final) :
    lengths.length = slots :=
  Proofs.Formats.Compression.Brotli.Huffman.CodeLengths.LengthsWire.exhausts_slots wire incomplete

/-- Success consumes one exact §3.5 code-length-code description. The
    remainder is preserved at bit granularity, under the caller's limit
    and the structural bound of two selector bits and 18 four-bit fields. -/
theorem read_sound {bitLimit : Nat} {before after : LSBReader} {input : List Bool} {table : Table}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read bitLimit before = .ok (table, after)) :
    ∃ used suffix, Wire used table ∧ input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit ∧ used.length ≤ 74 :=
  Proofs.Formats.Compression.Brotli.Huffman.CodeLengths.read_sound rep count read

/-- A checked singleton has exactly one present code and uses zero bits. -/
theorem Table.singleton_code {table : Table} {only : Nat}
    (kind : table.codes = .singleton only) : only < 18 ∧ table.codeFor only = some (0, 0) ∧
      ∀ other, only ≠ other → table.codeFor other = none :=
  Proofs.Formats.Compression.Brotli.Huffman.CodeLengths.Table.singleton_code kind

/-- The shared canonical code of each positive entry is recoverable by
    the shared LSB Huffman reader, with a width at most five. -/
theorem Table.canonical_code {table : Table} {codes : HuffmanTable} {symbol : Nat}
    (kind : table.codes = .canonical codes) (index : symbol < table.lengths.length)
    (positive : 0 < table.lengths[symbol].value) :
    ∃ code width, table.codeFor symbol = some (code, width) ∧ 0 < width ∧ width ≤ 5 ∧
      code < 2 ^ width ∧ lookupEntry codes.entries code width = some symbol ∧
      ∀ depth < width, lookupEntry codes.entries (code >>> (width - depth)) depth = none :=
  Proofs.Formats.Compression.Brotli.Huffman.CodeLengths.Table.canonical_code kind index positive

end Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths
