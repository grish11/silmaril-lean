module

import Silmaril.Formats.Compression.Brotli.Huffman.MainTable.Thms
meta import Silmaril.Formats.Compression.Brotli.Huffman.MainTable.Defs

namespace Silmaril.Formats.Compression.Brotli.Huffman.MainTable

private def buffered (bits : List Bool) : LSBReader :=
  let width := bits.length % 8
  let front := LSBWriter.empty.writeBits (bits.take width)
  let full := LSBWriter.empty.writeBits (bits.drop width)
  ⟨front.buffer, front.count, full.bytes.data.toList, 3⟩

private def sparse : Option CodeLengths.Table :=
  let depths := CodeLengths.symbolOrder.map fun symbol =>
    if symbol < 2 then CodeLengths.Length.one else .zero
  (CodeLengths.read 74 (buffered ([false, false] ++ depths.flatMap CodeLengths.Length.bits))).toOption.map
    Prod.fst

private def checked (cap : Nat) : Except Error (Table × LSBReader) := do
  let some table := sparse | throw .invalidLengths
  read ⟨5, cap⟩ 5 table (buffered [false, true, false, true, true])

#guard
  ((checked 4).toOption.map fun (table, after) =>
    (table.lengths, (List.range 6).map table.decoder.encodeSymbol, after.totalRead,
      after.readBit |>.map Prod.fst)) =
    some ([0, 1, 0, 1, 0], [none, some (0, 1), none, some (1, 1), none, none], 7, some true)

#guard
  (match checked 3 with
   | .ok _ => none
   | .error reason => some reason) = some (.lengths (.symbol .bitLimit))

#guard
  ((Internal.install ((List.range 14).map (· + 1) ++ [15, 15])).toOption.map fun table =>
    (table.decoder.encodeSymbol 14, table.decoder.encodeSymbol 15)) =
    some (some (32766, 15), some (32767, 15))

end Silmaril.Formats.Compression.Brotli.Huffman.MainTable
