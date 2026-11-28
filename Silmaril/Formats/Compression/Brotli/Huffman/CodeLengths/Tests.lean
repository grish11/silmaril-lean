module

import Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths.Thms
meta import Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths.Defs

namespace Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths

private def wire (skip : Nat) (lengths : List Length) : List Bool :=
  natBits skip 2 ++ lengths.flatMap Length.bits

/-- Model an exact suffix starting partway through a byte. -/
private def cursor (bits : List Bool) : LSBReader :=
  let frontWidth := bits.length % 8
  let front := LSBWriter.empty.writeBits (bits.take frontWidth)
  let full := LSBWriter.empty.writeBits (bits.drop frontWidth)
  ⟨front.buffer, front.count, full.bytes.data.toList, 13⟩

private def controls (limit : Nat) (bits : List Bool) : Option Error :=
  match read limit (cursor bits) with
  | .error error => some error
  | .ok _ => none

#guard controls 74 (wire 1 []) = some .unsupportedSimple
#guard controls 74 [false] = some .truncated
#guard controls 74 (wire 0 [] ++ [true, true, true]) = some .truncated
#guard controls 5 (wire 0 [.one, .one]) = some .bitLimit
#guard controls 1 (wire 0 [.one, .one]) = some .bitLimit
#guard controls 74 (wire 0 [.two, .one, .one]) = some .oversubscribed
#guard controls 74 (wire 3 (List.replicate 15 .zero)) = some .incomplete
#guard controls 74 (wire 3 ([.five, .five] ++ List.replicate 13 .zero)) = some .incomplete

private def singletonWire := wire 2 (.one :: List.replicate 15 .zero)

#guard controls 74 (singletonWire.take 35) = some .truncated
#guard controls 35 singletonWire = some .bitLimit

#guard
    (match read 36 (cursor (singletonWire ++ [true])) with
     | .ok (table, after) => (table.codeFor 3, table.codeFor 4, after.totalRead, after.readBits 1 |>.map Prod.fst)
     | .error _ => (none, none, 0, none)) =
      (some (0, 0), none, 49, some 1)

/- A complete table finishes at mass 32, leaving the following bits at
    their original cursor. Equal widths use numeric, rather than wire, order. -/
#guard
    (match read 10 (cursor (wire 3 [.one, .one] ++ [true, false, true])) with
     | .ok (table, after) => (table.codeFor 0, table.codeFor 4, after.totalRead, after.readBits 3 |>.map Prod.fst)
     | .error _ => (none, none, 0, none)) =
      (some (0, 1), some (1, 1), 23, some 5)

end Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths
