module

import Silmaril.Formats.Compression.Brotli.Huffman.Description.Thms
meta import Silmaril.Formats.Compression.Brotli.Huffman.Description.Defs

namespace Silmaril.Formats.Compression.Brotli.Huffman.Description

private def cursor (bits : List Bool) : LSBReader :=
  let width := bits.length % 8
  let front := LSBWriter.empty.writeBits (bits.take width)
  let full := LSBWriter.empty.writeBits (bits.drop width)
  ⟨front.buffer, front.count, full.bytes.data.toList, 13⟩

private def simple (alphabet : Nat) (shape : Simple.Shape) : List Bool :=
  natBits 1 2 ++ shape.bits alphabet

private def observed (alphabet cap : Nat) (bits : List Bool) :
    Option (List (Option (Nat × Nat)) × Nat × Option Bool) := do
  let (table, after) ← (read ⟨alphabet, cap⟩ alphabet (cursor bits)).toOption
  pure ((List.range alphabet).map table.codeFor, after.totalRead, after.readBit |>.map Prod.fst)

private def rejects (limits : MainLengths.Limits) (alphabet : Nat) (bits : List Bool) : Option Error :=
  match read limits alphabet (cursor bits) with
  | .ok _ => none
  | .error error => some error

#guard observed 1 4 (simple 1 (.singleton 0) ++ [true]) = some ([some (0, 0)], 17, some true)
#guard observed 3 8 (simple 3 (.pair 2 0) ++ [true]) =
  some ([some (0, 1), none, some (1, 1)], 21, some true)
#guard observed 4 10 (simple 4 (.triple 3 1 0) ++ [true]) =
  some ([some (2, 2), some (3, 2), none, some (0, 1)], 23, some true)
#guard observed 4 13 (simple 4 (.balanced 3 0 2 1) ++ [true]) =
  some ([some (0, 2), some (1, 2), some (2, 2), some (3, 2)], 26, some true)
#guard observed 4 13 (simple 4 (.skewed 3 2 1 0) ++ [true]) =
  some ([some (6, 3), some (7, 3), some (2, 2), some (0, 1)], 26, some true)

private def complex : List Bool :=
  natBits 2 2 ++
    (CodeLengths.Length.one :: List.replicate 15 .zero).flatMap CodeLengths.Length.bits

#guard observed 8 36 (complex ++ [true]) =
  some ((List.range 8).map (fun ordinal => some (ordinal, 3)), 49, some true)

#guard rejects ⟨704, 0⟩ 0 [] = some .alphabetSize
#guard rejects ⟨705, 4⟩ 705 [] = some .alphabetSize
#guard rejects ⟨3, 20⟩ 4 [] = some .alphabetLimit
#guard rejects ⟨4, 1⟩ 4 [true, false] = some .bitLimit
#guard rejects ⟨4, 2⟩ 4 [true] = some .truncated
#guard rejects ⟨3, 20⟩ 3 (simple 3 (.singleton 3)) = some (.simple .symbolRange)
#guard rejects ⟨4, 20⟩ 4 (simple 4 (.pair 1 1)) = some (.simple .duplicateSymbol)
#guard rejects ⟨4, 20⟩ 4 ((simple 4 (.balanced 0 1 2 3)).take 12) = some (.simple .truncated)
#guard rejects ⟨4, 12⟩ 4 (simple 4 (.balanced 0 1 2 3)) = some (.simple .bitLimit)
#guard rejects ⟨8, 35⟩ 8 complex = some (.secondary .bitLimit)
#guard rejects ⟨8, 40⟩ 8 (natBits 3 2) = some (.secondary .truncated)
#guard rejects ⟨7, 36⟩ 7 complex = some (.main (.lengths .incomplete))

#guard (match (Table.singleton 4 3 (by decide)).readSymbol (cursor []) with
        | some (symbol, after) => some (symbol, after.totalRead, after.readBit.isNone)
        | none => none) = some (3, 13, true)

end Silmaril.Formats.Compression.Brotli.Huffman.Description
