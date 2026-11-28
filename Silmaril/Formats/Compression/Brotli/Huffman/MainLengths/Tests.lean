module

import Silmaril.Formats.Compression.Brotli.Huffman.MainLengths.Thms
meta import Silmaril.Formats.Compression.Brotli.Huffman.MainLengths.Defs

namespace Silmaril.Formats.Compression.Brotli.Huffman.MainLengths

private def cursor (bits : List Bool) : LSBReader :=
  let frontWidth := bits.length % 8
  let front := LSBWriter.empty.writeBits (bits.take frontWidth)
  let full := LSBWriter.empty.writeBits (bits.drop frontWidth)
  ⟨front.buffer, front.count, full.bytes.data.toList, 13⟩

private def tableFor (fields : List (Nat × CodeLengths.Length)) : Option CodeLengths.Table :=
  let descriptions := CodeLengths.symbolOrder.map fun symbol =>
    ((fields.find? (fun pair => pair.1 == symbol)).map Prod.snd).getD .zero
  (CodeLengths.read 74 (cursor ([false, false] ++ descriptions.flatMap CodeLengths.Length.bits))).toOption.map
    Prod.fst

private def run (limits : Limits) (alphabet : Nat) (fields : List (Nat × CodeLengths.Length))
    (bits : List Bool) : Except Error (List Nat × Nat × Option Bool) := do
  let some table := tableFor fields | throw (.symbol .invalidCode)
  let (lengths, after) ← read limits alphabet table (cursor bits)
  return (lengths, after.totalRead, (after.readBit).map Prod.fst)

private def rejects (limits : Limits) (alphabet : Nat) (fields : List (Nat × CodeLengths.Length))
    (bits : List Bool) : Option Error :=
  match run limits alphabet fields bits with
  | .error error => some error
  | .ok _ => none

private def observed (history : History) (token : Token) :=
  let run := token.emit history
  (run.value.val, run.count, run.next.prior.val, run.next.previousRun)

#guard observed History.start (.repeat .previous 3) = (8, 6, 8, some (.previous, 6))
#guard observed ⟨7, some (.previous, 6)⟩ (.repeat .previous 2) = (7, 15, 7, some (.previous, 21))
#guard observed ⟨7, some (.zero, 3)⟩ (.repeat .zero 1) = (0, 9, 7, some (.zero, 12))
#guard observed ⟨7, some (.previous, 6)⟩ (.repeat .zero 1) = (0, 4, 7, some (.zero, 4))
#guard observed ⟨7, some (.zero, 12)⟩ (.repeat .previous 0) = (7, 3, 7, some (.previous, 3))
#guard observed ⟨7, some (.previous, 6)⟩ (.length 0) = (0, 1, 7, none)
#guard observed ⟨7, some (.zero, 6)⟩ (.length 4) = (4, 1, 4, none)

#guard
  (run ⟨4, 2⟩ 4 [(0, .one), (1, .one)] [true, true, false]).toOption =
    some ([1, 1, 0, 0], 15, some false)
#guard
  (run ⟨9, 0⟩ 9 [(3, .one)] [true]).toOption =
    some (List.replicate 8 3 ++ [0], 13, some true)

#guard rejects ⟨704, 0⟩ 704 [(0, .one)] [] = some .incomplete
#guard rejects ⟨7, 0⟩ 7 [(3, .one)] [] = some .incomplete
#guard rejects ⟨7, 0⟩ 8 [(3, .one)] [] = some .alphabetLimit
#guard rejects ⟨705, 0⟩ 705 [(3, .one)] [] = some .alphabetSize
#guard rejects ⟨704, 0⟩ 0 [(3, .one)] [] = some .alphabetSize
#guard rejects ⟨4, 0⟩ 4 [(0, .one), (1, .one)] [true] = some (.symbol .bitLimit)
#guard rejects ⟨4, 8⟩ 4 [(0, .one), (1, .one)] [] = some (.symbol .truncated)
#guard rejects ⟨5, 1⟩ 5 [(16, .one)] [true] = some .bitLimit
#guard rejects ⟨5, 2⟩ 5 [(16, .one)] [true] = some .truncated
#guard rejects ⟨2, 3⟩ 2 [(17, .one)] [false, false, false] = some .repeatExtent
#guard rejects ⟨3, 3⟩ 3 [(1, .one), (2, .one)] [true, false, false] = some .oversubscribed

end Silmaril.Formats.Compression.Brotli.Huffman.MainLengths
