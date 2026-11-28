module

import Silmaril.Formats.Compression.Brotli.Command.Thms
meta import Silmaril.Formats.Compression.Brotli.Command.Defs

open Silmaril.Formats.Compression

namespace Silmaril.Formats.Compression.Brotli.Command

private def cursor (bits : List Bool) : LSBReader :=
  let width := bits.length % 8
  let lead := LSBWriter.empty.writeBits (bits.take width)
  let bytes := LSBWriter.empty.writeBits (bits.drop width)
  ⟨lead.buffer, lead.count, bytes.bytes.data.toList, 5⟩

private def observed (result : Except Error (Value × LSBReader)) :
    Option (Value × Nat × Option Bool) := do
  let (command, after) ← result.toOption
  pure (command, after.totalRead, (after.readBit).map Prod.fst)

private def errorOf (result : Except Error (Value × LSBReader)) : Option Error :=
  match result with
  | .error error => some error
  | .ok _ => none

private def maximum : Fin 704 := 703
private def lastTable : Huffman.Description.Table := .singleton 704 703 (by decide)
private def pairTable : Option Huffman.Description.Table := do
  let bits := natBits 1 2 ++ natBits 1 2 ++ natBits 127 10 ++ natBits 703 10
  let (table, _) ← (Huffman.Description.read ⟨704, 24⟩ 704 (cursor bits)).toOption
  pure table

#guard spec 127 = ⟨⟨8, 1⟩, ⟨54, 4⟩, .implicitZero⟩
#guard spec 128 = ⟨⟨0, 0⟩, ⟨2, 0⟩, .explicit⟩
#guard spec maximum = ⟨⟨22594, 24⟩, ⟨2118, 24⟩, .explicit⟩

#guard observed (readExtras 127 5 (cursor (natBits 1 1 ++ natBits 12 4 ++ [false]))) =
  some (⟨127, 9, 66, .implicitZero⟩, 10, some false)
#guard observed (read lastTable 48 (cursor (List.replicate 48 true ++ [false]))) =
  some (⟨maximum, 16799809, 16779333, .explicit⟩, 53, some false)
#guard observed (read (.singleton 704 0 (by decide)) 0 (cursor [true])) =
  some (⟨0, 0, 2, .implicitZero⟩, 5, some true)
#guard (pairTable.bind fun table => observed (read table 6 (cursor ([false] ++ natBits 1 1 ++ natBits 12 4)))) =
  some (⟨127, 9, 66, .implicitZero⟩, 11, none)
#guard (pairTable.bind fun table => errorOf (read table 1 (cursor []))) = some (.symbol .truncated)

#guard errorOf (read lastTable 23 (cursor [])) = some (.bitLimit .insertExtra)
#guard errorOf (read lastTable 48 (cursor (List.replicate 23 false))) = some (.truncated .insertExtra)
#guard errorOf (read lastTable 47 (cursor (List.replicate 48 false))) = some (.bitLimit .copyExtra)
#guard errorOf (read lastTable 48 (cursor (List.replicate 47 false))) = some (.truncated .copyExtra)
#guard errorOf (read (.singleton 256 0 (by decide)) 0 (cursor [])) = some .alphabet

end Silmaril.Formats.Compression.Brotli.Command
