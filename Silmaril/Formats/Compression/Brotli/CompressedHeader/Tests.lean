module

import Silmaril.Formats.Compression.Brotli.CompressedHeader.Thms
meta import Silmaril.Formats.Compression.Brotli.CompressedHeader.Defs

open Silmaril.Formats.Compression

namespace Silmaril.Formats.Compression.Brotli.CompressedHeader

private def cursor (bits : List Bool) : LSBReader :=
  let width := bits.length % 8
  let lead := LSBWriter.empty.writeBits (bits.take width)
  let bytes := LSBWriter.empty.writeBits (bits.drop width)
  ⟨lead.buffer, lead.count, bytes.bytes.data.toList, 7⟩

private def singleton (symbol width : Nat) : List Bool :=
  natBits 1 2 ++ natBits 0 2 ++ natBits symbol width

private def initial (postfixBits direct mode : Nat) : List Bool :=
  [false, false, false] ++ natBits postfixBits 2 ++ natBits direct 4 ++ natBits mode 2

private def maps := [false, false]
private def literalAndCommand := singleton 65 8 ++ singleton 703 10
private def standard := initial 0 0 1 ++ maps ++ literalAndCommand ++ singleton 63 6
private def maximum := initial 3 15 3 ++ maps ++ literalAndCommand ++ singleton 519 10

private def observed (result : Except Error (Header × LSBReader)) :
    Option (List Nat × List (Option (Nat × Nat)) × Nat × Option Bool) := do
  let (header, after) ← result.toOption
  let tables := header.literalTrees ++ header.insertCopyTrees ++ header.distanceTrees
  pure (tables.map (·.alphabetSize), (tables.zip [65, 703, header.initial.fields.distanceAlphabet - 1]).map
    (fun (table, symbol) => table.codeFor symbol), after.totalRead, after.readBit |>.map Prod.fst)

private def errorOf (result : Except Error (Header × LSBReader)) : Option Error :=
  match result with
  | .error error => some error
  | .ok _ => none

#guard observed (read ⟨68, 3, 49⟩ (cursor (standard ++ [true]))) =
  some ([256, 704, 64], [some (0, 0), some (0, 0), some (0, 0)], 56, some true)
#guard observed (read ⟨68, 3, 53⟩ (cursor (maximum ++ [false]))) =
  some ([256, 704, 520], [some (0, 0), some (0, 0), some (0, 0)], 60, some false)

#guard errorOf (read ⟨67, 3, 49⟩ (cursor standard)) = some .mapEntryLimit
#guard errorOf (read ⟨68, 2, 49⟩ (cursor standard)) = some .treeLimit
#guard errorOf (read ⟨68, 3, 48⟩ (cursor standard)) = some (.tree .distance 0 (.simple .bitLimit))
#guard errorOf (read ⟨68, 3, 49⟩ (cursor (standard.take 48))) = some (.tree .distance 0 (.simple .truncated))
#guard errorOf (read ⟨68, 3, 49⟩ (cursor (standard.take 12))) =
  some (.map .distance (.prefixError (.count .truncated)))
#guard errorOf (read ⟨68, 3, 53⟩ (cursor
    (initial 1 0 0 ++ maps ++ literalAndCommand ++ singleton 112 7))) =
  some (.tree .distance 0 (.simple .symbolRange))
#guard errorOf (read ⟨68, 3, 0⟩ (cursor standard)) = some (.initial (.controls .bitLimit))

#guard errorOf (read ⟨68, 4, 60⟩ (cursor
    (initial 0 0 0 ++ [false, true, false, false, false, false] ++ singleton 1 1 ++ [false]))) =
  some (.map .distance .unusedTree)
#guard errorOf (read ⟨68, 3, 49⟩ (cursor (standard.take 25))) =
  some (.tree .insertCopy 0 .truncated)

end Silmaril.Formats.Compression.Brotli.CompressedHeader
