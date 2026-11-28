module

import Silmaril.Formats.Compression.Brotli.ContextMap.Thms
meta import Silmaril.Formats.Compression.Brotli.ContextMap.Defs

namespace Silmaril.Formats.Compression.Brotli.ContextMap

private def cursor (bits : List Bool) : LSBReader :=
  let width := bits.length % 8
  let lead := LSBWriter.empty.writeBits (bits.take width)
  let bytes := LSBWriter.empty.writeBits (bits.drop width)
  ⟨lead.buffer, lead.count, bytes.bytes.data.toList, 21⟩

private def observed (result : Except Error (Prefix × LSBReader)) :
    Option (List Nat × List (Option Nat) × Nat × Option Bool) := do
  let (parsed, after) ← result.toOption
  let (fields, cells) := match parsed with
    | .implicit entries => ([entries, 1], [parsed.implicitIndex? (entries - 1), parsed.implicitIndex? entries])
    | .coded entries trees rleMax table => ([entries, trees, rleMax, table.alphabetSize], [])
  pure (fields, cells, after.totalRead, after.readBit |>.map Prod.fst)

private def errorOf (result : Except Error (Prefix × LSBReader)) : Option Error :=
  match result with
  | .error reason => some reason
  | .ok _ => none

private def countTwo := [true, false, false, false]
private def noRle := countTwo ++ [false] ++ natBits 1 2 ++ natBits 0 2 ++ [true]
private def maxRle := countTwo ++ [true, true, true, true, true] ++ natBits 1 2 ++ natBits 0 2 ++ natBits 17 5

#guard observed (read .literal 256 ⟨16384, 1⟩ (cursor [false, true])) =
  some ([16384, 1], [some 0, none], 22, some true)
#guard observed (read .distance 2 ⟨8, 1⟩ (cursor [false, true])) =
  some ([8, 1], [some 0, none], 22, some true)
#guard observed (read .distance 1 ⟨4, 10⟩ (cursor (noRle ++ [true]))) =
  some ([4, 2, 0, 2], [], 31, some true)
#guard observed (read .literal 1 ⟨64, 18⟩ (cursor (maxRle ++ [true]))) =
  some ([64, 2, 16, 18], [], 39, some true)

#guard errorOf (read .literal 0 ⟨0, 0⟩ (cursor [])) = some .invalidBlockTypes
#guard errorOf (read .distance 257 ⟨1028, 1⟩ (cursor [false])) = some .invalidBlockTypes
#guard errorOf (read .literal 1 ⟨63, 1⟩ (cursor [false])) = some .entryLimit
#guard errorOf (read .distance 1 ⟨4, 10⟩ (cursor [true, false])) = some (.count .truncated)
#guard errorOf (read .distance 1 ⟨4, 11⟩ (cursor ([true] ++ natBits 2 3 ++ natBits 0 2))) = some .treeExtent
#guard errorOf (read .distance 1 ⟨4, 4⟩ (cursor noRle)) = some .bitLimit
#guard errorOf (read .literal 1 ⟨64, 18⟩ (cursor (maxRle.take 8))) = some .truncated
#guard errorOf (read .literal 1 ⟨64, 17⟩ (cursor maxRle)) = some (.description (.simple .bitLimit))
#guard errorOf (read .distance 1 ⟨4, 10⟩ (cursor (noRle.take 9))) = some (.description (.simple .truncated))

end Silmaril.Formats.Compression.Brotli.ContextMap
