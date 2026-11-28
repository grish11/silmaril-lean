module

import Silmaril.Formats.Compression.Brotli.ContextMap.Decode.Thms
meta import Silmaril.Formats.Compression.Brotli.ContextMap.Decode.Defs

open Silmaril.Formats.Compression

namespace Silmaril.Formats.Compression.Brotli.ContextMap.Decode

private def cursor (bits : List Bool) : LSBReader :=
  let width := bits.length % 8
  let lead := LSBWriter.empty.writeBits (bits.take width)
  let bytes := LSBWriter.empty.writeBits (bits.drop width)
  ⟨lead.buffer, lead.count, bytes.bytes.data.toList, 21⟩

private def observed (result : Except Error (Map × LSBReader)) : Option (Map × Nat × Option Bool) := do
  let (parsed, after) ← result.toOption
  pure (parsed, after.totalRead, after.readBit |>.map Prod.fst)

private def errorOf (result : Except Error (Map × LSBReader)) : Option Error :=
  match result with
  | .error reason => some reason
  | .ok _ => none

private def countTwo := [true, false, false, false]
private def selector := natBits 1 2
private def direct := countTwo ++ [false] ++ selector ++ natBits 1 2 ++ [false, true]
private def singleton := countTwo ++ [false] ++ selector ++ natBits 0 2 ++ [true]
private def rle := countTwo ++ [true] ++ natBits 0 4 ++ selector ++ natBits 1 2 ++
  natBits 1 2 ++ natBits 2 2
private def oversizedRun := countTwo ++ [true] ++ natBits 15 4 ++ selector ++ natBits 0 2 ++
  natBits 16 5 ++ natBits 0 16

#guard observed (read .literal 256 ⟨16384, 0, 1⟩ (cursor [false, true])) =
  some (.implicit 16384, 22, some true)

#guard observed (read .distance 1 ⟨4, 4, 16⟩ (cursor (direct ++ [false, true, false, true, false, true]))) =
  some (.coded 2 [0, 1, 0, 1], 37, some true)

#guard observed (read .distance 1 ⟨4, 4, 11⟩ (cursor (singleton ++ [true, false]))) =
  some (.coded 2 [1, 0, 1, 0], 32, some false)

#guard observed (read .distance 1 ⟨4, 2, 21⟩ (cursor (rle ++ [false, true, true, false, true]))) =
  some (.coded 2 [0, 0, 0, 1], 42, some true)

-- Seeking both trees in the final vector, even if all MTF positions are identical.
#guard errorOf (read .distance 1 ⟨4, 4, 11⟩ (cursor (singleton ++ [false]))) = some .unusedTree
#guard errorOf (read .distance 1 ⟨4, 3, 11⟩ (cursor (singleton ++ [true]))) = some .symbolLimit
#guard errorOf (read .distance 1 ⟨4, 4, 10⟩ (cursor (singleton ++ [true]))) = some .bitLimit
#guard errorOf (read .distance 1 ⟨4, 4, 11⟩ (cursor singleton)) = some .truncated
#guard errorOf (read .distance 1 ⟨3, 4, 11⟩ (cursor (singleton ++ [true]))) = some (.prefixError .entryLimit)
#guard errorOf (read .distance 1 ⟨4, 4, 17⟩ (cursor (singleton.take 9))) =
  some (.prefixError (.description (.simple .truncated)))

#guard errorOf (read .distance 1 ⟨4, 4, 21⟩ (cursor (rle ++ [false]))) = some .truncated
#guard errorOf (read .distance 1 ⟨4, 4, 18⟩ (cursor (rle ++ [false, true]))) = some .bitLimit
#guard errorOf (read .distance 1 ⟨4, 4, 21⟩ (cursor (rle ++ [false, true, false, true]))) = some .runExtent
#guard errorOf (read .distance 1 ⟨4, 4, 35⟩ (cursor oversizedRun)) = some .runExtent
#guard errorOf (read .distance 1 ⟨4, 4, 21⟩ (cursor (direct ++ [false, false, false, false, true]))) =
  some .unusedTree
#guard errorOf (read .distance 1 ⟨4, 4, 21⟩ (cursor (direct ++ [false]))) = some (.symbol .truncated)

#guard errorOf (read .distance 1 ⟨4, 4, 16⟩
    (cursor (countTwo ++ [true] ++ natBits 0 4 ++ selector ++ natBits 0 2 ++ natBits 3 2))) =
  some (.prefixError (.description (.simple .symbolRange)))

-- The largest literal extent can be filled by a zero-bit code, with
-- exactly the declared number of work units and the same bit offset.
#guard (observed (read .literal 256 ⟨16384, 16384, 11⟩ (cursor (singleton ++ [true, false])))).map
    (fun (map, offset, tail) => (map.indices.length, map.indices.take 4, offset, tail)) =
  some (16384, [1, 0, 1, 0], 32, some false)

end Silmaril.Formats.Compression.Brotli.ContextMap.Decode
