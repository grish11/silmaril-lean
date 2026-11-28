module

import Silmaril.Formats.Compression.Brotli.ContextHeader.Thms
meta import Silmaril.Formats.Compression.Brotli.ContextHeader.Defs

namespace Silmaril.Formats.Compression.Brotli.ContextHeader

private def cursor (bits : List Bool) : LSBReader :=
  let width := bits.length % 8
  let lead := LSBWriter.empty.writeBits (bits.take width)
  let bytes := LSBWriter.empty.writeBits (bits.drop width)
  ⟨lead.buffer, lead.count, bytes.bytes.data.toList, 21⟩

private def observed (result : Except Error (Fields × LSBReader)) :
    Option (Nat × Nat × Nat × List Nat × Nat × Option Bool) := do
  let (fields, next) ← result.toOption
  pure (fields.postfixBits.val, fields.direct, fields.distanceAlphabet,
    fields.modes.map Mode.code, next.totalRead, next.readBit |>.map Prod.fst)

private def errorOf {α : Type} (result : Except Error α) : Option Error :=
  match result with
  | .error reason => some reason
  | .ok _ => none

-- Authored RFC fields exercise every mode, including modes absent from the producer suite.
private def allModes :=
  natBits 3 2 ++ natBits 15 4 ++ [false, false, true, false, false, true, true, true]

#guard observed (readAfter 4 14 (cursor (allModes ++ [true]))) ==
  some (3, 120, 520, [0, 1, 2, 3], 35, some true)
#guard
  (readAfter 256 518 (cursor (List.replicate 519 false))).toOption.map
    (fun (fields, after) => (fields.modes.length, after.totalRead, after.readBit |>.map Prod.fst)) =
  some (256, 539, some false)
#guard observed ((read 11 (cursor ([false, false, false] ++ (⟨0, 0, [.utf8]⟩ : Fields).bits ++ [true]))).map
  (fun (header, after) => (header.fields, after))) == some (0, 0, 64, [2], 32, some true)

#guard errorOf (readAfter 0 14 (cursor allModes)) = some .invalidLiteralTypes
#guard errorOf (readAfter 257 520 (cursor [])) = some .invalidLiteralTypes
#guard errorOf (readAfter 4 13 (cursor allModes)) = some .bitLimit
#guard errorOf (readAfter 4 14 (cursor (allModes.take 1))) = some .truncated
#guard errorOf (readAfter 4 14 (cursor (allModes.take 5))) = some .truncated
#guard errorOf (readAfter 4 14 (cursor (allModes.take 13))) = some .truncated
#guard errorOf (read 20 (cursor (natBits 1 4 ++ natBits 1 2 ++ natBits 1 2 ++ natBits 0 4))) =
  some (.controls (.description (.simple .duplicateSymbol)))
#guard errorOf (read 11 (cursor [false, false, true])) = some (.controls .truncated)
#guard errorOf (read 10 (cursor (List.replicate 11 false))) = some .bitLimit
#guard errorOf (read 11 (cursor (List.replicate 10 false))) = some .truncated

end Silmaril.Formats.Compression.Brotli.ContextHeader
