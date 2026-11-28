module

import Silmaril.Formats.Compression.Brotli.BlockTypes.Thms
meta import Silmaril.Formats.Compression.Brotli.BlockTypes.Defs

namespace Silmaril.Formats.Compression.Brotli.BlockTypes

private def cursor (bits : List Bool) : LSBReader :=
  let width := bits.length % 8
  let lead := LSBWriter.empty.writeBits (bits.take width)
  let bytes := LSBWriter.empty.writeBits (bits.drop width)
  ⟨lead.buffer, lead.count, bytes.bytes.data.toList, 13⟩

private def count (width extra : Nat) : List Bool := [true] ++ natBits width 3 ++ natBits extra width

private def oneSymbol (code width : Nat) : List Bool := natBits 1 2 ++ natBits 0 2 ++ natBits code width

private def multiple : List Bool :=
  count 0 0 ++ oneSymbol 0 2 ++ oneSymbol 25 5 ++ natBits (2 ^ 24 - 1) 24

private def observed (cap : Nat) (bits : List Bool) :
    Option (List Nat × Nat × Nat × Option Bool) := do
  let (parsed, next) ← (read cap (cursor bits)).toOption
  let first := match parsed.literal with
    | .single => 0
    | .multiple _ _ _ length => length
  pure ([parsed.literal.typeCount, parsed.insertCopy.typeCount, parsed.distance.typeCount],
    first, next.totalRead, next.readBit |>.map Prod.fst)

private def rejection (cap : Nat) (bits : List Bool) : Option Error :=
  match read cap (cursor bits) with
  | .error error => some error
  | .ok _ => none

#guard observed 3 [false, false, false, true] = some ([1, 1, 1], 0, 16, some true)
#guard observed 45 (multiple ++ [false, false, true]) = some ([2, 1, 1], 16793840, 58, some true)
#guard rejection 2 [false, false, false] = some .bitLimit
#guard rejection 11 [true, true, true, true, false] = some .truncated
#guard rejection 44 (multiple ++ [false, false]) = some .bitLimit
#guard rejection 100 (multiple.take 42) = some .truncated
#guard rejection 100 (count 0 0 ++ oneSymbol 0 2 ++ oneSymbol 26 5) =
  some (.description (.simple .symbolRange))
#guard rejection 100 (count 0 0 ++ natBits 1 2 ++ natBits 1 2 ++ natBits 0 4) =
  some (.description (.simple .duplicateSymbol))
#guard (Internal.readCount ⟨cursor (count 7 127), 11⟩).toOption.map Prod.fst = some 256

end Silmaril.Formats.Compression.Brotli.BlockTypes
