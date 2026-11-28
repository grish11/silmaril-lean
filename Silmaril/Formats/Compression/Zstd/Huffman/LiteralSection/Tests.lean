module

import Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection.Defs
meta import Batteries.Data.Except

namespace Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection

private def limits : Limits := ⟨262144, 262144, ⟨128, ⟨256, 11⟩⟩⟩
private def tail : List UInt8 := [0, 0xff, 0x42]
private def single : List UInt8 := [0x32, 0xc0, 0, 0x80, 0x10, 0x0b]
private def four : List UInt8 := [0x66, 0, 3, 0x80, 0x10, 1, 0, 1, 0, 1, 0, 5, 6, 7, 1]

#guard read limits (single ++ tail) = .ok ⟨⟨.one10, 3, 3⟩, [0, 1, 1], 6, tail⟩
#guard read limits (four ++ tail) = .ok ⟨⟨.four10, 6, 12⟩, [0, 1, 1, 0, 1, 1], 15, tail⟩
#guard read limits [0x02, 0xc0, 0, 0x80, 0x10, 1] = .ok ⟨⟨.one10, 0, 3⟩, [], 6, []⟩
#guard readHeader [0x6a, 0, 0x30, 0, 0xff] = .ok (⟨.four14, 6, 12⟩, [0xff])
#guard readHeader [0x6e, 0, 0, 3, 0, 0xff] = .ok (⟨.four18, 6, 12⟩, [0xff])

#guard read limits [0] = .error (.unsupported .raw)
#guard read limits [1] = .error (.unsupported .rle)
#guard read limits [3] = .error (.unsupported .treeless)
#guard read limits [0x0e, 0, 0, 0] = .error .truncatedHeader
#guard read limits (single.take 5) = .error .truncatedBody
#guard read { limits with inputBytes := 5 } single = .error .inputLimit
#guard read { limits with outputBytes := 5 } four = .error .outputLimit
#guard read limits [0x0e, 0, 0, 0, 0x80] = .error .inputLimit
#guard read limits [0x1e, 0, 0x20, 0, 0] = .error .outputLimit
#guard read limits [0x32, 0xc0, 0, 0x80, 0x10, 0] = .error (.single .badEndMarker)
#guard read limits [0x32, 0xc0, 0, 0x80, 0, 0x0b] = .error (.tree (.direct .zeroMass))
#guard read limits (four.take 14 ++ [0]) = .error (.four (.stream 4 .badEndMarker))

end Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection
