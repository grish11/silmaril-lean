module

import Silmaril.Formats.Compression.Zstd.Huffman.FseWeights.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.Huffman.FseWeights.Defs
meta import Batteries.Data.Except

namespace Silmaril.Formats.Compression.Zstd.Huffman.FseWeights

private def onFirst : List UInt8 := [0x04, 0x10, 0x3f, 0x03, 0x04]
private def onSecond : List UInt8 := [0x04, 0x10, 0x3f, 0x07, 0x08]
private def shortField : List UInt8 := [0x05, 0x01, 0x45, 0x3f, 0x17, 0x40]
private def zeroBit : List UInt8 := [0x05, 0x01, 0x45, 0x3f, 0x85, 0x1f]

#guard read 5 2 (onFirst ++ [0, 0xff]) = .ok ⟨[0, 1], 5, [0, 0xff]⟩
#guard read 5 3 onSecond = .ok ⟨[0, 1, 0], 5, []⟩
#guard read 6 2 shortField = .ok ⟨[0, 1], 6, []⟩
#guard read 6 3 zeroBit = .ok ⟨[2, 1, 0], 6, []⟩

#guard read 6 1 shortField = .error .weightLimit
#guard read 5 2 onSecond = .error .weightLimit
#guard read 5 0 onFirst = .error .weightLimit
#guard read 4 2 onFirst = .error (.description .byteLimit)
#guard read 5 2 (onFirst.take 4) = .error (.description .truncated)
#guard read 4 2 [0x03, 0x10, 0x3f, 0x00] = .error (.description .badEndMarker)
#guard read 4 2 [0x03, 0x10, 0x3f, 0x20] = .error (.description .truncatedStates)

end Silmaril.Formats.Compression.Zstd.Huffman.FseWeights
