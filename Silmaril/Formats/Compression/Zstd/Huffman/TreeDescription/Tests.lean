module

import Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription.Defs
meta import Batteries.Data.Except

namespace Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription

private def caps : Limits := ⟨128, ⟨256, 11⟩⟩
private def directWire : List UInt8 := [0x80, 0x10]
private def fseWire : List UInt8 := [0x04, 0x10, 0x3f, 0x03, 0x04]
private def zeroMassWire : List UInt8 := [0x04, 0x10, 0x3f, 0x02, 0x04]
private def nonPowerWire : List UInt8 := [0x06, 0x10, 0x88, 0xc1, 0x07, 0x60, 0x04]
private def invalidRankWire : List UInt8 := [0x05, 0x01, 0x45, 0x3f, 0xcc, 0x12]
private def tail : List UInt8 := [0, 0xff]

#guard readTable caps (directWire ++ tail) =
  .ok (⟨.direct, ⟨1, [1, 1]⟩, 2, tail⟩, ⟨1, [⟨0, 1, 0⟩, ⟨1, 1, 1⟩]⟩)
#guard readTable caps (fseWire ++ tail) =
  .ok (⟨.fse, ⟨1, [0, 1, 1]⟩, 5, tail⟩, ⟨1, [⟨1, 1, 0⟩, ⟨2, 1, 1⟩]⟩)

#guard read caps [] = .error .truncated
#guard read caps [0] = .error (.fse (.description .emptyDescription))
#guard read ⟨1, caps.tree⟩ directWire = .error (.direct .byteLimit)
#guard read ⟨4, caps.tree⟩ fseWire = .error (.fse (.description .byteLimit))
#guard read ⟨128, ⟨1, 11⟩⟩ directWire = .error (.direct .symbolLimit)
#guard read ⟨128, ⟨2, 11⟩⟩ fseWire = .error (.fse .weightLimit)

#guard FseWeights.read 128 255 (zeroMassWire ++ tail) = .ok ⟨[0, 0], 5, tail⟩
#guard FseWeights.read 128 255 (nonPowerWire ++ tail) = .ok ⟨[3, 1], 7, tail⟩
#guard FseWeights.read 128 255 (invalidRankWire ++ tail) = .ok ⟨[2, 2], 6, tail⟩

#guard readTable caps (zeroMassWire ++ tail) = .error (.completion .zeroMass)
#guard readTable caps (nonPowerWire ++ tail) = .error (.completion .nonPowerRemainder)
#guard readTable caps (invalidRankWire ++ tail) = .error (.completion .invalidDeepestRank)

end Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription
