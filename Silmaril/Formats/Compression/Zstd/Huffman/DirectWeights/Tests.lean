module

import Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd.Huffman
open DirectWeights (Limits)

private def limits : Limits := ⟨65, 129, 11⟩

-- RFC 8878 example, including arbitrary padding in the spare low nibble.
#guard DirectWeights.read limits [0x84, 0x43, 0x20, 0x1f, 0xa5, 0, 0xff] =
  .ok ⟨⟨4, [4, 3, 2, 0, 1, 1]⟩, 4, [0xa5, 0, 0xff]⟩
#guard DirectWeights.read limits [130, 0x31, 0x10, 7] =
  .ok ⟨⟨3, [3, 1, 1, 2]⟩, 3, [7]⟩
#guard DirectWeights.read limits ([255] ++ List.replicate 63 0 ++ [1, 99]) =
  .ok ⟨⟨1, List.replicate 127 0 ++ [1, 1]⟩, 65, [99]⟩
#guard DirectWeights.read limits [138, 0xba, 0x98, 0x76, 0x54, 0x32, 0x1f] =
  .ok ⟨⟨11, [11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 1]⟩, 7, []⟩

#guard DirectWeights.read limits [] = .error .truncated
#guard DirectWeights.read limits [132, 0x43, 0x20] = .error .truncated
#guard DirectWeights.read limits [4, 0, 1, 2, 3] = .error (.unsupportedFse 4)
#guard DirectWeights.read limits [128, 0x0f] = .error .zeroMass
#guard DirectWeights.read limits [129, 0x31] = .error .nonPowerRemainder
#guard DirectWeights.read limits [128, 0x20] = .error .invalidDeepestRank
#guard DirectWeights.read {limits with depth := 12} [139, 0xcb, 0xa9, 0x87, 0x65, 0x43, 0x21] =
  .error .depthLimit
#guard DirectWeights.read {limits with bytes := 1} [128, 0x10] = .error .byteLimit
#guard DirectWeights.read {limits with symbols := 1} [128, 0x10] = .error .symbolLimit
#guard DirectWeights.read {limits with depth := 3} [132, 0x43, 0x20, 0x10] = .error .depthLimit
