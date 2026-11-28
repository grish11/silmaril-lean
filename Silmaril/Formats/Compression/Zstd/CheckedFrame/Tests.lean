module

import Silmaril.Formats.Compression.Zstd.CheckedFrame.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.CheckedFrame.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd (magic rawFrame)
open Silmaril.Formats.Compression.Zstd.CheckedFrame

private def limits : Limits := ⟨256, 16, 1024⟩

private def frame (blocks : List UInt8) : List UInt8 :=
  magic ++ [0, 0] ++ blocks

-- Raw "ab", two repetitions of "c", raw literals "de", RLE literals "ff".
private def mixed : List UInt8 :=
  frame ([16, 0, 0, 97, 98] ++ [18, 0, 0, 99] ++
    [36, 0, 0, 16, 100, 101, 0] ++ [29, 0, 0, 17, 102, 0])

#guard decode limits mixed = .ok [97, 98, 99, 99, 100, 101, 102, 102]
#guard decode { limits with output := 8 } mixed = .ok [97, 98, 99, 99, 100, 101, 102, 102]
#guard decode { limits with output := 7 } mixed = .error (.literalBlock .outputLimit)
#guard decode { limits with output := 3 } mixed = .error .outputLimit
#guard decode { limits with output := 1 } mixed = .error .outputLimit
#guard decode { limits with input := mixed.length } mixed = decode limits mixed
#guard decode { limits with input := mixed.length - 1 } mixed = .error .inputLimit
#guard decode { limits with window := 1023 } mixed = .error .windowLimit

#guard decode limits (frame [5, 0, 0]) = .error (.literalBlock .truncated)
#guard decode limits (frame [29, 0, 0, 17, 97]) = .error .truncated
#guard decode limits (frame [29, 0, 0, 17, 97, 0, 0]) = .error .trailingInput
#guard decode limits (frame [37, 0, 0, 17, 97, 0, 0]) = .error (.literalBlock .trailingSequences)
#guard decode limits (frame [32, 0, 0, 97, 98]) = .error .truncated
#guard decode limits (frame [8, 0, 0, 97]) = .error .truncated
#guard decode limits (frame [7, 0, 0]) = .error .reservedBlock
#guard decode limits (frame [11, 32, 0, 97]) = .error .blockLimit
#guard decode limits (frame [13, 32, 0]) = .error .blockLimit

#guard decode limits (frame [37, 0, 0, 2, 0, 0, 0]) = .error (.literalBlock (.unsupported .huffmanLiterals))
#guard decode limits (frame [37, 0, 0, 3, 0, 0, 0]) = .error (.literalBlock (.unsupported .treelessLiterals))
#guard decode limits (frame [37, 0, 0, 8, 97, 1, 0]) = .error (.literalBlock (.unsupported .sequences))
#guard decode limits (magic ++ [0x21, 7, 1, 9, 0, 0, 97]) = .error (.unsupportedDictionary 7)
#guard decode limits (magic ++ [0x28, 1, 9, 0, 0, 97]) = .error .badHeader
#guard decode limits (magic ++ [0x20, 2, 9, 0, 0, 97]) = .error .contentSizeMismatch
#guard decode limits (mixed ++ mixed) = .error .trailingInput

#guard decode limits (rawFrame [97]) = .ok [97]
#guard decode limits ((rawFrame [97]).take 12) = .error .truncated
#guard decode limits ((rawFrame [97]).take 13 ++ [0]) = .error .checksumMismatch
#guard decode limits (rawFrame [97] ++ [0]) = .error .trailingInput
#guard decode { limits with output := 0 } (rawFrame []) = .ok []

-- The two-byte content-size encoding adds 256 to the stored value.
#guard (decode ⟨32, 256, 1024⟩ (magic ++ [0x40, 0, 0, 0, 3, 8, 0, 97])).map List.length =
  .ok 256
#guard decode { limits with output := 2 } (frame [18, 0, 0, 97, 21, 0, 0, 0, 0]) =
  .ok [97, 97]
