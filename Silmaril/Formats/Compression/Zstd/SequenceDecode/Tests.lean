module

import Silmaril.Formats.Compression.Zstd.SequenceDecode.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.SequenceDecode.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd.SequenceDecode

private def limits : Silmaril.Formats.Compression.Zstd.SequenceTables.Limits := ⟨32, 2⟩

-- Pinned libzstd fixtures. Each FSE table consumes a state transition field.
#guard decode limits [2, 0x18, 3, 0x10, 0xfe, 0xff, 0xbf, 0xf8, 1, 0x6a, 0xa8, 1, 0x0c] =
  .ok [⟨17, 13, 35⟩, ⟨18, 10, 38⟩]
#guard decode limits [2, 0x84, 0x10, 0xfe, 0x27, 0x7e, 0x20, 0xea, 0xd6, 0x12, 2] =
  .ok [⟨17, 13, 35⟩, ⟨18, 6, 36⟩]
#guard decode limits [2, 0x60, 0x10, 0x10, 0x8a, 0x1f, 0xea, 0xa9, 0xe4, 8] =
  .ok [⟨17, 13, 35⟩, ⟨16, 6, 38⟩]

private def fsePrefix : List UInt8 := [2, 0x28, 0x10, 0x8a, 0x1f, 0x10, 0xfe, 0xff, 0xbf, 0xf8, 1]
private def payload : List UInt8 := [0x6a, 0xa8, 0x61, 0x80, 1]

#guard decode limits (fsePrefix ++ payload) = .ok [⟨17, 13, 35⟩, ⟨18, 6, 38⟩]
#guard decode limits (fsePrefix ++ [0x35, 0xd4, 0x30, 0xc0]) = .error .bitUnderflow
#guard decode limits (fsePrefix ++ [0xd4, 0x50, 0xc3, 0, 3]) = .error .trailingBits
#guard decode limits (fsePrefix ++ [0]) = .error .badEndMarker
#guard decode limits (fsePrefix ++ [1]) = .error .bitUnderflow
#guard decode limits fsePrefix = .error (.prefix .missingBitstream)
#guard decode ⟨15, 2⟩ (fsePrefix ++ payload) = .error (.prefix .inputLimit)
#guard decode ⟨16, 1⟩ (fsePrefix ++ payload) = .error (.prefix .sequenceLimit)

-- All RLE states require zero bits. Offset_Value 1 remains a raw repeat code.
#guard decode limits [2, 0x54, 0, 0, 0, 1] = .ok [⟨0, 1, 3⟩, ⟨0, 1, 3⟩]
#guard decode limits [2, 0x54, 0, 0, 0, 3] = .error .trailingBits
#guard decode limits [0] = .ok []
#guard decode limits [0, 1] = .error (.prefix .trailingEmptySection)
#guard decode limits [1, 0x0c, 1] = .error (.prefix (.unsupportedMode .matchLength 3))
