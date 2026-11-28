module

import Silmaril.Formats.Compression.Zstd.CheckedFrame.Sequences.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.CheckedFrame.Sequences.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd (magic rawFrame contentChecksum)
open Silmaril.Formats.Compression.Zstd.CheckedFrame.Sequences

private def limits : Limits := ⟨⟨256, 64, 1024⟩, 4⟩

private def frame (blocks : List UInt8) : List UInt8 := magic ++ [0, 0] ++ blocks

private def sequenceBlocks : List UInt8 :=
  -- Fresh mixed tables, a plain raw block, and then reuse all three tables.
  [0x64, 0, 0, 0x20, 97, 98, 99, 100, 1, 0x18, 2, 0x10, 0x3f, 3, 0x22,
   8, 0, 0, 33,
   0x4d, 0, 0, 0x20, 119, 120, 121, 122, 1, 0xfc, 3, 0x22]

private def expected : List UInt8 := [97, 98, 99, 100, 97, 98, 99, 33, 119, 120, 121, 122, 119, 120, 121]
private def checksummed := magic ++ [4, 0] ++ sequenceBlocks ++ contentChecksum expected

#guard decode limits (frame sequenceBlocks) = .ok expected
#guard decode limits checksummed = .ok expected
#guard decode ⟨⟨checksummed.length, expected.length, 1024⟩, 1⟩ checksummed = .ok expected
#guard decode limits (checksummed ++ [0]) = .error (.frame .trailingInput)
#guard decode limits (checksummed.take (checksummed.length - 1)) = .error (.frame .truncated)
#guard decode limits (magic ++ [4, 0] ++ sequenceBlocks ++ [0, 0, 0, 0]) =
  .error (.frame .checksumMismatch)
#guard decode ⟨⟨256, 14, 1024⟩, 4⟩ (frame sequenceBlocks) = .error (.compressed (.execution .outputLimit))
#guard decode ⟨⟨256, 64, 1024⟩, 0⟩ (frame sequenceBlocks) =
  .error (.compressed (.tables (.prefix .sequenceLimit)))
#guard decode ⟨⟨256, 64, 1023⟩, 4⟩ (frame sequenceBlocks) = .error (.frame .windowLimit)
#guard decode ⟨⟨12, 64, 1024⟩, 4⟩ (frame sequenceBlocks) = .error (.frame .inputLimit)
#guard decode limits (frame (sequenceBlocks.take (sequenceBlocks.length - 1))) = .error (.frame .truncated)

#guard decode limits (rawFrame [97, 98]) = .ok [97, 98]
#guard decode ⟨⟨256, 0, 1024⟩, 0⟩ (rawFrame []) = .ok []
#guard decode limits (frame [27, 0, 0, 97]) = .ok [97, 97, 97]
#guard decode limits (frame [29, 0, 0, 17, 97, 0]) = .ok [97, 97]
#guard decode limits (magic ++ [0x20, 2, 9, 0, 0, 97]) = .error (.frame .contentSizeMismatch)
#guard decode limits (frame [13, 0, 0, 2]) = .error (.compressed (.literals (.unsupported .huffmanLiterals)))
#guard decode limits (frame [13, 0, 0, 3]) = .error (.compressed (.literals (.unsupported .treelessLiterals)))
#guard decode limits (frame [37, 0, 0, 0, 1, 0xfc, 1]) = .error (.compressed (.tables (.missingTable .literalLength)))
#guard decode limits (frame [7, 0, 0]) = .error (.frame .reservedBlock)
#guard decode limits (magic ++ [0x21, 7, 1, 9, 0, 0, 97]) = .error (.frame (.unsupportedDictionary 7))
#guard decode limits [0x50, 0x2a, 0x4d, 0x18, 0, 0, 0, 0] = .error .skippableFrame
