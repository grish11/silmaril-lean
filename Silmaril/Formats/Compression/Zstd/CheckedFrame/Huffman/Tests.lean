module

import Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd (magic rawFrame contentChecksum)
open Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman

private def limits : Limits := ⟨⟨256, 64, 1024⟩, 1, ⟨128, ⟨256, 11⟩⟩⟩

private def frame (blocks : List UInt8) : List UInt8 := magic ++ [0, 0] ++ blocks

-- Install mixed sequence tables, interpose a physical RLE block, then reuse all three tables.
private def blocks : List UInt8 :=
  [0x64, 0, 0, 0x20, 97, 98, 99, 100, 1, 0x18, 2, 0x10, 0x3f, 3, 0x22,
   0x12, 0, 0, 33,
   0x4d, 0, 0, 0x20, 119, 120, 121, 122, 1, 0xfc, 3, 0x22]

private def expected : List UInt8 := [97, 98, 99, 100, 97, 98, 99, 33, 33, 119, 120, 121, 122, 119, 120, 121]
private def checksummed := magic ++ [4, 0] ++ blocks ++ contentChecksum expected

#guard decode limits (frame blocks) = .ok expected
#guard decode {limits with frame := ⟨checksummed.length, expected.length, 1024⟩} checksummed = .ok expected
#guard decode {limits with frame := ⟨256, 0, 1024⟩} (rawFrame []) = .ok []
#guard decode limits (checksummed ++ [0]) = .error (.frame .trailingInput)
#guard decode limits (checksummed ++ checksummed) = .error (.frame .trailingInput)
#guard decode limits (frame [0x2d, 0, 0, 3, 0x40, 0, 1, 0]) = .error (.compressed (.literals .unavailableTable))
#guard decode limits (frame [0x2d, 0, 0, 0, 1, 0xfc, 1, 0]) =
  .error (.compressed (.block (.tables (.missingTable .literalLength))))
#guard decode limits (frame [0x13, 0, 0]) = .error (.frame .truncated)
#guard decode limits (frame [7, 0, 0]) = .error (.frame .reservedBlock)
#guard decode limits [0x50, 0x2a, 0x4d, 0x18, 0, 0, 0, 0] = .error .skippableFrame
