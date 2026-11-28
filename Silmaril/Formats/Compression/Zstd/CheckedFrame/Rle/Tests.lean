module

import Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd (magic rawFrame)
open Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle

private def limits : Limits := ⟨⟨256, 16, 1024⟩, 4⟩

private def frame (blocks : List UInt8) : List UInt8 := magic ++ [0, 0] ++ blocks

-- Four raw bytes, then a zero-literal repeat code 1 (initial second offset 4).
private def repeats : List UInt8 :=
  frame [32, 0, 0, 97, 98, 99, 100, 69, 0, 0, 8, 33, 1, 84, 0, 0, 0, 1]

#guard decode limits repeats = .ok [97, 98, 99, 100, 97, 98, 99, 33]
#guard decode ⟨⟨repeats.length, 8, 1024⟩, 1⟩ repeats =
  .ok [97, 98, 99, 100, 97, 98, 99, 33]
#guard decode ⟨⟨repeats.length, 7, 1024⟩, 1⟩ repeats = .error (.execution .outputLimit)
#guard decode ⟨⟨repeats.length, 8, 1024⟩, 0⟩ repeats = .error (.sequences .commandLimit)
#guard decode ⟨⟨repeats.length - 1, 8, 1024⟩, 1⟩ repeats = .error (.frame .inputLimit)
#guard decode ⟨⟨repeats.length, 8, 1023⟩, 1⟩ repeats = .error (.frame .windowLimit)
#guard decode limits (repeats.take (repeats.length - 1)) = .error (.frame .truncated)
#guard decode limits (repeats ++ [0]) = .error (.frame .trailingInput)

#guard decode limits (frame [29, 0, 0, 17, 97, 0]) = .ok [97, 97]
#guard decode limits (frame [13, 0, 0, 2]) = .error (.literals (.unsupported .huffmanLiterals))
#guard decode limits (frame [13, 0, 0, 3]) = .error (.literals (.unsupported .treelessLiterals))
#guard decode limits (frame [29, 0, 0, 0, 1, 0]) = .error (.sequences (.unsupportedModes 0))
#guard decode limits (frame [29, 0, 0, 0, 1, 252]) = .error (.sequences (.unsupportedModes 252))
#guard decode limits (frame [29, 0, 0, 0, 1, 85]) = .error (.sequences .reservedModeBits)

#guard decode limits (rawFrame [97, 98]) = .ok [97, 98]
#guard decode limits (magic ++ [0x21, 7, 1, 9, 0, 0, 97]) =
  .error (.frame (.unsupportedDictionary 7))

#guard (History.initial.advance 3 [1, 2, 3, 4, 5] ⟨4, 1, 8⟩).recent = #[3, 4, 5]
#guard ((History.initial.advance 3 [1, 2, 3, 4, 5] ⟨4, 1, 8⟩).advance 3 [6] ⟨3, 4, 1⟩).recent =
  #[4, 5, 6]
