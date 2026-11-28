module

import Silmaril.Formats.Compression.Zstd.RleSequences.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.RleSequences.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd
open Silmaril.Formats.Compression.Zstd.RleSequences

private def fields : Option (Nat × Nat × Bool) := do
  let cursor ← ReverseBits.start [0xa6, 0x0b]
  let (first, cursor) ← ReverseBits.read 6 cursor
  let (second, cursor) ← ReverseBits.read 5 cursor
  return (first, second, cursor.isEmpty)

#guard fields = some (29, 6, true)
#guard (ReverseBits.start [0x01]).map ReverseBits.Cursor.isEmpty = some true
#guard (ReverseBits.start [0xa6, 0x0b]).bind (ReverseBits.read 12) = none
#guard ReverseBits.start [] = none
#guard ReverseBits.start [1, 0] = none

private def limits : Limits := ⟨128, 8⟩

#guard decode limits [0] = .ok []
#guard decode limits [128, 0] = .ok []
#guard decode limits [0, 0] = .error .trailingInput
#guard decode limits [1, 0x54, 2, 2, 2, 5] = .ok [⟨2, 5, 5⟩]
#guard decode limits [1, 0x54, 18, 5, 38, 0x25, 0x02] = .ok [⟨21, 34, 53⟩]
#guard decode limits ([1, 0x54, 35, 31, 52] ++ List.replicate 8 255) =
  .ok [⟨131071, 4294967295, 131074⟩]
#guard decode limits [2, 0x54, 1, 0, 0, 1] = .ok [⟨1, 1, 3⟩, ⟨1, 1, 3⟩]
#guard decode limits [] = .error .truncated
#guard decode limits [255, 0] = .error .truncated
#guard decode limits [1, 0x54, 2, 2] = .error .truncated
#guard decode limits [1, 0x54, 2, 2, 2] = .error .badEndMarker
#guard decode limits [1, 0x54, 2, 2, 2, 0] = .error .badEndMarker
#guard decode limits [1, 0x54, 2, 2, 2, 1] = .error .bitUnderflow
#guard decode limits [1, 0x54, 2, 2, 2, 10] = .error .trailingBits
#guard decode limits [1, 0x55] = .error .reservedModeBits
#guard decode limits [1, 0] = .error (.unsupportedModes 0)
#guard decode limits [1, 0xa8] = .error (.unsupportedModes 0xa8)
#guard decode limits [1, 0xfc] = .error (.unsupportedModes 0xfc)
#guard decode limits [1, 0x50] = .error (.unsupportedModes 0x50)
#guard decode limits [1, 0x54, 36, 2, 2, 5] = .error .invalidLiteralCode
#guard decode limits [1, 0x54, 2, 32, 2, 5] = .error .invalidOffsetCode
#guard decode limits [1, 0x54, 2, 2, 53, 5] = .error .invalidMatchCode
#guard decode { limits with input := 5 } [1, 0x54, 2, 2, 2, 5] = .error .inputLimit
#guard decode { limits with commands := 1 } [2, 0x54, 1, 0, 0, 1] = .error .commandLimit
