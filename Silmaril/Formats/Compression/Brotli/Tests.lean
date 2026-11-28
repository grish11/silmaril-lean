module

import Silmaril.Formats.Compression.Brotli.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Brotli.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Brotli

private def limits : Limits := ⟨16, 16, windowSize 24, 4⟩
private def twoRaw : List UInt8 := [0, 0, 0x10, 97, 0, 0, 8, 98, 3]

#guard decode ⟨1, 0, windowSize 18, 1⟩ [0x33] = .ok []
#guard decode ⟨twoRaw.length, 2, windowSize 16, 3⟩ twoRaw = .ok [97, 98]
#guard decode {limits with steps := 2} twoRaw = .error .stepLimit
#guard decode {limits with steps := 0} [0x33] = .error .stepLimit
#guard decode {limits with input := twoRaw.length - 1} twoRaw = .error .inputLimit
#guard decode {limits with output := 1} twoRaw = .error .outputLimit
#guard decode {limits with window := windowSize 16 - 1} twoRaw = .error .windowLimit

#guard decode limits [] = .error .truncated
#guard decode limits [0] = .error .truncated
#guard decode limits [0, 0, 0x10] = .error .truncated
#guard decode limits twoRaw.dropLast = .error .truncated
#guard decode limits [0x11] = .error .reservedWindow
#guard decode limits [0x1c] = .error .reservedMetadata
#guard decode limits [0x0c] = .error .unsupportedMetadata
#guard decode limits [0x04, 0, 0] = .error .noncanonicalLength
#guard decode limits [0, 0, 0] = .error .unsupportedCompressed
#guard decode limits [0, 0, 0x30, 97, 3] = .error .nonzeroPadding
#guard decode limits [0x73] = .error .nonzeroPadding
#guard decode limits (twoRaw ++ [0]) = .error .trailingInput
