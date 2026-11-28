module

import Silmaril.Formats.Compression.Lz4Raw.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Lz4Raw.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Lz4Raw

private def raw (expected : Nat) (bytes : List UInt8) : Except Error (List UInt8) :=
  decode ⟨bytes.length, bytes.length, expected, expected⟩ bytes

private def tailFive : List UInt8 := [98, 99, 100, 101, 102]
private def restart : List UInt8 := [0x50] ++ tailFive

-- Canonical empty block, the small literal exception, and an unused final low nibble.
#guard raw 0 [0] = .ok []
#guard raw 0 [] = .error .truncated
#guard raw 0 [1] = .error .invalidTail
#guard raw 1 [0x1f, 97] = .ok [97]
#guard raw 4 [0x40, 1, 2, 3, 4] = .ok [1, 2, 3, 4]

-- At the exact tail boundary, offset 1 overlaps seven output bytes.
#guard raw 13 ([0x13, 97, 1, 0] ++ restart) = .ok (List.replicate 8 97 ++ tailFive)
#guard raw 17 ([0x10, 97, 1, 0, 0x03, 1, 0] ++ restart) =
  .ok (List.replicate 12 97 ++ tailFive)
#guard raw 13 ([0x13, 97, 0, 0] ++ restart) = .error .invalidOffset
#guard raw 13 ([0x13, 97, 2, 0] ++ restart) = .error .invalidOffset

-- Each tail requirement can fail independently.
#guard raw 12 ([0x12, 97, 1, 0] ++ restart) = .error .invalidTail
#guard raw 13 [0x14, 97, 1, 0, 0x40, 98, 99, 100, 101] = .error .invalidTail
#guard raw 8 [0x13, 97, 1, 0] = .error .truncated
#guard raw 8 [0x13, 97, 1, 0, 0] = .error .invalidTail

-- Both extension fields require a terminating byte, including a zero at exact multiples.
#guard encodeLiteral (List.replicate 15 97) = [0xf0, 0] ++ List.replicate 15 97
#guard encodeLiteral (List.replicate 525 97) = [0xf0, 255, 255, 0] ++ List.replicate 525 97
#guard raw 525 ([0xf0, 255, 255, 0] ++ List.replicate 525 97) = .ok (List.replicate 525 97)
#guard raw 25 ([0x1f, 97, 1, 0, 0] ++ restart) = .ok (List.replicate 20 97 ++ tailFive)
#guard raw 280 ([0x1f, 97, 1, 0, 255, 0] ++ restart) = .ok (List.replicate 275 97 ++ tailFive)
#guard raw 300 [0xf0, 255] = .error .truncated
#guard raw 300 [0x1f, 97, 1, 0, 255] = .error .truncated
#guard raw 15 [0xf0, 255, 0] = .error .outputSizeMismatch
#guard raw 15 [0xf0, 0, 97] = .error .truncated
#guard raw 13 [0x13, 97, 1] = .error .truncated

-- Sizes are exact and each caller cap is checked independently.
#guard decode ⟨3, 2, 2, 2⟩ [0x20, 97, 98] = .error .compressedLimit
#guard decode ⟨3, 3, 2, 1⟩ [0x20, 97, 98] = .error .outputLimit
#guard decode ⟨2, 3, 2, 2⟩ [0x20, 97, 98] = .error .compressedSizeMismatch
#guard decode ⟨4, 4, 2, 2⟩ [0x20, 97, 98] = .error .compressedSizeMismatch
#guard raw 1 [0x20, 97, 98] = .error .outputSizeMismatch
#guard raw 3 [0x20, 97, 98] = .error .outputSizeMismatch
#guard raw 2 [0x20, 97, 98, 0] = .error .truncated
#guard raw 2 [0x20, 97, 98, 0, 0] = .error .outputSizeMismatch

example : parse ⟨1, 1, 0, 0⟩ [0] = .ok (.final []) := rfl
example : decode ⟨0, 0, 0, 0⟩ [0] = .error .compressedSizeMismatch := rfl
example : decode ⟨1, 1, 0, 0⟩ [1] = .error .invalidTail := rfl
