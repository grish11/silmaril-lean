module

import Silmaril.Formats.Compression.Snappy.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Snappy.Defs
meta import Batteries.Data.Except

/-! Regression vectors for Parquet's raw Snappy payload. -/

open Silmaril.Formats.Compression.Snappy

-- Pinned Snappy 1.2.2 output on the empty input, on 70 'a' bytes, and on bytes 0 to 79.
#guard decode 0 [0] = .ok []
#guard decode 70 [0x46, 0, 0x61, 0xfe, 1, 0, 5, 1] = .ok (List.replicate 70 0x61)
private def sequence80 : List UInt8 := (List.range 80).map UInt8.ofNat
#guard decode 80 ([0x50, 0xf0, 0x4f] ++ sequence80) = .ok sequence80
#guard encode sequence80 = .ok ([0x50, 0xf0, 0x4f] ++ sequence80)
#guard encode [] = .ok [0]
#guard Internal.writeLength 5 maxLength = [0xff, 0xff, 0xff, 0xff, 0x0f]
#guard Internal.writeLiteralHead 16777216 = [0xfc, 0, 0, 0, 1]

-- Copy-4 overlaps on offset two. Copy-1 uses high offset bits as well as the trailing byte.
#guard parse 8 [8, 4, 0x61, 0x62, 0x17, 2, 0, 0, 0] =
  .ok ⟨8, [.literal [0x61, 0x62], .copy 2 6]⟩
#guard decode 8 [8, 4, 0x61, 0x62, 0x17, 2, 0, 0, 0] =
  .ok [0x61, 0x62, 0x61, 0x62, 0x61, 0x62, 0x61, 0x62]
private def sequence256 : List UInt8 := (List.range 256).map UInt8.ofNat
#guard decode 260 ([0x84, 2, 0xf0, 0xff] ++ sequence256 ++ [0x21, 0]) =
  .ok (sequence256 ++ [0, 1, 2, 3])
#guard decode 260 ([0x84, 2, 0xf0, 0xff] ++ sequence256 ++ [0x0e, 0, 1]) =
  .ok (sequence256 ++ [0, 1, 2, 3])

-- Accept non-minimal length fields that the reference reader accepts.
#guard decode 0 [0x80, 0] = .ok []
#guard decode 1 [1, 0xfc, 0, 0, 0, 0, 42] = .ok [42]
#guard decode 1 [1, 0xf8, 0, 0, 0, 42] = .ok [42]
#guard decode 1 [1, 0xf4, 0, 0, 42] = .ok [42]

-- Malformed preambles, short fields, invalid distances and size mismatches.
#guard decode 100 [] = .error (.malformed .preamble)
#guard decode 100 [0x80] = .error (.malformed .preamble)
#guard decode 100 [0x80, 0x80, 0x80, 0x80, 0x10] = .error (.malformed .preamble)
#guard decode 100 [0x80, 0x80, 0x80, 0x80, 0x80, 0] = .error (.malformed .preamble)
#guard decode 100 [1] = .error (.malformed .truncatedTag)
#guard decode 100 [1, 0] = .error (.malformed .truncatedTag)
#guard decode 100 [4, 0xf4, 0] = .error (.malformed .truncatedTag)
#guard decode 100 [4, 0x0e, 1] = .error (.malformed .truncatedTag)
#guard decode 100 [1, 2, 1, 0] = .error (.malformed .invalidOffset)
#guard decode 100 [2, 0, 42, 2, 0, 0] = .error (.malformed .invalidOffset)
#guard decode 100 [1, 4, 42, 43] = .error (.malformed .lengthMismatch)
#guard decode 100 [2, 0, 42, 1, 1] = .error (.malformed .lengthMismatch)
#guard decode 100 [2, 0, 42] = .error (.malformed .truncatedTag)
#guard decode 100 [1, 0xfc, 0xff, 0xff, 0xff, 0xff] = .error (.malformed .lengthMismatch)
#guard decode 100 [1, 0, 42, 0] = .error (.malformed .trailingInput)
#guard decodeMember 100 [1, 0, 42, 0] = .ok ([42], [0])

-- A valid uint32 declared length is checked before the tag phase.
#guard decode 69 [70] = .error (.limited 70 69)
#guard decode 0 [0xff, 0xff, 0xff, 0xff, 0x0f] = .error (.limited 4294967295 0)
#guard decode 0 [0xff, 6, 0, 0, 0x73, 0x4e, 0x61, 0x50, 0x70, 0x59] =
  .error (.unsupported .framedStream)

example : decode 0 [0] = .ok [] := rfl
example : decode 0 [1] = .error (.limited 1 0) := rfl
example : decode 1 [1, 0, 42, 0] = .error (.malformed .trailingInput) := rfl
