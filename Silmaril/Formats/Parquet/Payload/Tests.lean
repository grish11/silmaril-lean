module

import Silmaril.Formats.Parquet.Payload.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Parquet.Payload.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Parquet.Payload

/-! Byte vectors extracted by the pinned PyArrow V1 page oracle. -/

private def plain : List UInt8 :=
  (List.replicate 16 [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255]).flatten

private def snappy : List UInt8 :=
  [0x80, 0x02, 0x10, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01, 0x05, 0x18, 0x00,
   0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0x01, 0x08, 0xfe, 0x10, 0x00, 0xfe,
   0x10, 0x00, 0xfe, 0x10, 0x00, 0xae, 0x10, 0x00]

private def gzip : List UInt8 :=
  [0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x03, 0x63, 0x60,
   0x60, 0x60, 0x60, 0x64, 0x80, 0x80, 0xff, 0x40, 0xc0, 0x30, 0xc2, 0xf8,
   0x00, 0x6a, 0x85, 0xfc, 0x10, 0x00, 0x01, 0x00, 0x00]

private def lz4 : List UInt8 :=
  [0x50, 0x00, 0x00, 0x00, 0x00, 0x01, 0x05, 0x00, 0x70, 0x00, 0x00, 0x00,
   0xff, 0xff, 0xff, 0xff, 0x09, 0x00, 0x0f, 0x10, 0x00, 0xd4, 0x50, 0x00,
   0xff, 0xff, 0xff, 0xff]

private def page (id : Int) (input : List UInt8) (expected : Nat := 256) :
    Except Error (List UInt8) :=
  decode ⟨input.length, input.length, expected, expected, 512⟩ id input

#guard page 0 plain = .ok plain
#guard page 1 snappy = .ok plain
#guard page 2 gzip = .ok plain
#guard page 7 lz4 = .ok plain

-- The declared codec selects the interpretation.
#guard page 0 snappy = .error .outputSizeMismatch
#guard page 5 lz4 = .error (.unsupportedCodec 5)
#guard page (-1) plain = .error (.unsupportedCodec (-1))
#guard page 2 snappy = .error (.malformed .gzip)
#guard page 1 (snappy.take (snappy.length - 1)) = .error (.malformed .snappy)
#guard page 1 (snappy ++ [0]) = .error (.trailingInput .snappy)
#guard page 7 (lz4 ++ [0]) = .error (.malformed .lz4Raw)
#guard page 2 (gzip ++ [0]) = .error (.trailingInput .gzip)
#guard page 2 (gzip ++ gzip) = .error (.trailingInput .gzip)
#guard page 2 (gzip.set (gzip.length - 8) 0) = .error (.malformed .gzip)
#guard page 2 (gzip.set (gzip.length - 1) 1) = .error (.malformed .gzip)

-- Exact size is separate from the caller caps.
#guard page 1 snappy 255 = .error .outputSizeMismatch
#guard page 1 snappy 257 = .error .outputSizeMismatch
#guard page 7 lz4 255 = .error .outputSizeMismatch
#guard page 2 gzip 32 = .error .outputSizeMismatch
#guard page 2 gzip 257 = .error .outputSizeMismatch
#guard decode ⟨33, 32, 256, 256, 512⟩ 2 gzip = .error .compressedLimit
#guard decode ⟨33, 33, 256, 255, 512⟩ 2 gzip = .error .outputLimit
#guard decode ⟨32, 33, 256, 256, 512⟩ 2 gzip = .error .compressedSizeMismatch
#guard decode ⟨34, 34, 256, 256, 512⟩ 2 gzip = .error .compressedSizeMismatch
#guard decode ⟨33, 33, 256, 256, 0⟩ 2 gzip = .error .gzipIncomplete
#guard decode ⟨32, 32, 256, 256, 64⟩ 2 (gzip.take 32) = .error .gzipIncomplete

example : decode ⟨1, 0, 0, 0, 0⟩ 2 [] = .error .compressedLimit := rfl
example : decode ⟨0, 0, 1, 0, 0⟩ 2 [] = .error .outputLimit := rfl
example : decode ⟨0, 0, 0, 0, 0⟩ 5 [] = .error (.unsupportedCodec 5) := rfl
