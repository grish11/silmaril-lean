module

import Silmaril.Formats.Compression.Zstd.SequenceTables.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.SequenceTables.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd.SequenceTables

private def limits : Limits := ⟨12, 128⟩

private def describe : Table → Nat × Nat
  | .rle symbol => (0, symbol)
  | .fse table => (table.log, table.rows.length)

#guard resolve limits [0] = .ok .empty
#guard resolve limits [128, 0] = .ok .empty
#guard (resolve limits [128, 128, 0, 1]).map Section.count = .ok 128
#guard (resolve ⟨5, 98047⟩ [255, 255, 255, 0, 1]).map Section.count = .ok 98047

-- Predefined literal lengths, RLE offsets, transmitted match lengths.
-- libzstd writes the [16, 16] normalized weights as 10 3f.
#guard (resolve ⟨7, 1⟩ [1, 0x18, 2, 0x10, 0x3f, 0xa5, 0xff]).map
  (fun result => match result with
    | .empty => (0, [], [])
    | .coded count tables stream => (count,
        [describe tables.literalLength, describe tables.offset, describe tables.matchLength], stream)) =
  .ok (1, [(6, 64), (0, 2), (5, 32)], [0xa5, 0xff])
#guard resolve limits [1, 0x54, 35, 31, 52, 1] =
  .ok (.coded 1 ⟨.rle 35, .rle 31, .rle 52⟩ [1])

#guard resolve limits [255, 0] = .error (.count .truncated)
#guard resolve limits [0, 0] = .error .trailingEmptySection
#guard resolve limits [1] = .error .missingModes
#guard resolve limits [1, 1, 1] = .error .reservedBits
#guard resolve limits [1, 0x40] = .error (.missingRleSymbol .literalLength)
#guard resolve limits [1, 0x40, 36, 1] = .error (.invalidRleSymbol .literalLength)
#guard resolve limits [1, 0x10, 32, 1] = .error (.invalidRleSymbol .offset)
#guard resolve limits [1, 0x04, 53, 1] = .error (.invalidRleSymbol .matchLength)
#guard resolve limits [1, 0x80, 0xf0] = .error (.transmitted .literalLength .truncated)
#guard resolve limits [1, 0x20, 4, 1] = .error (.transmitted .offset .accuracyLog)
#guard resolve limits [1, 0x0c, 1] = .error (.unsupportedMode .matchLength 3)
#guard resolve limits [1, 0] = .error .missingBitstream
#guard resolve ⟨2, 1⟩ [1, 0, 1] = .error .inputLimit
#guard resolve ⟨3, 0⟩ [1, 0, 1] = .error .sequenceLimit
