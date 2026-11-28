module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ColumnIndex.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ColumnIndex.Defs

/-! Independent full-file wire observations and typed malformed controls. -/

namespace Silmaril.Formats.Parquet.ColumnIndex

private def fixture : Bytes := ⟨include_bytes "../../../../data/parquet-column-index/column-index.parquet"⟩
private def noIndex : Bytes := ⟨include_bytes "../../../../data/parquet-offset-index/v1-no-index.parquet"⟩

private structure Observation where
  span : Footer.Span
  frameOffsets : List Nat
  nullPages : List Bool
  minValues : List (List UInt8)
  maxValues : List (List UInt8)
  order : BoundaryOrder
  counts : Option (List Int)
  deriving DecidableEq

private def observed (source : Bytes) (group : Nat) : Except Error (Option Observation) :=
  (readFile {} source group 0).map (Option.map fun index =>
    ⟨index.span, index.pages.map (fun (entry, _) => entry.frame.header.start), index.raw.nullPages,
      index.raw.minValues.map Bytes.toList, index.raw.maxValues.map Bytes.toList,
      index.raw.order, index.raw.nullCounts⟩)

-- The first and last non-null pages overlap in both ordered groups.
#guard observed fixture 0 = .ok (some
  ⟨⟨291, 338⟩, [4, 39, 62], [false, true, false],
    [[0, 0, 0, 0x80], [], [0, 0, 0, 0]], [[3, 0, 0, 0], [], [0xff, 0xff, 0xff, 0x7f]],
    .ascending, some [1, 4, 1]⟩)
#guard observed fixture 1 = .ok (some
  ⟨⟨338, 385⟩, [97, 132, 155], [false, true, false],
    [[5, 0, 0, 0], [], [0, 0, 0, 0x80]], [[12, 0, 0, 0], [], [8, 0, 0, 0]],
    .descending, some [1, 4, 1]⟩)
#guard observed fixture 2 = .ok (some
  ⟨⟨385, 440⟩, [190, 221, 256], [false, false, false],
    [[0xfb, 0xff, 0xff, 0xff], [8, 0, 0, 0], [0xee, 0xff, 0xff, 0xff]],
    [[0, 0, 0, 0], [12, 0, 0, 0], [5, 0, 0, 0]], .unordered, some [2, 1, 1]⟩)
#guard observed noIndex 0 = .ok none

private def change (source : Bytes) (offset : Nat) (byte : UInt8) : Bytes :=
  ⟨source.data.set! offset byte⟩

-- Group 0's order, all-null flag, and signed counts.
#guard observed (change fixture 323 14) 0 = .error (.boundaryOrder 7)
#guard observed (change fixture 294 2) 0 = .error .boundWidth
#guard observed (change fixture 327 6) 0 = .error .nullCount
#guard observed (change fixture 326 1) 0 = .error .nullCount

-- The footer advertises a different slice width.
#guard observed (change fixture 641 92) 0 = .error (.compact (.compact .truncated))
#guard observed (change fixture 641 96) 0 = .error .trailingBytes
#guard observed (change (change fixture 638 0xf0) 639 6) 0 = .error .overlapsOffsetIndex
#guard observed (change (change fixture 638 0x80) 639 1) 0 = .error .overlapsChunk
#guard observed (change fixture 443 10) 0 = .error (.offsetIndex (.pageOffset 0 5 4))

-- Remove the OffsetIndex reference pair and adjust the ColumnIndex delta.
private def missingOffsets : Bytes :=
  (Footer.fileBytes fixture 0 632).append <|
    (Bytes.ofList [0x36]).append <|
      (Footer.fileBytes fixture 638 1106).append (Bytes.ofList [0x47, 2, 0, 0, 0x50, 0x41, 0x52, 0x31])

#guard observed missingOffsets 0 = .error .missingOffsetIndex

-- Remove the ColumnIndex length field, keeping the footer length exact.
private def partialColumn : Bytes :=
  (Footer.fileBytes fixture 0 640).append <|
    (Footer.fileBytes fixture 642 1106).append (Bytes.ofList [0x4a, 2, 0, 0, 0x50, 0x41, 0x52, 0x31])

#guard observed partialColumn 0 = .error (.snapshot (.invalidMetadata .indexInterval))
#guard readFile { maxIndexBytes := 46 } fixture 0 0 = .error .indexByteLimit
#guard readFile { maxEntries := 2 } fixture 0 0 = .error (.compact (.compact .lengthLimit))

private def checkedShape (bytes : Bytes) : Except Error (Option (List Int)) := do
  let some offsets ← (OffsetIndex.readFile {} fixture 0 0).mapError Error.offsetIndex | throw .missingOffsetIndex
  let raw ← readExact {} bytes
  let _ ← checkShape raw offsets.pages
  pure raw.nullCounts

-- Thrift structs with an omitted count vector or a well-typed short vector.
private def noCounts : Bytes := (Footer.fileBytes fixture 291 324).push 0
private def shortCounts : Bytes :=
  (Footer.fileBytes fixture 291 325).append (Bytes.ofList [0x26, 8, 2, 0])

private def shortBound : Bytes :=
  (Footer.fileBytes fixture 291 298).append <|
    (Bytes.ofList [3, 0, 0, 0]).append (Footer.fileBytes fixture 303 338)

private def duplicateFlags : Bytes :=
  (Footer.fileBytes fixture 291 296).append <|
    (Bytes.ofList [9, 2, 1]).append (Footer.fileBytes fixture 296 338)

#guard checkedShape shortBound = .error .boundWidth
#guard readExact {} duplicateFlags = .error (.duplicateField 1)
#guard readExact {} (Bytes.ofList [0]) = .error (.missingField 1)
#guard observed (change fixture 322 0x16) 0 = .error (.fieldType 4 (.payload .i64))

#guard checkedShape noCounts = .ok none
#guard checkedShape shortCounts = .error (.entryCount 5 3 2)
#guard (readFile {} (change (change fixture 326 0) 328 0) 0 0).map
    (Option.map (fun index => index.raw.nullCounts)) = .ok (some (some [0, 4, 0]))

end Silmaril.Formats.Parquet.ColumnIndex
