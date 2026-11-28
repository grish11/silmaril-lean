module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ColumnIndex.Signed.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ColumnIndex.Signed.Defs

/-! Independently produced Parquet files and shape-preserving semantic controls. -/

namespace Silmaril.Formats.Parquet.ColumnIndex.Signed

private def v1 : Bytes := ⟨include_bytes "../../../../../data/parquet-column-index/column-index.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../../data/parquet-column-index/column-index-v2.parquet"⟩
private def noIndex : Bytes := ⟨include_bytes "../../../../../data/parquet-offset-index/v1-no-index.parquet"⟩

private def bindInput (spelling : String) (source : Bytes) :
    Option (Σ snapshot : Snapshot.Checked, FlatColumn.Binding snapshot ⟨spelling, .int32, .optional⟩) := do
  let snapshot ← (Snapshot.check (Failure := Unit) {} source).toOption
  let binding ← (FlatColumn.bindColumn snapshot ⟨spelling, .int32, .optional⟩).toOption
  pure ⟨snapshot, binding⟩

private def observed (source : Bytes) (group : Nat) :
    Option (Slots × Except Error (Option (List (Option Bounds)))) := do
  let ⟨_, binding⟩ ← bindInput "number" source
  let result ← (read {} binding group).toOption
  pure (result.rows, result.index)

private def ascendingRows : Slots :=
  [some (-2147483648), none, some (-9), some 3, none, none, none, none,
    some 0, some 7, none, some 2147483647]

private def descendingRows : Slots :=
  [some 5, none, some 7, some 12, none, none, none, none,
    some (-2147483648), some (-18), none, some 8]

private def unorderedRows : Slots :=
  [none, some (-5), some 0, none, some 8, some 12, none, some 10,
    some (-18), none, some 5, some (-1)]

private def accepts (source : Bytes) : Bool :=
  observed source 0 == some (ascendingRows, .ok (some
    [some ⟨-2147483648, 3⟩, none, some ⟨0, 2147483647⟩])) &&
  observed source 1 == some (descendingRows, .ok (some
    [some ⟨5, 12⟩, none, some ⟨-2147483648, 8⟩])) &&
  observed source 2 == some (unorderedRows, .ok (some
    [some ⟨-5, 0⟩, some ⟨8, 12⟩, some ⟨-18, 5⟩]))

#guard accepts v1
#guard accepts v2
#guard ordered .ascending [-2147483648, -2147483648, 0, 2147483647]
#guard ordered .descending [2147483647, 0, 0, -2147483648]
#guard ordered .unordered [5, -1, 1, -5]

private def change (source : Bytes) (offset : Nat) (value : UInt8) : Bytes :=
  Bytes.ofList (source.toList.set offset value)

private def falseFlag : Bytes :=
  (Footer.fileBytes (change v1 294 2) 0 303).append <|
    (Bytes.ofList [4, 0, 0, 0, 0]).append <|
    (Footer.fileBytes v1 304 316).append <|
    (Bytes.ofList [4, 3, 0, 0, 0]).append <|
    (Footer.fileBytes (change v1 327 6) 317 329).append <|
    (Bytes.ofList [0]).append (Footer.fileBytes v1 338 v1.length)

private def absentCounts : Bytes := change (change v1 324 0) 641 68

-- The first upper bound need only contain the value; it can be loose.
#guard observed (change v1 312 4) 0 = some (ascendingRows, .ok (some
  [some ⟨-2147483648, 4⟩, none, some ⟨0, 2147483647⟩]))

-- These are well-shaped index claims with original page frames and exact extents.
#guard observed (change v1 312 2) 0 =
  some (ascendingRows, .error (.page 0 .containment))
#guard observed (change v1 326 0) 0 =
  some (ascendingRows, .error (.page 0 (.nullCount 0 1)))
#guard observed falseFlag 0 =
  some (ascendingRows, .error (.page 1 .allNull))
#guard observed (change v1 365 13) 1 = some (descendingRows, .error .upperOrder)
#guard observed (change (change v1 425 2) 420 12) 2 = some (unorderedRows, .error .lowerOrder)
#guard observed absentCounts 0 = observed v1 0

private def annotated : Bytes :=
  (Footer.fileBytes v1 0 547).append <|
    (Bytes.ofList [0x25, 26]).append <|
    (Footer.fileBytes v1 547 1106).append (Bytes.ofList [0x4e, 0x02, 0, 0, 80, 65, 82, 49])

private def missingOrder : Bytes :=
  (Footer.fileBytes v1 0 1100).append
    (Bytes.ofList [0, 0x47, 0x02, 0, 0, 80, 65, 82, 49])

#guard observed annotated 0 = some (ascendingRows, .error (.order .annotated))
#guard observed missingOrder 0 = some (ascendingRows, .error (.order .missingOrder))
#guard observed (change v1 1102 0x2c) 0 = some (ascendingRows, .error (.order .unsupportedOrder))
#guard observed (change v1 323 14) 0 = some (ascendingRows, .error (.index (.boundaryOrder 7)))

private def indexAbsent : Bool := Id.run do
  let some ⟨_, binding⟩ := bindInput "number" noIndex | return false
  let .ok result := read {} binding 0 | return false
  return result.index == .ok none

#guard indexAbsent

private def latePageErrorKept (source : Bytes) : Bool := Id.run do
  let some ⟨_, binding⟩ := bindInput "number" source | return false
  let .error (.page 0 0 "number" 2 62 (.decode (.scalar _))) := read {} binding 0 | return false
  return (read {} binding 0).map Result.rows == readFull {} binding 0

-- Corrupt the last page's definition section even when the index is also invalid.
#guard latePageErrorKept (change v1 79 17)
#guard latePageErrorKept (change (change v1 79 17) 323 14)

end Silmaril.Formats.Parquet.ColumnIndex.Signed
