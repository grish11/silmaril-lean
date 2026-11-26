module

import Silmaril.Formats.Parquet.RleBooleanPage.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Bytes
meta import Silmaril.Formats.Parquet.RleBooleanPage.Defs
meta import Batteries.Data.Except

/-! Pinned PyArrow pages and isolated malformed Boolean value streams. -/

namespace Silmaril.Formats.Parquet.RleBooleanPage

private def limits : Limits := ⟨⟨100, 100, ⟨64, 16⟩, 0⟩, ⟨64, 16⟩⟩
private def mixed : List (Option Bool) := [some true, none, some false, some true, some false, none, some true]
private def required : List (Option Bool) :=
  List.replicate 16 (some true) ++ List.replicate 16 (some false) ++
    [some true, some false, some true, some false, some true]
private def allNull : List (Option Bool) := [none, none, none]

private def lengthWord (size : UInt8) : Bytes := .ofList [size, 0, 0, 0]
private def mixedValues : Bytes := .ofList [2, 0, 0, 0, 3, 0x15]
private def requiredValues : Bytes := .ofList [6, 0, 0, 0, 32, 1, 32, 0, 3, 0x15]
private def mixedLevels : Bytes := .ofList [3, 0x5d]
private def nullLevels : Bytes := .ofList [6, 0]

private def bodyV1 (nullable : Bool) (levels values : Bytes) : Bytes :=
  if nullable then (lengthWord levels.length.toUInt8).append (levels.append values) else values

private def bodyV2 (_ : Bool) (levels values : Bytes) : Bytes :=
  levels.append values

private def hex (bytes : Bytes) : String :=
  String.ofList (bytes.toList.flatMap fun b => [(b.toNat / 16).digitChar, (b.toNat % 16).digitChar])

private def fixtureRows (version : String) (body : Bool → Bytes → Bytes → Bytes) : String :=
  let line name nullable slots nulls (levels values : Bytes) :=
    let page := body nullable levels values
    String.intercalate "\t" [version, name, if nullable then "1" else "0", toString page.length,
      toString slots, toString nulls, toString levels.length, hex page] ++ "\n"
  line "mixed" true 7 2 mixedLevels mixedValues ++
  line "required" false 37 0 .empty requiredValues ++
  line "all-null" true 3 3 nullLevels (lengthWord 0)

#guard (include_str "../../../../tests/formats/parquet-rle-boolean-page/pyarrow-26.0.1.tsv") =
  fixtureRows "1.0" bodyV1 ++ fixtureRows "2.0" bodyV2

private def params (nullable : Bool) (count : Nat) (version : ScalarPage.Version)
    (body : Bytes) : ScalarPage.Parameters :=
  ⟨⟨body.length, body.length⟩, ⟨0, if nullable then 1 else 0⟩, count, 0, 3, version⟩

private def runV1 (nullable : Bool) (count : Nat) (levels values : Bytes) :
    Except Error (List (Option Bool)) :=
  let body := bodyV1 nullable levels values
  decode .boolean (params nullable count (.v1 3 3) body) limits body

private def runV2 (nullable : Bool) (count nulls : Nat) (levels values : Bytes) :
    Except Error (List (Option Bool)) :=
  let body := bodyV2 nullable levels values
  decode .boolean (params nullable count (.v2 nulls count 0 levels.length (some false)) body) limits body

#guard runV1 true 7 mixedLevels mixedValues = .ok mixed
#guard runV2 true 7 2 mixedLevels mixedValues = .ok mixed
#guard runV1 false 37 .empty requiredValues = .ok required
#guard runV2 false 37 0 .empty requiredValues = .ok required
#guard runV1 true 3 nullLevels (lengthWord 0) = .ok allNull
#guard runV2 true 3 3 nullLevels (lengthWord 0) = .ok allNull

-- Change only the scalar length word in each real mixed page.
#guard runV1 true 7 mixedLevels (.ofList [1, 0, 0, 0, 3, 0x15]) = .error .lengthMismatch
#guard runV1 true 7 mixedLevels (.ofList [3, 0, 0, 0, 3, 0x15]) = .error .lengthMismatch
#guard runV2 true 7 2 mixedLevels (.ofList [1, 0, 0, 0, 3, 0x15]) = .error .lengthMismatch
#guard runV2 true 7 2 mixedLevels (.ofList [3, 0, 0, 0, 3, 0x15]) = .error .lengthMismatch
#guard runV1 true 7 mixedLevels (.ofList [255, 255, 255, 255, 3, 0x15]) = .error .lengthMismatch
#guard runV2 true 7 2 mixedLevels (.ofList [255, 255, 255, 255, 3, 0x15]) = .error .lengthMismatch
#guard runV2 true 3 3 nullLevels .empty = .error .truncatedLength
#guard readValues 5 limits.values (.ofList [2, 0, 0]) = .error .truncatedLength

-- The word itself is exact, then the run decoder must consume every byte.
#guard readValues 5 limits.values (.ofList [3, 0, 0, 0, 3, 0x15, 0]) = .error (.hybrid .trailingBytes)
#guard readValues 5 limits.values (.ofList [1, 0, 0, 0, 3]) = .error (.hybrid .truncated)
#guard readValues 1 limits.values (.ofList [2, 0, 0, 0, 4, 1]) = .error (.hybrid .countMismatch)
#guard readValues 9 limits.values mixedValues = .error (.hybrid .truncated)
#guard readValues 1 limits.values (.ofList [2, 0, 0, 0, 2, 2]) = .error (.hybrid .valueOverflow)
#guard readValues 1 limits.values (.ofList [3, 0, 0, 0, 0x82, 0, 1]) =
  .error (.hybrid .noncanonicalHeader)
#guard readValues 5 ⟨5, 1⟩ mixedValues = .error (.hybrid .byteLimit)
#guard readValues 5 ⟨4, 2⟩ mixedValues = .error (.hybrid .valueLimit)
#guard readValues 0 ⟨0, 0⟩ (lengthWord 0) = .ok []
#guard readValues 0 limits.values mixedValues = .error (.hybrid .trailingBytes)
#guard readValues 5 limits.values (.ofList [2, 0, 0, 0, 3, 0xf5]) =
  .ok [true, false, true, false, true]

#guard decode .int32 (params false 37 (.v1 3 3) requiredValues) limits requiredValues =
  .error (.unsupportedPhysical .int32)
#guard decode .boolean { params false 37 (.v1 3 3) requiredValues with encoding := 0 }
    limits requiredValues = .error (.page (.unsupportedEncoding 0))
#guard runV2 true 7 1 mixedLevels mixedValues = .error (.page (.levels .presentCountMismatch))

end Silmaril.Formats.Parquet.RleBooleanPage
