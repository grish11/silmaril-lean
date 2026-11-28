module

import Silmaril.Formats.Parquet.DeltaFixedPage.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Bytes
meta import Silmaril.Formats.Parquet.DeltaFixedPage.Defs
meta import Batteries.Data.Except

/-! Pinned PyArrow fixed-width encoding-7 pages and rejected scalar extents. -/

namespace Silmaril.Formats.Parquet.DeltaFixedPage

private def mixedScalars : Bytes := .ofList [
  0x80, 0x01, 0x04, 0x03, 0x00, 0x02, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00,
  0x00, 0x00, 0x80, 0x01, 0x04, 0x03, 0x06, 0x03, 0x01, 0x00, 0x00, 0x00,
  0x02, 0x00, 0x00, 0x00, 0xff, 0x00, 0x61, 0x62]
private def requiredScalars : Bytes := .ofList [
  0x80, 0x01, 0x04, 0x04, 0x00, 0x09, 0x04, 0x00, 0x00, 0x00, 0x69, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x80, 0x01, 0x04, 0x04, 0x0a, 0x07, 0x04, 0x00, 0x00, 0x00,
  0x30, 0x09, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0x01, 0x02, 0x03, 0x04, 0x7f, 0x80,
  0x00, 0x01, 0x00]
private def nullScalars : Bytes := .ofList [
  0x80, 0x01, 0x04, 0x00, 0x00, 0x80, 0x01, 0x04, 0x00, 0x00]

private def mixedLevels : Bytes := .ofList [3, 0x0d]
private def nullLevels : Bytes := .ofList [6, 0]

private def mixed : List (Option Bytes) :=
  [some (.ofList [0xff, 0, 0x61]), none, some (.ofList [0xff, 0, 0x62]), some (.ofList [0xff, 0, 0x62])]
private def required : List (Option Bytes) :=
  [some (.ofList [0, 0xff, 1, 2, 3]), some (.ofList [0, 0xff, 1, 2, 4]),
    some (.ofList [0, 0xff, 1, 2, 4]), some (.ofList [0x7f, 0x80, 0, 1, 0])]

private def bodyV1 (nullable : Bool) (levels scalars : Bytes) : Bytes :=
  if nullable then (Bytes.ofList [levels.length.toUInt8, 0, 0, 0]).append (levels.append scalars)
  else scalars

private def bodyV2 (_ : Bool) (levels scalars : Bytes) : Bytes := levels.append scalars

private def hex (bytes : Bytes) : String :=
  String.ofList (bytes.toList.flatMap fun b => [(b.toNat / 16).digitChar, (b.toNat % 16).digitChar])

private def fixtureRows (version : String) (body : Bool → Bytes → Bytes → Bytes) : String :=
  let line name width nullable slots nulls (levels scalars : Bytes) :=
    String.intercalate "\t" [version, name, toString width, if nullable then "1" else "0",
      toString slots, toString nulls, toString levels.length, hex (body nullable levels scalars),
      hex scalars] ++ "\n"
  line "mixed" 3 true 4 1 mixedLevels mixedScalars ++
  line "required" 5 false 4 0 .empty requiredScalars ++
  line "all-null" 3 true 3 3 nullLevels nullScalars

#guard (include_str "../../../../tests/formats/parquet-delta-fixed-page/pyarrow-26.0.1.tsv") =
  fixtureRows "1.0" bodyV1 ++ fixtureRows "2.0" bodyV2

private def deltaLimits : DeltaBinaryPacked.Limits := ⟨128, 16, 128, 4, 2⟩
private def limits : Limits :=
  ⟨⟨128, 128, ⟨16, 16⟩, 0⟩, ⟨deltaLimits, ⟨deltaLimits, 40, 8⟩, 8, 40⟩⟩

private def leaf (nullable : Bool) (width : Int) : Footer.SchemaElement :=
  ⟨some .fixedLenByteArray, some width, some (if nullable then .optional else .required), "v", none⟩

private def params (nullable : Bool) (count : Nat) (version : ScalarPage.Version)
    (body : Bytes) : ScalarPage.Parameters :=
  ⟨⟨body.length, body.length⟩, ⟨0, if nullable then 1 else 0⟩, count, 0, 7, version⟩

private def runV1 (nullable : Bool) (width : Int) (count : Nat) (levels scalars : Bytes) :
    Except Error (List (Option Bytes)) :=
  let body := bodyV1 nullable levels scalars
  decode (leaf nullable width) .fixedLenByteArray (params nullable count (.v1 3 3) body) limits body

private def runV2 (nullable : Bool) (width : Int) (count nulls : Nat) (levels scalars : Bytes) :
    Except Error (List (Option Bytes)) :=
  let body := bodyV2 nullable levels scalars
  let h := ScalarPage.Version.v2 nulls count 0 levels.length (some false)
  decode (leaf nullable width) .fixedLenByteArray (params nullable count h body) limits body

#guard runV1 true 3 4 mixedLevels mixedScalars = .ok mixed
#guard runV2 true 3 4 1 mixedLevels mixedScalars = .ok mixed
#guard runV1 false 5 4 .empty requiredScalars = .ok required
#guard runV2 false 5 4 0 .empty requiredScalars = .ok required
#guard runV1 true 3 3 nullLevels nullScalars = .ok [none, none, none]
#guard runV2 true 3 3 3 nullLevels nullScalars = .ok [none, none, none]

#guard selectWidth { leaf true 3 with typeLength := none } .fixedLenByteArray = .error .invalidWidth
#guard selectWidth (leaf true (-1)) .fixedLenByteArray = .error .invalidWidth
#guard selectWidth (leaf true 0) .fixedLenByteArray = .error .invalidWidth
#guard selectWidth (leaf true ((2 ^ 31) - 1)) .fixedLenByteArray = .ok ((2 ^ 31) - 1)
#guard selectWidth (leaf true (2 ^ 31)) .fixedLenByteArray = .error .invalidWidth
#guard selectWidth (leaf true 3) .byteArray = .error .schemaMismatch
#guard selectWidth { leaf true 3 with numChildren := some 1 } .fixedLenByteArray = .error .schemaMismatch
#guard selectWidth { leaf true 3 with physicalType := some .byteArray } .fixedLenByteArray = .error .schemaMismatch

#guard runV1 true 4 4 mixedLevels mixedScalars = .error .widthMismatch
#guard runV2 true 2 4 1 mixedLevels mixedScalars = .error (.scalar (.suffixStream .valueLimit))
#guard runV2 true 9 3 3 nullLevels nullScalars = .error .widthLimit
#guard runV1 true 3 3 mixedLevels mixedScalars = .error (.scalar (.prefixStream .countMismatch))
#guard runV2 true 3 4 2 mixedLevels mixedScalars = .error (.page (.levels .presentCountMismatch))
#guard runV1 true 3 4 mixedLevels (mixedScalars.push 0) = .error (.scalar (.suffixStream .trailingBytes))
#guard runV2 true 3 4 1 mixedLevels (.ofList (mixedScalars.toList.take (mixedScalars.length - 1))) =
  .error (.scalar (.suffixStream .truncated))
#guard runV1 true 3 3 nullLevels .empty = .error (.scalar (.prefixStream (.wire .truncated)))
#guard runV2 true 3 3 3 nullLevels (nullScalars.push 0) = .error (.scalar (.suffixStream .trailingBytes))
#guard readValues 3 3 { limits.values with decodedBytes := 8 } mixedScalars = .error .decodedByteLimit
#guard readValues 3 3 { limits.values with valueBytes := 3, decodedBytes := 9 } mixedScalars =
  .ok (mixed.filterMap id)
#guard readValues 3 0 { limits.values with valueBytes := 3, decodedBytes := 0 } nullScalars = .ok []

#guard decode (leaf false 5) .fixedLenByteArray
    { params false 4 (.v1 3 3) requiredScalars with encoding := 6 } limits requiredScalars =
  .error (.page (.unsupportedEncoding 6))
#guard decode (leaf false 5) .fixedLenByteArray
    (params false 4 (.v1 3 3) requiredScalars) limits (requiredScalars.push 0) =
  .error (.page (.payload .compressedSizeMismatch))

end Silmaril.Formats.Parquet.DeltaFixedPage
