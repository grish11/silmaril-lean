module

import Silmaril.Formats.Parquet.DeltaPage.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Bytes
meta import Silmaril.Formats.Parquet.DeltaPage.Defs
meta import Batteries.Data.Except

/-! Exact PyArrow V1/V2 bodies, pairing checks, and independent budgets. -/

namespace Silmaril.Formats.Parquet.DeltaPage

private def deltaLimits : DeltaBinaryPacked.Limits := ⟨128, 8, 256, 4, 1⟩
private def lengthLimits : DeltaLengthByteArray.Limits := ⟨deltaLimits, 32, 16⟩
private def limits : Limits := ⟨⟨128, 128, ⟨8, 2⟩, 0⟩, deltaLimits, lengthLimits,
  ⟨deltaLimits, lengthLimits, 16, 64⟩⟩

private def signed32 : Bytes := .ofList (
  [0x80, 1, 4, 5, 0x26, 0x2d, 6, 0, 0, 0, 0x80, 0xbb, 0x30] ++ List.replicate 21 0)
private def signed64 : Bytes := .ofList [0x80, 2, 4, 3, 0x80, 0xc8, 0xaf, 0xa0, 0x25, 5, 0, 0, 0, 0]
private def lengthBytes : Bytes := .ofList (
  [0x80, 1, 4, 4, 0, 1, 2, 0, 0, 0, 0x0b] ++ List.replicate 7 0 ++
  [0xc3, 0xa9, 0xff, 0, 0x80, 0x78, 0x79])
private def prefixBytes : Bytes := .ofList (
  [0x80, 1, 4, 6, 0, 3, 3, 0, 0, 0, 4, 0x21] ++ List.replicate 10 0 ++
  [0x80, 1, 4, 6, 8, 3, 2, 0, 0, 0, 0x4c, 2] ++ List.replicate 6 0 ++
  [0x61, 0x78, 0x69, 0x73, 0x6c, 0x65, 0xff, 0, 0x80, 0x81])
private def nullBytes : Bytes := .ofList [0x80, 1, 4, 0, 0, 0x80, 1, 4, 0, 0]

private def v2Body (levels : List UInt8) (scalars : Bytes) : Bytes :=
  (Bytes.ofList levels).append scalars
private def v1Body (levels : List UInt8) (scalars : Bytes) : Bytes :=
  (Bytes.ofList [2, 0, 0, 0]).append (v2Body levels scalars)

private def levels32 : List UInt8 := [3, 0x6d]
private def levels64 : List UInt8 := [3, 0x15]
private def lengthLevels : List UInt8 := [3, 0x2d]
private def prefixLevels : List UInt8 := [3, 0xed]
private def nullLevels : List UInt8 := [6, 0]

private def hex (bytes : Bytes) : String :=
  String.ofList (bytes.toList.flatMap fun b => [(b.toNat / 16).digitChar, (b.toNat % 16).digitChar])

private def fixtureLine (version name physical : String) (id slots nulls : Nat)
    (levels : List UInt8) (body scalars : Bytes) : String :=
  String.intercalate "\t" [version, name, physical, toString id, toString slots, toString nulls,
    toString levels.length, hex body, hex scalars] ++ "\n"

private def fixtureRows (version : String) (body : List UInt8 → Bytes → Bytes) : String :=
  fixtureLine version "signed32" "INT32" 5 7 2 levels32 (body levels32 signed32) signed32 ++
  fixtureLine version "signed64" "INT64" 5 5 2 levels64 (body levels64 signed64) signed64 ++
  fixtureLine version "length" "BYTE_ARRAY" 6 6 2 lengthLevels (body lengthLevels lengthBytes) lengthBytes ++
  fixtureLine version "prefix" "BYTE_ARRAY" 7 8 2 prefixLevels (body prefixLevels prefixBytes) prefixBytes ++
  fixtureLine version "all-null" "BYTE_ARRAY" 7 3 3 nullLevels (body nullLevels nullBytes) nullBytes

#guard (include_str "../../../../tests/formats/parquet-delta-page/pyarrow-26.0.1.tsv") =
  fixtureRows "1.0" v1Body ++ fixtureRows "2.0" v2Body

private def params (id : Int) (slots : Nat) (version : ScalarPage.Version) (body : Bytes) :
    ScalarPage.Parameters :=
  ⟨⟨body.length, body.length⟩, ⟨0, 1⟩, slots, 0, id, version⟩

private def runV1 (kind : Kind) (id : Int) (slots : Nat) (levels : List UInt8) (scalars : Bytes) :
    Except Error (List (Option kind.Value)) :=
  let body := v1Body levels scalars
  decode kind (params id slots (.v1 3 3) body) limits body

private def runV2 (kind : Kind) (id : Int) (slots nulls : Nat) (levels : List UInt8) (scalars : Bytes) :
    Except Error (List (Option kind.Value)) :=
  let body := v2Body levels scalars
  decode kind (params id slots (.v2 nulls slots 0 levels.length (some false)) body) limits body

private def values32 : List (Option Int32) := [some 19, none, some (-4), some 19, none, some 7, some (-4)]
private def values64 : List (Option Int64) := [some 5000000000, none, some 4999999997, none, some 4999999994]
private def valuesLength : List (Option Bytes) :=
  [some .empty, none, some (.ofList [0xc3, 0xa9]), some (.ofList [0xff, 0, 0x80]), none,
    some (.ofList [0x78, 0x79])]
private def valuesPrefix : List (Option Bytes) :=
  [some ⟨"axis".toUTF8⟩, none, some ⟨"axle".toUTF8⟩, some (.ofList [0xff, 0, 0x80]), none,
    some (.ofList [0xff, 0, 0x81]), some .empty, some .empty]

#guard runV1 (.signed .int32) 5 7 levels32 signed32 = .ok values32
#guard runV2 (.signed .int32) 5 7 2 levels32 signed32 = .ok values32
#guard runV1 (.signed .int64) 5 5 levels64 signed64 = .ok values64
#guard runV2 (.signed .int64) 5 5 2 levels64 signed64 = .ok values64
#guard runV1 .byteArray 6 6 lengthLevels lengthBytes = .ok valuesLength
#guard runV2 .byteArray 6 6 2 lengthLevels lengthBytes = .ok valuesLength
#guard runV1 .byteArray 7 8 prefixLevels prefixBytes = .ok valuesPrefix
#guard runV2 .byteArray 7 8 2 prefixLevels prefixBytes = .ok valuesPrefix
#guard runV1 .byteArray 7 3 nullLevels nullBytes = .ok [none, none, none]
#guard runV2 .byteArray 7 3 3 nullLevels nullBytes = .ok [none, none, none]

#guard Kind.ofPhysical? .int32 = some (.signed .int32)
#guard Kind.ofPhysical? .int64 = some (.signed .int64)
#guard Kind.ofPhysical? .byteArray = some .byteArray
#guard Kind.ofPhysical? .fixedLenByteArray = none
#guard Kind.ofPhysical? .float = none
#guard runV1 (.signed .int32) 6 7 levels32 signed32 = .error (.unsupportedEncoding (.signed .int32) 6)
#guard runV2 .byteArray 5 6 2 lengthLevels lengthBytes = .error (.unsupportedEncoding .byteArray 5)
#guard runV2 .byteArray 8 8 2 prefixLevels prefixBytes = .error (.unsupportedEncoding .byteArray 8)
#guard runV1 (.signed .int32) 5 7 [3, 0x4d] signed32 = .error (.binaryPacked .countMismatch)
#guard runV2 (.signed .int32) 5 7 1 levels32 signed32 = .error (.page (.levels .presentCountMismatch))
#guard runV2 (.signed .int64) 5 5 2 levels64 (signed64.push 0) = .error (.binaryPacked .trailingBytes)
#guard runV2 .byteArray 6 6 2 lengthLevels (lengthBytes.push 0) = .error (.lengthByteArray .trailingBytes)
#guard runV2 .byteArray 7 8 2 prefixLevels (prefixBytes.push 0) =
  .error (.byteArray (.suffixStream .trailingBytes))

private def signedBody : Bytes := v2Body levels32 signed32
private def lenBody : Bytes := v2Body lengthLevels lengthBytes
private def prefBody : Bytes := v2Body prefixLevels prefixBytes

#guard decode (.signed .int32) (params 5 7 (.v2 2 7 0 2 (some false)) signedBody)
    limits (signedBody.push 0) = .error (.page (.payload .compressedSizeMismatch))
#guard decode (.signed .int32) { (params 5 7 (.v2 2 7 0 2 (some false)) signedBody) with
      sizes := ⟨signedBody.length, 1⟩ } limits signedBody = .error (.page .invalidLevelExtent)
#guard decode (.signed .int32) (params 5 7 (.v1 4 3) (v1Body levels32 signed32))
    limits (v1Body levels32 signed32) = .error (.page .unsupportedLevelEncoding)
#guard decode (.signed .int32) (params 5 7 (.v2 2 7 0 2 (some false)) signedBody)
    { limits with binaryPacked := { deltaLimits with values := 4 } } signedBody =
  .error (.binaryPacked .valueLimit)
#guard decode .byteArray (params 6 6 (.v2 2 6 0 2 (some false)) lenBody)
    { limits with lengthByteArray := { lengthLimits with payloadBytes := 6 } } lenBody =
  .error (.lengthByteArray .payloadLimit)
#guard decode .byteArray (params 7 8 (.v2 2 8 0 2 (some false)) prefBody)
    { limits with byteArray := { limits.byteArray with decodedBytes := 13 } } prefBody =
  .error (.byteArray .decodedByteLimit)

end Silmaril.Formats.Parquet.DeltaPage
