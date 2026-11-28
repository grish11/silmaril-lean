module

import Silmaril.Formats.Parquet.ByteStreamSplitPage.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Bytes
meta import Silmaril.Formats.Parquet.ByteStreamSplitPage.Defs
meta import Batteries.Data.Except

/-! Actual PyArrow V1/V2 pages, raw floating bits, and schema and extent rejections. -/

namespace Silmaril.Formats.Parquet.ByteStreamSplitPage

private def limits : Limits := ⟨⟨300, 300, ⟨96, 16⟩, 0⟩, ⟨64, 256, 8⟩⟩
private def signed32 : Bytes := .ofList [
  0, 0xfe, 4, 0xff, 0, 0xff, 3, 0xff, 0, 0xff, 2, 0xff, 0x80, 0xff, 1, 0x7f]
private def signed64 : Bytes := .ofList [
  0, 0xfe, 8, 0xff, 0, 0xff, 7, 0xff, 0, 0xff, 6, 0xff, 0, 0xff, 5, 0xff,
  0, 0xff, 4, 0xff, 0, 0xff, 3, 0xff, 0, 0xff, 2, 0xff, 0x80, 0xff, 1, 0x7f]
private def floatBits : Bytes := .ofList [0x45, 0x21, 0, 1, 0x23, 0x43, 0, 0,
  0xc1, 0xc5, 0, 0, 0x7f, 0xff, 0x80, 0]
private def doubleBits : Bytes := .ofList [
  0xbc, 0x45, 0, 1, 0x9a, 0x23, 0, 0, 0x78, 1, 0, 0, 0x56, 0xef, 0, 0,
  0x34, 0xcd, 0, 0, 0x12, 0xab, 0, 0, 0xf8, 0xf8, 0, 0, 0x7f, 0xff, 0x80, 0]
private def fixed : Bytes := .ofList [0, 0x80, 0x11, 0xff, 0, 0x22, 0x41, 0x7f, 0x33]
private def snappyV2 : Bytes := .ofList [
  0x19, 0x6d, 0xdb, 0xb6, 0x6d, 0xdb, 0xb6, 0x6d, 0xdb, 0xb6, 0x6d, 0xdb, 0xb6,
  0x80, 2, 0x0c, 0, 0xfe, 4, 0xff, 0xf2, 4, 0, 8, 0xff, 3, 0xff, 0xf6, 4, 0,
  8, 2, 0xff, 0, 0xea, 4, 0, 0x0c, 0x80, 0xff, 1, 0x7f, 0xee, 4, 0]
private def mixedLevels : Bytes := .ofList [3, 0x2d]
private def fixedLevels : Bytes := .ofList [3, 0x15]
private def nullLevels : Bytes := .ofList [6, 0]

private def v1Body (levels lanes : Bytes) : Bytes :=
  (Bytes.ofList [2, 0, 0, 0]).append (levels.append lanes)
private def v2Body (levels lanes : Bytes) : Bytes := levels.append lanes

private def hex (bytes : Bytes) : String :=
  String.ofList (bytes.toList.flatMap fun b => [(b.toNat / 16).digitChar, (b.toNat % 16).digitChar])

private def fixtureLine (version name physical width : String) (codec decoded slots nulls levels : Nat)
    (flag : String) (body : Bytes) : String :=
  String.intercalate "\t" [version, name, physical, width, toString codec, toString body.length,
    toString decoded, toString slots, toString nulls, toString levels, flag, hex body] ++ "\n"

private def fixtureRows (version flag : String) (body : Bytes → Bytes → Bytes) : String :=
  let line name physical width slots nulls levels lanes :=
    let page := body levels lanes
    fixtureLine version name physical width 0 page.length slots nulls levels.length flag page
  line "signed32" "INT32" "-" 6 2 mixedLevels signed32 ++
  line "signed64" "INT64" "-" 6 2 mixedLevels signed64 ++
  line "float-bits" "FLOAT" "-" 6 2 mixedLevels floatBits ++
  line "double-bits" "DOUBLE" "-" 6 2 mixedLevels doubleBits ++
  line "fixed" "FIXED_LEN_BYTE_ARRAY" "3" 5 2 fixedLevels fixed ++
  line "all-null" "FIXED_LEN_BYTE_ARRAY" "3" 3 3 nullLevels .empty

#guard (include_str "../../../../tests/formats/parquet-byte-stream-split-page/pyarrow-26.0.1.tsv") =
  fixtureRows "1.0" "-" v1Body ++ fixtureRows "2.0" "0" v2Body ++
  fixtureLine "2.0" "signed32-snappy" "INT32" "-" 1 269 96 32 13 "1" snappyV2

private def leaf (physical : Footer.PhysicalType) (width : Option Int := none) : Footer.SchemaElement :=
  ⟨some physical, width, some .optional, "v", none⟩

private def fixedLeaf : Footer.SchemaElement := leaf .fixedLenByteArray (some 3)

private def params (slots : Nat) (version : ScalarPage.Version) (body : Bytes) : ScalarPage.Parameters :=
  ⟨⟨body.length, body.length⟩, ⟨0, 1⟩, slots, 0, 9, version⟩

private def runV1 (schema : Footer.SchemaElement) (physical : Footer.PhysicalType)
    (slots : Nat) (levels lanes : Bytes) : Except Error Decoded :=
  let body := v1Body levels lanes
  decode schema physical (params slots (.v1 3 3) body) limits body

private def runV2 (schema : Footer.SchemaElement) (physical : Footer.PhysicalType)
    (slots nulls : Nat) (levels lanes : Bytes) : Except Error Decoded :=
  let body := v2Body levels lanes
  decode schema physical (params slots (.v2 nulls slots 0 levels.length (some false)) body) limits body

private def slotsMatch (kind : ByteStreamSplit.Kind) [DecidableEq kind.Value]
    (expected : List (Option kind.Value)) (result : Except Error Decoded) : Bool :=
  match result with
  | .error _ => false
  | .ok result => if h : result.kind = kind then decide ((h ▸ result.slots) = expected) else false

private def values32 : List (Option Int32) :=
  [some (-2147483648), none, some (-2), some 0x01020304, none, some 2147483647]
private def values64 : List (Option Int64) :=
  [some (-9223372036854775808), none, some (-2), some 0x0102030405060708, none, some 9223372036854775807]
private def valuesFloat : List (Option UInt32) :=
  [some 0x7fc12345, none, some 0xffc54321, some 0x80000000, none, some 1]
private def valuesDouble : List (Option UInt64) :=
  [some 0x7ff8123456789abc, none, some 0xfff8abcdef012345, some 0x8000000000000000, none, some 1]
private def valuesFixed : List (Option Bytes) :=
  [some (.ofList [0, 0xff, 0x41]), none, some (.ofList [0x80, 0, 0x7f]), none, some (.ofList [0x11, 0x22, 0x33])]

#guard slotsMatch .int32 values32 (runV1 (leaf .int32) .int32 6 mixedLevels signed32)
#guard slotsMatch .int32 values32 (runV2 (leaf .int32) .int32 6 2 mixedLevels signed32)
#guard slotsMatch .int64 values64 (runV1 (leaf .int64) .int64 6 mixedLevels signed64)
#guard slotsMatch .int64 values64 (runV2 (leaf .int64) .int64 6 2 mixedLevels signed64)
#guard slotsMatch .floatBits valuesFloat (runV1 (leaf .float) .float 6 mixedLevels floatBits)
#guard slotsMatch .floatBits valuesFloat (runV2 (leaf .float) .float 6 2 mixedLevels floatBits)
#guard slotsMatch .doubleBits valuesDouble (runV1 (leaf .double) .double 6 mixedLevels doubleBits)
#guard slotsMatch .doubleBits valuesDouble (runV2 (leaf .double) .double 6 2 mixedLevels doubleBits)
#guard slotsMatch (.fixedLenBytes 3) valuesFixed (runV1 fixedLeaf .fixedLenByteArray 5 fixedLevels fixed)
#guard slotsMatch (.fixedLenBytes 3) valuesFixed (runV2 fixedLeaf .fixedLenByteArray 5 2 fixedLevels fixed)
#guard slotsMatch (.fixedLenBytes 3) [none, none, none] (runV1 fixedLeaf .fixedLenByteArray 3 nullLevels .empty)
#guard slotsMatch (.fixedLenBytes 3) [none, none, none] (runV2 fixedLeaf .fixedLenByteArray 3 3 nullLevels .empty)

private def compressedParams : ScalarPage.Parameters :=
  ⟨⟨45, 269⟩, ⟨0, 1⟩, 96, 1, 9, .v2 32 96 0 13 (some true)⟩
#guard slotsMatch .int32 (List.replicate 16 values32).flatten
  (decode (leaf .int32) .int32 compressedParams limits snappyV2)

#guard selectKind (leaf .int32) .int64 = .error .schemaMismatch
#guard selectKind { fixedLeaf with numChildren := some 1 } .fixedLenByteArray = .error .schemaMismatch
#guard selectKind (leaf .boolean) .boolean = .error (.unsupportedPhysical .boolean)
#guard selectKind (leaf .byteArray) .byteArray = .error (.unsupportedPhysical .byteArray)
#guard selectKind (leaf .fixedLenByteArray) .fixedLenByteArray = .error .invalidFixedWidth
#guard selectKind (leaf .fixedLenByteArray (some (-1))) .fixedLenByteArray = .error .invalidFixedWidth
#guard selectKind (leaf .fixedLenByteArray (some 0)) .fixedLenByteArray = .error .invalidFixedWidth
#guard selectKind (leaf .fixedLenByteArray (some (2 ^ 31))) .fixedLenByteArray = .error .invalidFixedWidth
#guard (runV2 (leaf .fixedLenByteArray (some 2)) .fixedLenByteArray 5 2 fixedLevels fixed).map (fun _ => ()) =
  .error (.scalar .trailingBytes)
#guard (runV2 (leaf .int32) .int32 6 2 mixedLevels (.ofList (signed32.toList.take 15))).map (fun _ => ()) =
  .error (.scalar .truncated)
#guard (runV1 (leaf .int32) .int32 6 mixedLevels (signed32.push 0)).map (fun _ => ()) =
  .error (.scalar .trailingBytes)
#guard (runV2 (leaf .int32) .int32 6 1 mixedLevels signed32).map (fun _ => ()) =
  .error (.page (.levels .presentCountMismatch))
#guard (decode (leaf .int32) .int32 { compressedParams with encoding := 5 } limits snappyV2).map (fun _ => ()) =
  .error (.page (.unsupportedEncoding 5))
#guard (decode (leaf .int32) .int32 { compressedParams with sizes := ⟨45, 12⟩ } limits snappyV2).map (fun _ => ()) =
  .error (.page .invalidLevelExtent)
#guard (decode (leaf .int32) .int32 compressedParams limits (snappyV2.push 0)).map (fun _ => ()) =
  .error (.page (.payload .compressedSizeMismatch))
#guard (decode fixedLeaf .fixedLenByteArray (params 3 (.v2 3 3 0 2 (some false)) nullLevels)
    { limits with scalars := { limits.scalars with width := 2 } } nullLevels).map (fun _ => ()) =
  .error (.scalar .widthLimit)

end Silmaril.Formats.Parquet.ByteStreamSplitPage
