module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Footer.Defs
import Silmaril.Formats.Parquet.Page.Defs
import Silmaril.Formats.Parquet.LegacyBitPackedV1.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Bytes
meta import Silmaril.Formats.Parquet.Footer.Defs
meta import Silmaril.Formats.Parquet.Page.Defs
meta import Silmaril.Formats.Parquet.LegacyBitPackedV1.Defs

/-! A complete pinned parquet-java V1 file and isolated malformed page bodies. -/

namespace Silmaril.Formats.Parquet.LegacyBitPackedV1

private def fixture : Bytes :=
  ⟨include_bytes "../../../../data/parquet-legacy-bit-packed-v1/optional-int32-v1.parquet"⟩

private def definitions : Bytes := .ofList [0xb2, 0x80]
private def suffix : Bytes := .ofList [
  0x11, 0, 0, 0, 0xf7, 0xff, 0xff, 0xff, 0x2c, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x80]
private def body : Bytes := definitions.append suffix

private def schema : FlatPage.LevelSchema := ⟨0, 1⟩
private def limits : ScalarPage.Limits := ⟨64, 64, ⟨9, 2⟩, 0⟩
private def levels : List Nat := [1, 0, 1, 1, 0, 0, 1, 0, 1]
private def expected : Decoded :=
  ⟨[some 17, none, some (-9), some 300, none, none, some 0, none, some (-2147483648)], 4⟩

private def fixturePage : Option (Page.Header × Footer.PhysicalType × Int × Bytes) := do
  let (footer, metadata) ← (Footer.readFooter {} fixture).toOption
  let [_, leaf] := metadata.schema | none
  let [group] := metadata.rowGroups | none
  let [column] := group.columns | none
  if leaf.physicalType != some .int32 || leaf.repetition != some .optional ||
      column.metadata.pathInSchema != [leaf.name] || group.numRows != 9 then none
  else
    let span ← Page.columnSpan footer.start column.metadata
    let [frame] ← (Page.readChunk {} fixture span).toOption | none
    if (frame.header.start, frame.payload.start, frame.payload.stop) != (4, 21, 43) then none
    else
      pure (frame.value, column.metadata.physicalType, column.metadata.codec,
        Footer.fileBytes fixture frame.payload.start frame.payload.stop)

private def header (source : Bytes) (count : Nat := 9) : Page.Header :=
  ⟨source.length, source.length, none, .dataV1 ⟨count, 0, 4, 3⟩⟩

#guard fixturePage = some (header body, .int32, 0, body)

#guard fixturePage.map (fun (header, physical, codec, source) =>
    prepare physical schema codec header limits source) = some (.ok ⟨levels, suffix⟩)

#guard fixturePage.map (fun (header, physical, codec, source) =>
    decodeInt32 physical schema codec header limits source) = some (.ok expected)

private def run (header : Page.Header) (source : Bytes) : Except Error Decoded :=
  decodeInt32 .int32 schema 0 header limits source

#guard run (header .empty 0) .empty = .ok ⟨[], 0⟩
#guard run (header (.ofList [0x1f]) 3) (.ofList [0x1f]) = .ok ⟨[none, none, none], 3⟩
#guard run (header (body.push 0)) (body.push 0) = .error (.plain .trailingBytes)

private def shortValues : Bytes := .ofList (body.toList.take 21)
#guard run (header shortValues) shortValues = .error (.plain .truncated)
#guard run (header (.ofList [0xb2])) (.ofList [0xb2]) = .error (.levels .truncated)
#guard run (header body) shortValues = .error (.page (.payload .compressedSizeMismatch))
#guard run { header body with uncompressedSize := 21 } body = .error (.payload .outputSizeMismatch)
#guard run { header body with compressedSize := 2 ^ 31 } body = .error (.page .invalidPageSize)

#guard run { header body with kind := .dataV1 ⟨9, 5, 4, 3⟩ } body =
  .error (.page (.unsupportedEncoding 5))
#guard run { header body with kind := .dataV1 ⟨9, 0, 3, 3⟩ } body =
  .error (.page .unsupportedLevelEncoding)
#guard run { header body with kind := .dataV1 ⟨9, 0, 4, 4⟩ } body =
  .error (.page .unsupportedLevelEncoding)
#guard run { header body with kind := .dataV2 ⟨9, 4, 9, 0, 2, 0, false⟩ } body =
  .error .unsupportedPage
#guard run { header body with kind := .dictionary ⟨5, 0, none⟩ } body = .error .unsupportedPage
#guard run { header body with crc := some 0 } body = .error .crcUnsupported

#guard decodeInt32 .int32 schema 1 (header body) limits body = .error (.unsupportedCodec 1)
#guard decodeInt32 .int64 schema 0 (header body) limits body = .error .unsupportedSchema
#guard decodeInt32 .int32 ⟨0, 0⟩ 0 (header body) limits body = .error .unsupportedSchema
#guard decodeInt32 .int32 ⟨1, 1⟩ 0 (header body) limits body = .error .unsupportedSchema

#guard decodeInt32 .int32 schema 0 (header body) { limits with compressedBytes := 21 } body =
  .error (.page (.payload .compressedLimit))
#guard decodeInt32 .int32 schema 0 (header body) { limits with uncompressedBytes := 21 } body =
  .error (.page (.payload .outputLimit))
#guard decodeInt32 .int32 schema 0 (header body) { limits with levels := ⟨8, 2⟩ } body =
  .error (.page (.levels .countLimit))
#guard decodeInt32 .int32 schema 0 (header body) { limits with levels := ⟨9, 1⟩ } body =
  .error (.levels .byteLimit)

end Silmaril.Formats.Parquet.LegacyBitPackedV1
