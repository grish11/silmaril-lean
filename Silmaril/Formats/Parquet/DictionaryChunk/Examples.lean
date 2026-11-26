module

import Silmaril.Formats.Parquet.DictionaryChunk.Thms
import Silmaril.Data.IncludeBytes
import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.DictionaryChunk.Defs

/-! Whole-file fixtures from parquet-java 1.16.0 and PyArrow 26.0.1. -/

namespace Silmaril.Formats.Parquet.DictionaryChunk

set_option maxRecDepth 4096

private def arrowV1 : Bytes := ⟨include_bytes "../../../../data/parquet-dictionary-chunk/arrow-v1.parquet"⟩
private def arrowV2 : Bytes := ⟨include_bytes "../../../../data/parquet-dictionary-chunk/arrow-v2.parquet"⟩
private def javaV1 : Bytes := ⟨include_bytes "../../../../data/parquet-dictionary-chunk/java-v1.parquet"⟩
private def javaV2 : Bytes := ⟨include_bytes "../../../../data/parquet-dictionary-chunk/java-v2.parquet"⟩

private def arrowCell (row column : Nat) : Option Int32 :=
  if column = 0 then
    let value := row / 24 * 100 + if row % 24 < 8 then row % 3 else row % 24
    some (Int32.ofInt value)
  else if row < 24 || row % 4 == 0 then none
  else some (Int32.ofInt (-9 + 7 * Int.ofNat (row % 5)))

private def javaCell (row column : Nat) : Option Int32 :=
  if column = 0 then some (Int32.ofInt (17 - 11 * Int.ofNat (row % 3)))
  else if row % 4 = 0 then none
  else some (Int32.ofInt (-9 + 7 * Int.ofNat (row % 5)))

private def observed (name : String) (index : Nat) (field : FlatScan.Field) (chunk : Chunk) : String :=
  let windows := chunk.frames.map fun f => s!"{f.header.start}:{f.payload.start}:{f.payload.stop}"
  let entries := chunk.dictionary.toList.flatMap fun d => d.entries.toList
  String.intercalate "\t" [name, toString index, field.name, String.intercalate "," windows,
    String.intercalate "," (entries.map toString),
    String.intercalate "," (chunk.data.map fun p => toString p.params.encoding),
    String.intercalate "," (chunk.data.map fun p => toString p.params.numValues)] ++ "\n"

private def checkFile (name : String) (source : Bytes) (cell : Nat → Nat → Option Int32) :
    Except String String := do
  let (footer, metadata) ← (Footer.readFooter {} source).mapError reprStr
  let fields ← (FlatScan.flatSchema (ε := Unit) {} metadata.schema).mapError reprStr
  let mut rowStart := 0
  let mut output := ""
  for (group, index) in metadata.rowGroups.zipIdx do
    let rows := group.numRows.toNat
    if group.columns.length != fields.length then throw "column count"
    for ((field, column), colIndex) in (fields.zip group.columns).zipIdx do
      let chunk ← (DictionaryChunk.read {} source footer.start field rows column.metadata).mapError reprStr
      let slots ← (scanColumn {} source footer.start field rows column.metadata).mapError reprStr
      if slots != (List.range rows).map (fun row => cell (rowStart + row) colIndex) then
        throw s!"{name}: wrong slot at {index}/{field.name}"
      output := output ++ observed name index field chunk
    rowStart := rowStart + rows
  pure output

private def observeFixtures : Except String String := do
  let av1 ← checkFile "arrow-v1.parquet" arrowV1 arrowCell
  let av2 ← checkFile "arrow-v2.parquet" arrowV2 arrowCell
  let jv1 ← checkFile "java-v1.parquet" javaV1 javaCell
  let jv2 ← checkFile "java-v2.parquet" javaV2 javaCell
  return av1 ++ av2 ++ jv1 ++ jv2

#guard observeFixtures = .ok (include_str "../../../../data/parquet-dictionary-chunk/windows.tsv")

private def requiredField : FlatScan.Field := ⟨"required_i32", .required⟩

private def frameBytes (frame : Page.Frame) : Bytes :=
  Footer.fileBytes arrowV2 frame.header.start frame.payload.stop

private def reordered (frames : List Page.Frame) : Bytes :=
  (Bytes.ofList [80, 65, 82, 49]).append (Bytes.ofList (frames.flatMap fun f => (frameBytes f).toList))

private def checkAdmission : Except String Unit := do
  let (footer, metadata) ← (Footer.readFooter {} arrowV2).mapError reprStr
  let some column := metadata.rowGroups.head?.bind (fun g => g.columns.head?.map (·.metadata)) |
    throw "missing test column"
  let readAt (limits : Limits) (source : Bytes) (metadata : Footer.ColumnMetadata) :=
    (DictionaryChunk.read limits source footer.start requiredField 24 metadata).map (fun _ => ())
  let expect (observed : Except Error Unit) (reason : Error) : Except String Unit :=
    if observed = .error reason then .ok () else throw s!"wanted {reprStr reason}, got {reprStr observed}"
  expect (readAt { maxEntries := 10 } arrowV2 column) .entryLimit
  expect (readAt { maxDictionaryBytes := 43 } arrowV2 column) .dictionaryByteLimit
  expect (readAt { maxRows := 23 } arrowV2 column) .rowLimit
  expect (readAt { page.maxPages := 3 } arrowV2 column) (.page .pageLimit)
  expect (readAt {} arrowV2 { column with codec := 1 }) .columnCodec
  expect (readAt {} arrowV2 { column with physicalType := .int64 }) .columnType
  expect (readAt {} arrowV2 { column with dataPageOffset := column.dataPageOffset + 1 }) .dataOffset
  expect (readAt {} arrowV2 { column with numValues := 23 }) .rowCount
  expect (readAt {} arrowV2 { column with totalCompressedSize := column.totalCompressedSize - 1 })
    (.page .payloadBounds)
  -- The first dictionary's count at byte 12 is zigzag 11. Claim 10 without changing the body.
  expect (readAt {} ⟨arrowV2.data.set! 12 20⟩ column) (.dictionaryBody .trailingBytes)
  expect (readAt {} ⟨arrowV2.data.set! 12 24⟩ column) (.dictionaryBody .truncated)
  let chunk ← (DictionaryChunk.read {} arrowV2 footer.start requiredField 24 column).mapError reprStr
  let [dictionary, first, second, plain] := chunk.frames | throw "wrong test page sequence"
  let readReordered (source : Bytes) (dictionaryOffset : Option Int) (dataOffset : Int) (rows : Nat) :=
    (DictionaryChunk.read {} source source.length requiredField rows { column with
      dictionaryPageOffset := dictionaryOffset, dataPageOffset := dataOffset,
      totalCompressedSize := (source.length : Int) - 4, numValues := rows }).map (fun _ => ())
  expect (readReordered (reordered [dictionary, first, dictionary, second, plain]) (some 4) 62 24)
    .misplacedDictionary
  expect (readReordered (reordered [plain, dictionary]) none 4 8) .misplacedDictionary
  expect (readReordered (reordered [dictionary, first, second, plain]) none 4 24) .dictionaryOffset
  expect (readReordered (reordered [first, second, plain]) (some 4) 4 24) .dictionaryOffset
  expect (readReordered (reordered [first, second, plain]) none 4 24) .missingDictionary
  expect (readReordered (reordered [dictionary]) (some 4) 62 0) .dataOffset
  let plainOnly := reordered [plain]
  let plainMetadata := { column with
    dictionaryPageOffset := none
    dataPageOffset := 4
    totalCompressedSize := (plainOnly.length : Int) - 4
    numValues := 8 }
  let slots ← (scanColumn {} plainOnly plainOnly.length requiredField 8 plainMetadata).mapError reprStr
  if slots != (List.range 8).map (fun i => arrowCell (16 + i) 0) then throw "PLAIN-only slots"
  -- The caller's checked frame may retain CRC bits. Admission rejects them.
  let crc := { first with value.crc := some 0 }
  expect ((Internal.admitData {} .required chunk.dictionary crc).map (fun _ => ())) .crcUnsupported
  let corrupt := ⟨arrowV2.data.set! first.payload.start 33⟩
  expect ((scanColumn {} corrupt footer.start requiredField 24 column).map (fun _ => ()))
    (.dictionaryPage (.hybrid .invalidWidth))

#guard checkAdmission = .ok ()

end Silmaril.Formats.Parquet.DictionaryChunk
