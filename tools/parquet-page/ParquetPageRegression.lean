module

import Silmaril.Formats.Parquet.Page.Defs
import Silmaril.Formats.Parquet.Footer.Defs
import Silmaril.Data.IncludeBytes
import Batteries.Data.Except

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Page

private def assertThat (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError name)

private def success {α ε : Type} [Repr ε] (label : String) (answer : Except ε α) : IO α :=
  match answer with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {repr error}")

private def syntheticV2 : Bytes := .ofList [
  0x15, 6, 0x15, 8, 0x15, 8, 0x5c,
  0x15, 8, 0x15, 2, 0x15, 8, 0x15, 0, 0x15, 2, 0x15, 2, 0x12, 0, 0,
  0xaa, 0xbb, 0xcc, 0xdd]

private def synthetic : IO Unit := do
  let whole : Footer.Span := ⟨0, syntheticV2.length⟩
  let frame ← success "synthetic V2" (readPage {} syntheticV2 whole 0)
  assertThat "exact header and payload" (frame.header == ⟨0, 22⟩ && frame.payload == ⟨22, 26⟩)
  assertThat "V2 level and value spans" (frame.v2Spans == some ⟨⟨22, 23⟩, ⟨23, 24⟩, ⟨24, 26⟩⟩)
  assertThat "inline false compression flag and exact prefix" (readHeaderPrefix {} syntheticV2 ==
    .ok (⟨4, 4, none, .dataV2 ⟨4, 1, 4, 0, 1, 1, false⟩⟩, 22))
  assertThat "declared chunk cuts the payload" (readPage {} syntheticV2 ⟨0, 25⟩ 0 == .error .payloadBounds)
  assertThat "declared chunk cuts the STOP" (readPage {} syntheticV2 ⟨0, 21⟩ 0 ==
    .error (.header (.traversal (.compact .truncated))))
  assertThat "header cap" (readPage {maxHeaderBytes := 20} syntheticV2 whole 0 ==
    .error (.header (.traversal (.compact .truncated))))
  assertThat "bad cursor" (readPage {} syntheticV2 whole 26 == .error .cursorBounds)
  assertThat "chunk exceeds file" (readChunk {} syntheticV2 ⟨0, 27⟩ == .error .chunkBounds)
  assertThat "page count cap" (readChunk {maxPages := 0} syntheticV2 whole == .error .pageLimit)
  let padded := syntheticV2.push 0
  assertThat "chunk must end on a page boundary" (readChunk {} padded ⟨0, padded.length⟩ ==
    .error (.header (.missingField 1)))
  assertThat "empty chunk" (readChunk {maxPages := 0} syntheticV2 ⟨26, 26⟩ == .ok [])
  let short := fun octets => readHeaderPrefix {} (.ofList octets)
  assertThat "negative compressed length" (short [0x15, 8, 0x15, 0, 0x15, 1, 0] ==
    .error (.negativeField 3))
  assertThat "missing required field" (short [0x15, 8, 0x15, 0, 0] == .error (.missingField 3))
  assertThat "duplicate required field" (short [0x15, 8, 0x05, 2, 8, 0] == .error (.duplicateField 1))
  assertThat "wrong wire type" (short [0x16, 8, 0] == .error (.fieldType 1 (.payload .i64)))
  assertThat "invalid V2 level length" (readHeaderPrefix {}
    ⟨(syntheticV2.data.extract 0 16).push 10 ++ syntheticV2.data.extract 17 26⟩ == .error .invalidV2Lengths)
  assertThat "invalid V2 counts" (readHeaderPrefix {}
    ⟨(syntheticV2.data.extract 0 10).push 10 ++ syntheticV2.data.extract 11 26⟩ == .error .invalidV2Counts)
  assertThat "conflicting page detail" (short [0x15, 2, 0x15, 0, 0x15, 0, 0x3c, 0, 0x1c, 0, 0] ==
    .error (.conflictingKind 1))
  let skipped : Bytes := .ofList [
    0x15, 2, 0x15, 2, 0x15, 2, 0x3c, 0, 0, 0xff,
    0x15, 8, 0x15, 0, 0x15, 0, 0x15, 1, 0x68, 2, 0, 0xff, 0]
  let frames ← success "skipped page kinds" (readChunk {} skipped ⟨0, skipped.length⟩)
  assertThat "index and unknown advance, CRC retains bits" (frames == [
    ⟨⟨1, 1, none, .skipped .indexPage⟩, ⟨0, 9⟩, ⟨9, 10⟩⟩,
    ⟨⟨0, 0, some 0xffffffff, .skipped (.unknown 4)⟩, ⟨10, 23⟩, ⟨23, 23⟩⟩])

private def allTypes : Bytes := ⟨include_bytes "../parquet-footer/fixtures/alltypes_plain.parquet"⟩
private def v2Snappy : Bytes := ⟨include_bytes "fixtures/datapage_v2.snappy.parquet"⟩

private def readColumns (file : Bytes) : IO (List (List Frame)) := do
  let (span, metadata) ← success "fixture footer" (Footer.readFooter {} file)
  let [group] := metadata.rowGroups | throw (IO.userError "expected one fixture row group")
  group.columns.mapM fun column => do
    let some chunk := columnSpan span.start column.metadata | throw (IO.userError "fixture column bounds")
    success (String.intercalate "." column.metadata.pathInSchema) (readChunk {} file chunk)

private def offsets (columns : List (List Frame)) : List (List (Nat × Nat × Nat)) :=
  columns.map (List.map fun frame => (frame.header.start, frame.payload.start, frame.payload.stop))

private def fixtures : IO Unit := do
  let plain ← readColumns allTypes
  assertThat "all V1 and dictionary offsets" (offsets plain == [
    [(4,17,49), (49,66,77)], [(109,126,133)], [(168,181,189), (189,206,215)],
    [(256,269,277), (277,294,303)], [(345,358,366), (366,383,392)],
    [(429,442,458), (458,475,484)], [(524,537,545), (545,562,571)],
    [(610,623,639), (639,656,665)], [(705,718,766), (766,783,793)],
    [(840,853,863), (863,880,889)], [(929,944,1040), (1040,1057,1068)]])
  assertThat "pinned dictionary and V1 metadata" (plain.head?.map (List.map (·.value)) == some [
    ⟨32, 32, none, .dictionary ⟨8, 2, none⟩⟩,
    ⟨11, 11, none, .dataV1 ⟨8, 2, 3, 4⟩⟩])
  let v2 ← readColumns v2Snappy
  assertThat "all V2 and dictionary offsets" (offsets v2 == [
    [(4,17,26), (26,61,67)], [(67,104,116)], [(116,129,153), (153,198,204)],
    [(204,235,243)], [(243,256,270), (270,307,321)]])
  let some frame := v2.getLast?.bind List.getLast? | throw (IO.userError "expected nested V2 page")
  assertThat "nested V2 metadata and on-disk sections" (
    frame.value == ⟨12, 14, none, .dataV2 ⟨10, 2, 5, 8, 5, 3, true⟩⟩ &&
    frame.v2Spans == some ⟨⟨307, 310⟩, ⟨310, 315⟩, ⟨315, 321⟩⟩)

public def main : IO Unit := do
  synthetic
  fixtures
  IO.println "Parquet page framing: 29 pinned dictionary/V1/V2 pages and negative cases passed"
