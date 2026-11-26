module

import Silmaril.Formats.Parquet.Snapshot.Thms
import Silmaril.Formats.Parquet.Page.Defs
import Silmaril.Formats.Parquet.ScalarPage.Defs
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Defs
meta import Silmaril.Formats.Parquet.Snapshot.Defs
meta import Silmaril.Formats.Parquet.Page.Defs
meta import Silmaril.Formats.Parquet.ScalarPage.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Defs

namespace Silmaril.Formats.Parquet.Snapshot

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Hive

-- One INT32 column in three groups, produced by PyArrow 26.0.1.
private def fixture : Bytes := Bytes.ofList [
  0x50, 0x41, 0x52, 0x31, 0x15, 0x00, 0x15, 0x1c, 0x15, 0x1c, 0x2c, 0x15, 0x04, 0x15,
  0x00, 0x15, 0x06, 0x15, 0x06, 0x1c, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x04,
  0x01, 0x0b, 0x00, 0x00, 0x00, 0x0c, 0x00, 0x00, 0x00, 0x15, 0x00, 0x15, 0x1c, 0x15,
  0x1c, 0x2c, 0x15, 0x04, 0x15, 0x00, 0x15, 0x06, 0x15, 0x06, 0x1c, 0x00, 0x00, 0x00,
  0x02, 0x00, 0x00, 0x00, 0x04, 0x01, 0x15, 0x00, 0x00, 0x00, 0x16, 0x00, 0x00, 0x00,
  0x15, 0x00, 0x15, 0x14, 0x15, 0x14, 0x2c, 0x15, 0x02, 0x15, 0x00, 0x15, 0x06, 0x15,
  0x06, 0x1c, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x02, 0x01, 0x1f, 0x00, 0x00,
  0x00, 0x15, 0x04, 0x19, 0x2c, 0x35, 0x00, 0x18, 0x06, 0x73, 0x63, 0x68, 0x65, 0x6d,
  0x61, 0x15, 0x02, 0x00, 0x15, 0x02, 0x25, 0x02, 0x18, 0x05, 0x76, 0x61, 0x6c, 0x75,
  0x65, 0x00, 0x16, 0x0a, 0x19, 0x3c, 0x19, 0x1c, 0x26, 0x00, 0x1c, 0x15, 0x02, 0x19,
  0x25, 0x06, 0x00, 0x19, 0x18, 0x05, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x15, 0x00, 0x16,
  0x04, 0x16, 0x42, 0x16, 0x42, 0x26, 0x08, 0x49, 0x1c, 0x15, 0x00, 0x15, 0x00, 0x15,
  0x02, 0x00, 0x3c, 0x29, 0x06, 0x19, 0x26, 0x00, 0x04, 0x00, 0x00, 0x00, 0x16, 0x42,
  0x16, 0x04, 0x26, 0x08, 0x16, 0x42, 0x00, 0x19, 0x1c, 0x26, 0x00, 0x1c, 0x15, 0x02,
  0x19, 0x25, 0x06, 0x00, 0x19, 0x18, 0x05, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x15, 0x00,
  0x16, 0x04, 0x16, 0x42, 0x16, 0x42, 0x26, 0x4a, 0x49, 0x1c, 0x15, 0x00, 0x15, 0x00,
  0x15, 0x02, 0x00, 0x3c, 0x29, 0x06, 0x19, 0x26, 0x00, 0x04, 0x00, 0x00, 0x00, 0x16,
  0x42, 0x16, 0x04, 0x26, 0x4a, 0x16, 0x42, 0x00, 0x19, 0x1c, 0x26, 0x00, 0x1c, 0x15,
  0x02, 0x19, 0x25, 0x06, 0x00, 0x19, 0x18, 0x05, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x15,
  0x00, 0x16, 0x02, 0x16, 0x3a, 0x16, 0x3a, 0x26, 0x8c, 0x01, 0x49, 0x1c, 0x15, 0x00,
  0x15, 0x00, 0x15, 0x02, 0x00, 0x3c, 0x29, 0x06, 0x19, 0x26, 0x00, 0x02, 0x00, 0x00,
  0x00, 0x16, 0x3a, 0x16, 0x02, 0x26, 0x8c, 0x01, 0x16, 0x3a, 0x00, 0x28, 0x20, 0x70,
  0x61, 0x72, 0x71, 0x75, 0x65, 0x74, 0x2d, 0x63, 0x70, 0x70, 0x2d, 0x61, 0x72, 0x72,
  0x6f, 0x77, 0x20, 0x76, 0x65, 0x72, 0x73, 0x69, 0x6f, 0x6e, 0x20, 0x32, 0x36, 0x2e,
  0x30, 0x2e, 0x31, 0x19, 0x1c, 0x1c, 0x00, 0x00, 0x00, 0xf6, 0x00, 0x00, 0x00, 0x50,
  0x41, 0x52, 0x31]

private abbrev Value (_ : Unit) := Int32
private def schema : Scan.Schema String Unit := ⟨1, fun _ => ("value", ())⟩

-- This fixture has exactly one optional INT32 V1 page per row group.
private def decodeFixture : DecodeGroup schema Value String := fun snapshot index group => do
  let spans : Array Footer.Span := #[⟨23, 37⟩, ⟨56, 70⟩, ⟨89, 99⟩]
  let some expected := spans[index]? | throw "unexpected fixture index"
  if snapshot.bytes ≠ fixture || snapshot.footer.start ≠ 99 then throw "unexpected fixture bytes"
  let [column] := group.columns | throw "expected one column"
  let some chunk := Page.columnSpan snapshot.footer.start column.metadata | throw "invalid chunk span"
  let [frame] ← (Page.readChunk { maxPages := 1 } snapshot.bytes chunk).mapError
    (fun _ => "invalid fixture page framing") | throw "expected one page"
  if frame.payload ≠ expected then throw "unexpected fixture body span"
  let .dataV1 header := frame.value.kind | throw "expected a V1 page"
  let some bytes := snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) |
    throw "invalid fixture slice"
  let params : ScalarPage.Parameters :=
    ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, ⟨0, 1⟩,
      header.numValues, column.metadata.codec, header.encoding,
      .v1 header.definitionLevelEncoding header.repetitionLevelEncoding⟩
  let limits : ScalarPage.Limits := ⟨14, 14, ⟨2, 2⟩, 0⟩
  let values ← (ScalarPage.decode .int32 params limits bytes).mapError fun _ => "invalid INT32 page"
  pure (values.map fun value _ => value)

private def bindFixture : Bind schema Value String := fun metadata => do
  let [_, column] := metadata.schema | throw "expected one column"
  if column.name = "value" && column.physicalType = some .int32 &&
      column.repetition = some .optional then pure decodeFixture
  else throw "unexpected fixture schema"

private def observe (limits : Limits) (bind : Bind schema Value String) (fuel : Nat) (bytes : Bytes) :
    Except (Error String) (List (List (Option Int32)) × Events.Termination (Error String)) :=
  ((batchReader limits bind).read fuel bytes).map fun ⟨_, trace⟩ =>
    (trace.rows.map List.ofFn, trace.termination)

private def indexFacts (bytes : Bytes) : Except (Error String) (List (Nat × Int) × Footer.Span) :=
  (check {} bytes).map fun snapshot =>
    ((List.range snapshot.groupCount).filterMap fun index =>
      (snapshot.groupAt index).map fun group => (index, group.numRows), snapshot.footer)

#guard indexFacts fixture = .ok ([(0, 2), (1, 2), (2, 1)], ⟨99, 345⟩)
#guard ((check {} fixture).bind fun snapshot =>
  (snapshot.readGroup decodeFixture 3).map List.length) = .error (.groupIndex 3)
#guard observe {} bindFixture 4 fixture =
  .ok ([[some 11], [some 12], [some 21], [some 22], [some 31]], .eos)
#guard observe {} bindFixture 0 fixture = .ok ([], .closed)
#guard observe {} bindFixture 1 fixture = .ok ([[some 11], [some 12]], .closed)
#guard observe {} bindFixture 3 fixture =
  .ok ([[some 11], [some 12], [some 21], [some 22], [some 31]], .closed)
#guard observe {} bindFixture 4 .empty = .error (.footer (.framing .shortFile))
#guard observe { maxSchemaDepth := 1 } bindFixture 4 fixture = .error (.invalidMetadata .schemaDepth)
#guard observe {} (fun _ => .error "wrong type") 4 fixture = .error (.schema "wrong type")

private def failMiddle : DecodeGroup schema Value String := fun snapshot index group =>
  if index = 1 then .error "middle group"
  else if index = 2 then .error "later group"
  else decodeFixture snapshot index group

#guard observe {} (fun _ => .ok failMiddle) 4 fixture =
  .ok ([[some 11], [some 12]], .readError (.decode 1 "middle group"))
#guard observe {} (fun _ => .ok fun _ _ _ => .ok []) 4 fixture =
  .ok ([], .readError (.rowCount 0 2 0))

private def partitions : TypedPartitions.PartitionSchema Unit := ⟨#[⟨"year", (), .reject⟩]⟩

private def convert : TypedPartitions.Convert Value String := fun _ text =>
  match text.toInt? with
  | none => .error "invalid year"
  | some year => .ok (Int32.ofInt year)

private def manifest (paths : List String) := Manifest.prepare schema partitions {} convert paths

private def fromPath : String → Except String Bytes
  | "year=%37/a.parquet" | "year=8/b.parquet" => .ok fixture
  | "year=8/malformed.parquet" => .ok .empty
  | _ => .error "snapshot missing"

private def scan (paths : List String) :
    Option (List (List (Option Int32)) × Events.Termination (Manifest.FileError (Error String))) :=
  (manifest paths).toOption.map fun files =>
    let opener := Manifest.snapshotOpener {} fromPath bindFixture
    let projection := Scan.Projection.ofArray (#[1, 0] : Array (Fin 2))
    let trace := Manifest.scan opener projection (fun _ => some true) files
    (trace.rows.map List.ofFn, trace.termination)

private def rowsFor (year : Int32) : List (List (Option Int32)) :=
  ([11, 12, 21, 22, 31] : List Int32).map fun value => [some year, some value]

#guard scan ["year=%37/a.parquet", "year=8/b.parquet", "year=%37/a.parquet"] =
  some (rowsFor 7 ++ rowsFor 8 ++ rowsFor 7, .eos)
#guard scan ["year=%37/a.parquet", "year=8/missing.parquet", "year=8/b.parquet"] =
  some (rowsFor 7, .readError (.open "year=8/missing.parquet" (.input "snapshot missing")))
#guard scan ["year=%37/a.parquet", "year=8/malformed.parquet", "year=8/b.parquet"] =
  some (rowsFor 7, .readError (.open "year=8/malformed.parquet" (.footer (.framing .shortFile))))

#print axioms Checked.readGroup_ok_iff
#print axioms Checked.collect_readAll_success
#print axioms Checked.collect_readAll_eof
#print axioms Checked.collect_readAll_first_error

end Silmaril.Formats.Parquet.Snapshot
