module

import Silmaril.Formats.Arrow.FileReader.FooterOnly.Defs
meta import Silmaril.Formats.Arrow.FileReader.FooterOnly.Defs
import Silmaril.Formats.Arrow.FileReader.FooterOnly.Fixture
meta import Silmaril.Formats.Arrow.FileReader.FooterOnly.Fixture
import Silmaril.Formats.Arrow.FileWriter.Defs
meta import Silmaril.Formats.Arrow.FileWriter.Defs

open Silmaril Silmaril.Formats.Arrow
open FileReader.FooterOnly FileReader.FooterOnly.Fixture

private def fields : List Field := [⟨"signed", true, .int32⟩, ⟨"text", true, .utf8⟩]

private def firstRows : List Row :=
  [[some (.int32 (-7)), some (.utf8 "é")], [none, none],
    [some (.int32 42), some (.utf8 "")], [some (.int32 (-2147483648)), some (.utf8 "雪")]]

private def secondRows : List Row :=
  [[some (.int32 0), none], [some (.int32 2147483647), some (.utf8 "tail")]]

private def reads (input : KBytes) : Bool := Id.run do
  let .ok index := readIndex {} input | return false
  let .ok (some last) := index.readRowsAt {} 1 | return false
  let .ok (some first) := index.readRowsAt {} 0 | return false
  let .ok none := index.readRowsAt {} 2 | return false
  let .ok (some frame) := index.readBatchAt {} 1 | return false
  return decide (index.footer.fields = fields ∧
    index.footer.blocks = [⟨8, 208, 176⟩, ⟨392, 208, 96⟩] ∧
    index.span.start = 704 ∧ index.span.length = 248 ∧
    [first, last] = [firstRows, secondRows] ∧ frame.body.len = 96 ∧
    frame.body.toList = (input.toList.drop 600).take 96)

#guard reads multi
#guard [8, 16, 392, 600, 696, 704, 952].all fun split =>
  reads (multi.slice 0 split ++ multi.slice split (multi.len - split))

#guard Id.run do
  let .ok index := readIndex { batches := 0 } schemaOnly | return false
  let .ok none := index.readRowsAt {} 0 | return false
  let .ok .eos := readEnvelope {} schemaOnly 8 | return false
  return decide (index.footer.fields = fields ∧ index.footer.blocks = [] ∧ index.span.start = 16)

private def patch (input : KBytes) (offset width value : Nat) : KBytes :=
  input.slice 0 offset ++ .leaf width value ++
    input.slice (offset + width) (input.len - (offset + width))

private def rejects (input : KBytes) (error : Error) (limits : Limits := {}) : Bool :=
  match readIndex limits input with
  | .ok _ => false
  | .error actual => decide (actual = error)

#guard (List.range multi.len).all fun size => !(readIndex {} (multi.slice 0 size)).isOk
#guard rejects (patch multi 6 2 1) (.malformed .alignment)
#guard rejects (patch multi (multi.len - 10) 4 (2^31)) (.malformed .metadataLength)
#guard rejects (patch multi multiBlocks 8 16) (.malformed .batchLayout)
#guard rejects (patch multi (multiBlocks + 24) 8 400) (.malformed .batchLayout)
#guard rejects (patch multi (multiBlocks + 24) 8 384) (.malformed .batchLayout)
#guard rejects (patch multi (multiBlocks + 24) 8 8) (.malformed .batchLayout)
#guard rejects (patch multi (multiBlocks + 24) 8 (2^63)) (.malformed .flatbuffer)
#guard rejects (patch multi (multiBlocks + 8) 4 207) (.malformed .batchLayout)
#guard rejects (patch multi (multiBlocks + 40) 8 88) (.malformed .batchLayout)
#guard rejects (patch multi (multiBlocks + 40) 8 120) (.malformed .batchLayout)
#guard rejects (patch multi 696 4 0) (.malformed .continuation)
#guard rejects (patch multi 700 4 8) (.malformed .trailingBytes)
#guard rejects (patch schemaOnly 8 4 0) (.malformed .continuation)
#guard rejects multi (.limit .batches) { batches := 1 }
#guard rejects multi (.limit .metadataBytes) { metadataBytes := 247 }

-- Keep the overall second block extent, but make its two lengths disagree
-- with its message. Reading the first block still succeeds.
#guard Id.run do
  let malformed := patch (patch multi (multiBlocks + 32) 4 216) (multiBlocks + 40) 8 88
  let .ok index := readIndex {} malformed | return false
  let .ok (some first) := index.readRowsAt {} 0 | return false
  let .error (.malformed .metadataLength) := index.readRowsAt {} 1 | return false
  return decide (first = firstRows)

#guard rejects (patch multi 12 4 192) (.malformed .metadataLength)

-- Put a Schema inside the first indexed metadata extent. Neither a valid
-- Schema there nor a malformed one is admitted as the leading RecordBatch.
private def leadingSchema : KBytes :=
  let schema := MetadataWriter.Wire.schemaBytes [] 0
  multi.slice 0 16 ++ schema ++ KBytes.zeros (200 - schema.len) ++ multi.slice 216 (multi.len - 216)

#guard rejects leadingSchema (.malformed .schemaOrder)
#guard rejects (patch leadingSchema 16 4 0) (.malformed .flatbuffer)

#guard Id.run do
  let .error (.malformed .schemaOrder) := FileReader.readIndex {} multi | return false
  let .ok strict := FileWriter.emit {} fields [] | return false
  let .ok index := FileReader.readIndex {} strict | return false
  let .error (.malformed .flatbuffer) := FileReader.readIndex {} (patch strict 16 4 0) | return false
  return decide (index.footer.fields = fields) &&
    rejects strict (.malformed .batchLayout) && rejects (patch strict 16 4 0) (.malformed .batchLayout)
