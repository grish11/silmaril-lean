module

import Silmaril.Formats.Arrow.MixedFlat.File.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.File.Defs
import Silmaril.Formats.Arrow.MixedFlat.File.Fixture
meta import Silmaril.Formats.Arrow.MixedFlat.File.Fixture
import Silmaril.Formats.Arrow.MixedFlat.Stream.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture

open Silmaril Silmaril.Formats
open Arrow.MixedFlat.File Arrow.MixedFlat.File.Fixture

private inductive Values where
  | primitive (values : Arrow.Column)
  | binary (values : List (Option (List UInt8)))
  | text (values : List (Option String))
  deriving DecidableEq

private def observe (batch : Arrow.MixedFlat.Observed) : Nat × List (Arrow.MixedFlat.Field × Values) :=
  (batch.rowCount, batch.columns.map fun (field, column) =>
    (field, match column with
      | .primitive values => .primitive values
      | .binaryView values => .binary (values.map (·.map KBytes.toList))
      | .utf8View values => .text values))

private def fields : List Arrow.MixedFlat.Field :=
  [⟨"i", true, .primitive .int32⟩, ⟨"b", true, .view .binary⟩,
    ⟨"u", true, .primitive .utf8⟩, ⟨"v", true, .view .utf8⟩]

-- The file and stream fixtures were independently emitted and reopened by
-- PyArrow. Observe the same rows and fields while addressing the file out of order.
#guard Id.run do
  let .ok index := readIndex {} multi | return false
  let .ok sequential := Arrow.MixedFlat.Stream.read {} Arrow.MixedFlat.Stream.Fixture.multi
    | return false
  let .ok (some first) := index.readAt {} 0 | return false
  let .ok (some last) := index.readAt {} 2 | return false
  let .ok (some empty) := index.readAt {} 1 | return false
  let .ok none := index.readAt {} 3 | return false
  return decide (index.footer.fields = fields ∧ index.footer.blocks = indexBlocks ∧
    index.span.start = footerStart ∧ [first.rowCount, empty.rowCount, last.rowCount] = [4, 0, 2] ∧
    [observe first, observe empty, observe last] = sequential.batches.map (observe ∘ (·.observed)))

#guard Id.run do
  let .ok index := readIndex { batches := 0 } schemaOnly | return false
  let .ok none := index.readAt {} 0 | return false
  return decide (index.footer.fields = fields ∧ index.footer.blocks = [])

private def patch (bytes : KBytes) (offset width value : Nat) : KBytes :=
  bytes.slice 0 offset ++ .leaf width value ++ bytes.slice (offset + width) (bytes.len - (offset + width))

private def rejectsIndex (input : KBytes) (expected : Error) (limits : Arrow.Limits := {}) : Bool :=
  match readIndex limits input with
  | .error actual => decide (actual = expected)
  | .ok _ => false

private def rejectsThird (input : KBytes) (expected : BlockError)
    (limits : Arrow.MixedFlat.Limits := {}) : Bool := Id.run do
  let .ok index := readIndex {} input | return false
  let .ok (some first) := index.readAt {} 0 | return false
  let .ok (some empty) := index.readAt {} 1 | return false
  let .ok none := index.readAt limits 3 | return false
  let .error failure := index.readAt limits 2 | return false
  return decide (failure = .batch 2 expected ∧ first.rowCount = 4 ∧ empty.rowCount = 0)

#guard rejectsIndex (patch multi lastBlockSlot 8 1248) .blockLayout
#guard rejectsIndex (patch multi (lastBlockSlot + 16) 8 144) .blockLayout
#guard rejectsIndex (patch multi lastBlockSlot 8 (2^63)) (.footer (.malformed .flatbuffer))
#guard rejectsIndex (patch multi (multi.len - 10) 4 (2^31)) (.footer (.malformed .metadataLength))
#guard rejectsIndex (patch multi footerFieldName 1 106) .schemaMismatch
#guard rejectsIndex (patch multi (footerStart - 4) 4 8) (.eos (.malformed .trailingBytes))
#guard rejectsIndex multi (.footer (.limit .batches)) { batches := 2 }

-- The block still ends at its original offset, so the index admits it
-- and the selected record check detects the inconsistent lengths.
#guard rejectsThird (patch (patch multi (lastBlockSlot + 8) 4 376) (lastBlockSlot + 16) 8 120) .metadataLength
#guard rejectsThird (patch multi lastBodyWord 8 120) .bodyLength
#guard rejectsThird multi (.decode (.body (.limit .totalRows))) { observation := { totalRows := 1 } }
