module

import Silmaril.Formats.Arrow.MixedFlat.File.Window.Projection.Defs
import Silmaril.Formats.Arrow.MixedFlat.File.Fixture
meta import Silmaril.Formats.Arrow.MixedFlat.File.Window.Projection.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.File.Fixture

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.File.Window MixedFlat.File.Fixture

private inductive Values where
  | primitive (values : Arrow.Column)
  | binary (values : List (Option (List UInt8)))
  | text (values : List (Option String))
  deriving DecidableEq

private def observe (column : MixedFlat.Field × MixedFlat.Column) : MixedFlat.Field × Values :=
  (column.1, match column.2 with
    | .primitive slots => .primitive slots
    | .binaryView slots => .binary (slots.map (Option.map KBytes.toList))
    | .utf8View slots => .text slots)

private def agrees (input : KBytes) (positions rowCounts : List Nat) : Bool := Id.run do
  let .ok strict := MixedFlat.File.readIndex {} input | return false
  let .ok window := readIndex {} input 0 input.len | return false
  let .ok batches := strict.footer.blocks.mapM
    (MixedFlat.File.readRecord {} input strict.footer.fields) | return false
  let some projection := window.checkProjection positions | return false
  let .ok none := window.readProjectedAt {} batches.length projection | return false
  return decide (strict.footer = window.footer ∧ batches.map MixedFlat.Observed.rowCount = rowCounts) &&
    (List.range batches.length).all fun n => Id.run do
      let some batch := batches[n]? | return false
      let some expected := positions.mapM (fun i => batch.columns[i]?) | return false
      let .ok (some selected) := window.readProjectedAt {} n projection | return false
      return decide (selected.rowCount = batch.rowCount ∧
        selected.columns.map observe = expected.map observe)

#guard agrees multi [3, 0, 3, 1] [4, 0, 2]
#guard agrees multi [] [4, 0, 2]
#guard agrees (multi ++ KBytes.empty) [3, 0, 3, 1] [4, 0, 2]
#guard agrees schemaOnly [3, 0, 3, 1] []

-- The embedded schema and footer still admit the index. The first record
-- fails during traversal, and the last record remains independently readable.
#guard Id.run do
  let firstPrefix := 264
  let pastPrefix := firstPrefix + 4
  let damaged := multi.slice 0 firstPrefix ++ .leaf 4 0 ++ multi.slice pastPrefix (multi.len - pastPrefix)
  let .ok strict := MixedFlat.File.readIndex {} damaged | return false
  let .ok window := readIndex {} damaged 0 damaged.len | return false
  let .error (.envelope (.malformed .continuation)) := strict.footer.blocks.mapM
    (MixedFlat.File.readRecord {} damaged strict.footer.fields) | return false
  let some projection := window.checkProjection [1] | return false
  let .error (.file (.batch 0 (.envelope (.malformed .continuation)))) :=
    window.readProjectedAt {} 0 projection | return false
  let .ok (some suffix) := window.readProjectedAt {} 2 projection | return false
  return decide (suffix.rowCount = 2 ∧ suffix.columns.map observe =
    [(⟨"b", true, .view .binary⟩, .binary [some [], some [255]])])
