module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Arrow.MixedFlat.File.Events.Defs
import Silmaril.Formats.Arrow.MixedFlat.File.Window.Projection.Defs
import Silmaril.Formats.Arrow.MixedFlat.File.Fixture
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Arrow.MixedFlat.File.Events.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.File.Window.Projection.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.File.Fixture

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational
open MixedFlat.File.Fixture

namespace Silmaril.Formats.Arrow.MixedFlat.File.Events

private inductive Value where
  | primitive (value : Arrow.Value)
  | binaryView (octets : List UInt8)
  | utf8View (value : String)
  deriving DecidableEq

private def value : Cell → Value
  | .primitive payload => .primitive payload
  | .binaryView payload => .binaryView payload.toList
  | .utf8View payload => .utf8View payload

private def expected : List MixedFlat.Field :=
  [⟨"i", true, .primitive .int32⟩, ⟨"b", true, .view .binary⟩,
    ⟨"u", true, .primitive .utf8⟩, ⟨"v", true, .view .utf8⟩]

private def agrees (input : KBytes) (fields : List MixedFlat.Field) (positions counts : List Nat) :
    Bool := Id.run do
  let .ok ⟨source, trace⟩ := read {} input | return false
  let .ok window := MixedFlat.File.Window.readIndex {} input 0 input.len | return false
  let some selection := window.checkProjection positions | return false
  let some indices := positions.mapM (fun i =>
    if valid : i < source.width then some (⟨i, valid⟩ : Fin source.width) else none) | return false
  let projection := Scan.Projection.ofArray indices.toArray
  let projected := trace.scan projection (fun _ => some true)
  let .ok none := window.readProjectedAt {} counts.length selection | return false
  return decide (List.ofFn (fun i => (source.kind i).1) = fields ∧
      projected.termination = .eos ∧ projected.batches.map AlignedColumns.rowCount = counts) &&
    (List.range counts.length).all fun n => Id.run do
      let some event := projected.batches[n]? | return false
      let .ok (some selected) := window.readProjectedAt {} n selection | return false
      let labelled := List.ofFn fun i : Fin projection.width =>
        ((projection.schema.kind i).1, (event.values i).map (Option.map value))
      return decide (selected.rowCount = event.rowCount ∧
        selected.columns.map (fun (field, column) => (field, (cells column).map (Option.map value))) =
          labelled)

#guard agrees multi expected [3, 0, 3, 1] [4, 0, 2]
#guard agrees multi expected [0, 1, 2, 3] [4, 0, 2]
#guard agrees multi expected [] [4, 0, 2]
#guard agrees schemaOnly expected [3, 0, 3, 1] []

private def zeroColumns : KBytes :=
  let bytes := include_bytes "../../../../../../tests/formats/arrow-ipc/file-zero-columns.arrow"
  .leaf bytes.size (KBytes.leVal bytes.data.toList)

#guard agrees zeroColumns [] [] [3, 0]

#guard match read { observation := { totalRows := 5 } } multi with
  | .error (.budget 2 (.limit .totalRows)) => true
  | _ => false

#guard match read { observation := { totalCells := 20 } } multi with
  | .error (.budget 2 (.limit .totalCells)) => true
  | _ => false

-- A late wire failure is atomic even when the first two batches are readable.
#guard Id.run do
  let tail := lastBodyWord + 8
  let damaged := multi.slice 0 lastBodyWord ++ .leaf 8 120 ++ multi.slice tail (multi.len - tail)
  let .ok index := MixedFlat.File.readIndex {} damaged | return false
  let .ok (some first) := index.readAt {} 0 | return false
  let .ok (some empty) := index.readAt {} 1 | return false
  let .error (.file (.batch 2 .bodyLength)) := read {} damaged | return false
  return first.rowCount == 4 && empty.rowCount == 0

end Silmaril.Formats.Arrow.MixedFlat.File.Events
