module

import Silmaril.Formats.Arrow.MixedFlat.Stream.Events.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Events.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational
open MixedFlat.Events MixedFlat.Stream.Fixture

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Events

private inductive Value where
  | primitive (value : Arrow.Value)
  | binaryView (octets : List UInt8)
  | utf8View (value : String)
  deriving DecidableEq

private def observe : Cell → Value
  | .primitive payload => .primitive payload
  | .binaryView payload => .binaryView payload.toList
  | .utf8View payload => .utf8View payload

private def eventColumns {signature : Scan.Schema MixedFlat.Field Unit} (batch : MixedFlat.Events.Batch signature) :
    List (MixedFlat.Field × List (Option Value)) :=
  List.ofFn fun i => ((signature.kind i).1, (batch.values i).map (Option.map observe))

private def strictColumns (observed : MixedFlat.Observed) :
    List (MixedFlat.Field × List (Option Value)) :=
  observed.columns.map fun (field, column) => (field, (cells column).map (Option.map observe))

private def agrees (input : KBytes) (counts : List Nat) (limits : MixedFlat.Limits := {}) :
    Bool := Id.run do
  let .ok eager := Stream.read limits input | return false
  let .ok ⟨signature, trace⟩ := readAll limits input | return false
  return decide (List.ofFn (fun i => (signature.kind i).1) = eager.fields ∧
    trace.termination = .eos ∧ trace.batches.map AlignedColumns.rowCount = counts ∧
    trace.batches.map eventColumns = eager.batches.map (strictColumns ∘ (·.observed)))

#guard agrees multi [4, 0, 2]
#guard agrees schemaOnly [] { observation := { ipc := { batches := 0 }, totalRows := 0 } }
#guard agrees zeroColumns [3, 0] { observation := { totalCells := 0 } }

private def stops (input : KBytes) (counts : List Nat) (error : Error)
    (limits : MixedFlat.Limits := {}) : Bool := Id.run do
  let .ok ⟨signature, trace⟩ := readAll limits input | return false
  let .ok expected := Stream.read {} multi | return false
  let .error eager := Stream.read limits input | return false
  return decide (List.ofFn (fun i => (signature.kind i).1) = expected.fields ∧ eager = error.eager ∧
    trace.termination = .readError error ∧ trace.batches.map AlignedColumns.rowCount = counts ∧
    trace.batches.map eventColumns = (expected.batches.take counts.length).map (strictColumns ∘ (·.observed)))

#guard stops lateTruncated [4, 0] (.message 2 lastRecordOffset (.body (.malformed .truncated)))
#guard stops (multi.slice 0 (lastRecordOffset + 9)) [4, 0]
  (.message 2 lastRecordOffset (.envelope (.malformed .truncated)))
#guard stops (multi.slice 0 multiEos) [4, 0, 2] (.message 3 multiEos (.envelope (.malformed .truncated)))
#guard stops (multi ++ .leaf 1 0) [4, 0, 2] (.message 3 multiEos .trailingBytes)
#guard stops multi [4, 0] (.message 2 lastRecordOffset .batchLimit)
  { observation := { ipc := { batches := 2 } } }
#guard stops multi [4, 0] (.message 2 lastRecordOffset (.budget (.limit .totalRows)))
  { observation := { totalRows := 5 } }
#guard stops multi [4, 0] (.message 2 lastRecordOffset (.budget (.limit .totalCells)))
  { observation := { totalCells := 20 } }
#guard stops multi [] (.message 0 (8 + multiSchemaSize) (.envelope (.limit .metadataBytes)))
  { observation := { ipc := { metadataBytes := 300 } } }
#guard stops multi [] (.message 0 (8 + multiSchemaSize) (.body (.limit .bodyBytes)))
  { observation := { ipc := { bodyBytes := 0 } } }

-- The first two records are delivered before the third body's truncation is observed.
#guard Id.run do
  let pull := reader {}
  let .ok ⟨_, opened⟩ := pull.openInput lateTruncated | return false
  let .ok (some (first, next)) := pull.next opened | return false
  let .ok (some (empty, next)) := pull.next next | return false
  let .error (.message 2 offset (.body (.malformed .truncated))) := pull.next next | return false
  return decide ([first.rowCount, empty.rowCount] = [4, 0] ∧ offset = lastRecordOffset)

end Silmaril.Formats.Arrow.MixedFlat.Stream.Events
