module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull.Defs
import Silmaril.Formats.Arrow.MixedFlat.File.Fixture
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.File.Fixture

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational
open MixedFlat.File.Events MixedFlat.File.Fixture

namespace Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull

private inductive Value where
  | primitive (value : Arrow.Value)
  | binaryView (octets : List UInt8)
  | utf8View (value : String)
  deriving DecidableEq

private def observe : Cell → Value
  | .primitive payload => .primitive payload
  | .binaryView payload => .binaryView payload.toList
  | .utf8View payload => .utf8View payload

private def rowsAndColumns {signature : Scan.Schema MixedFlat.Field Unit}
    (batch : Batch signature) : Nat × List (MixedFlat.Field × List (Option Value)) :=
  (batch.rowCount, List.ofFn fun i => ((signature.kind i).1, (batch.values i).map (Option.map observe)))

private def agrees (input : KBytes) (counts : List Nat) : Bool := Id.run do
  let .ok ⟨source, eager⟩ := MixedFlat.File.Events.read {} input | return false
  let .ok ⟨opened, drained⟩ := readAll {} input | return false
  return decide (List.ofFn (fun i => source.kind i) = List.ofFn (fun i => opened.kind i) ∧
    drained.termination = .eos ∧ drained.batches.map AlignedColumns.rowCount = counts ∧
    drained.batches.map rowsAndColumns = eager.batches.map rowsAndColumns)

#guard agrees multi [4, 0, 2]
#guard agrees schemaOnly []

private def zeroColumns : KBytes :=
  let bytes := include_bytes "../../../../../../../tests/formats/arrow-ipc/file-zero-columns.arrow"
  .leaf bytes.size (KBytes.leVal bytes.data.toList)

#guard agrees zeroColumns [3, 0]

private def damaged : KBytes :=
  let tail := lastBodyWord + 8
  multi.slice 0 lastBodyWord ++ .leaf 8 120 ++ multi.slice tail (multi.len - tail)

-- Open admits the footer independently of damage in a later wire record.
#guard Id.run do
  let pull := reader {}
  let .ok ⟨_, cursor⟩ := pull.openInput damaged | return false
  let .ok (some (first, cursor)) := pull.next cursor | return false
  let .ok (some (empty, cursor)) := pull.next cursor | return false
  let .error (.file (.batch 2 .bodyLength)) := pull.next cursor | return false
  let .ok ⟨_, eager⟩ := MixedFlat.File.Events.read {} multi | return false
  return decide ([first.rowCount, empty.rowCount] = [4, 0] ∧
    [rowsAndColumns first, rowsAndColumns empty] = (eager.batches.take 2).map rowsAndColumns)

private def retainsPrefix (input : KBytes) (limits : MixedFlat.Limits) (error : Error) : Bool := Id.run do
  let .ok ⟨_, trace⟩ := readAll limits input | return false
  let .ok ⟨_, control⟩ := MixedFlat.File.Events.read {} multi | return false
  return decide (trace.termination = .readError error ∧
    trace.batches.map rowsAndColumns = (control.batches.take 2).map rowsAndColumns)

#guard retainsPrefix damaged {} (.file (.batch 2 .bodyLength))
#guard retainsPrefix multi { observation := { totalRows := 5 } } (.budget 2 (.limit .totalRows))
#guard retainsPrefix multi { observation := { totalCells := 20 } } (.budget 2 (.limit .totalCells))

-- The generic driver spends one call for the empty batch and one for EOS.
#guard Id.run do
  let .ok ⟨_, trace⟩ := (reader {}).read 3 multi | return false
  return decide (trace.batches.map AlignedColumns.rowCount = [4, 0, 2] ∧
    trace.termination = .closed)

end Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull
