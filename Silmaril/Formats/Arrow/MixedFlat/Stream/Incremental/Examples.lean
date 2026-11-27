module

import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
import Silmaril.Prelude.Bytes.Write.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
meta import Silmaril.Prelude.Bytes.Write.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational
open MixedFlat.Stream.Fixture

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental

private inductive Value where
  | primitive (value : Arrow.Value)
  | binaryView (octets : List UInt8)
  | utf8View (value : String)
  deriving DecidableEq

private def observe : MixedFlat.Events.Cell → Value
  | .primitive value => .primitive value
  | .binaryView value => .binaryView value.toList
  | .utf8View value => .utf8View value

private abbrev Columns := List (MixedFlat.Field × List (Option Value))

private structure Observation where
  range : Stream.BatchRange
  rows : Nat
  columns : Columns
  deriving DecidableEq

private def observeRecord (batch : Stream.Batch) : Observation :=
  ⟨batch.range, batch.observed.rowCount, batch.observed.columns.map fun (field, column) =>
    (field, (MixedFlat.Events.cells column).map (Option.map observe))⟩

private def observeEvent {signature : Scan.Schema MixedFlat.Field Unit}
    (batch : MixedFlat.Events.Batch signature) : Nat × Columns :=
  (batch.rowCount, List.ofFn fun i => ((signature.kind i).1, (batch.values i).map (Option.map observe)))

private inductive Terminal where
  | ok (last : Nat)
  | error (cause : Error)
  deriving DecidableEq

private def terminal : Except Error Nat → Terminal
  | .ok last => .ok last
  | .error cause => .error cause

private structure Trace where
  fields : Option (List MixedFlat.Field) := none
  batches : List Observation := []
  terminal : Option Terminal := none

private def pump : Nat → Cursor → KBytes → Trace → Cursor × Trace
  | 0, cursor, _, trace => (cursor, trace)
  | fuel + 1, cursor, chunk, trace =>
    match feed cursor chunk with
    | .error cause => (cursor, { trace with terminal := some (.error cause) })
    | .ok (.wait pending) => (pending, trace)
    | .ok (.advance pending rest) => pump fuel pending rest trace
    | .ok (.schema fields _ pending rest) => pump fuel pending rest { trace with fields := some fields }
    | .ok (.batch _ delivered pending rest) =>
      let (rows, columns) := observeEvent delivered.event
      pump fuel pending rest { trace with batches := ⟨delivered.record.range, rows, columns⟩ :: trace.batches }

private def collect : Cursor → Trace → List KBytes → Trace
  | cursor, trace, [] => { trace with terminal := trace.terminal.orElse (fun _ => some (terminal (finish cursor))) }
  | cursor, trace, chunk :: rest =>
    if trace.terminal.isSome then trace
    else
      let (pending, trace) := pump (3 * chunk.len + 8) cursor chunk trace
      collect pending trace rest

private def run (limits : Limits) (chunks : List KBytes) : Trace :=
  collect (start limits) {} chunks

private def agrees (input : KBytes) (chunks : List KBytes) (limits : Limits := {}) : Bool := Id.run do
  let .ok eager := Stream.read limits.mixed input | return false
  let .ok ⟨signature, pull⟩ := Stream.Events.readAll limits.mixed input | return false
  let .eos := pull.termination | return false
  let trace := run limits chunks
  return decide (trace.fields = some eager.fields ∧ trace.terminal = some (.ok input.len) ∧
    trace.batches.reverse = eager.batches.map observeRecord ∧
    trace.batches.reverse.map (fun batch => (batch.rows, batch.columns)) = pull.batches.map observeEvent ∧
    List.ofFn (fun i => (signature.kind i).1) = eager.fields)

private def splitAt (input : KBytes) (cuts : List Nat) : List KBytes :=
  let (pieces, last) := cuts.foldl (fun (pieces, last) cut => (input.slice last (cut - last) :: pieces, cut)) ([], 0)
  pieces.reverse ++ [input.slice last (input.len - last)]

private def singleBytes (input : KBytes) : List KBytes :=
  (List.range input.len).map fun i => input.slice i 1

#guard agrees multi (singleBytes multi) { totalDataBuffers := 5 }
#guard agrees multi (splitAt multi
  [0, 3, 3, 4, 5, 7, 8, 22, 255, 256, 257, 262, 264, 353, 639, 640, 641, 800,
    912, 915, 920, 1239, 1247, 1249, 1255, 1256, 1615, 1617, 1700, 1743, 1744, 1745,
    1747, 1748, 1751, 1752])
#guard agrees schemaOnly (singleBytes schemaOnly)
  { mixed := { observation := { ipc := { batches := 0 }, totalRows := 0 } }, totalDataBuffers := 0 }
#guard agrees zeroColumns (singleBytes zeroColumns)
  { mixed := { observation := { totalCells := 0 } }, totalDataBuffers := 0 }

private def stops (chunks : List KBytes) (completed : Nat) (expected : Error)
    (limits : Limits := {}) : Bool := Id.run do
  let .ok eager := Stream.read {} multi | return false
  let trace := run limits chunks
  return decide (trace.fields = some eager.fields ∧ trace.terminal = some (.error expected) ∧
    trace.batches.reverse = (eager.batches.take completed).map observeRecord)

#guard stops (singleBytes lateTruncated) 2
  (.framing (some 2) ⟨.body, 1616, .malformed .truncated⟩)
#guard stops (splitAt (multi.write lastViewPrefix 4 0) [255, 1247, 1615, 1699, 1701, 1751]) 2
  (.batch 2 lastRecordOffset (.record (.decode (.field 3 (.view (.slot 0 .prefixMismatch))))))
#guard stops [multi, .leaf 1 0] 3
  (.framing (some 3) ⟨.tail, multi.len, .malformed .trailingBytes⟩)
#guard stops [multi ++ .leaf 1 0] 3
  (.framing (some 3) ⟨.tail, multi.len, .malformed .trailingBytes⟩)
#guard stops [multi.slice 0 multiEos] 3
  (.framing (some 3) ⟨.prefix, multiEos, .malformed .truncated⟩)
#guard stops [multi] 2 (.batch 2 lastRecordOffset .dataBufferLimit) { totalDataBuffers := 4 }
#guard stops [multi] 2 (.batch 2 lastRecordOffset (.record .batchLimit))
  { mixed := { observation := { ipc := { batches := 2 } } } }
#guard stops [multi] 2 (.batch 2 lastRecordOffset (.record (.budget (.limit .totalRows))))
  { mixed := { observation := { totalRows := 5 } } }
#guard stops [multi] 2 (.batch 2 lastRecordOffset (.record (.budget (.limit .totalCells))))
  { mixed := { observation := { totalCells := 20 } } }

-- A complete EOS can be followed by empty chunks, and only finish certifies termination.
#guard Id.run do
  let (cursor, trace) := pump 32 (start {}) multi {}
  let .ok (.wait _) := feed cursor .empty | return false
  return decide (trace.terminal = none ∧ trace.batches.length = 3 ∧ finish cursor = .ok multi.len)

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental
