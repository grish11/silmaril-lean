module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Defs
public import Silmaril.Formats.Arrow.MixedFlat.Events.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Thms
import Silmaril.Formats.Arrow.MixedFlat.Events.Thms

/-! Pull events from a bounded mixed Arrow IPC V5 stream carrier. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Events

open Silmaril.Relational
open MixedFlat.Events

inductive Error where
  | openError (cause : Stream.Error)
  | message (ordinal offset : Nat) (cause : Stream.BatchError)
  deriving DecidableEq, Repr

def Error.eager : Error → Stream.Error
  | .openError cause => cause
  | .message ordinal _ cause => .batch ordinal cause

abbrev Trace (signature : Scan.Schema MixedFlat.Field Unit) :=
  Arrow.Events.Trace signature (fun _ => Cell) Error

abbrev EventStream := Arrow.Events.EventStream MixedFlat.Field (fun _ : Unit => Cell) Error

structure Decoded (fields : List MixedFlat.Field) where
  record : Stream.Batch
  event : MixedFlat.Events.Batch (schema fields)
  aligned : Agrees (schema fields) record.observed event

/-- Check the next envelope at its original byte offset. The record decoder
owns the metadata, body and running row/cell checks. EOS must end the carrier. -/
def readNext (limits : MixedFlat.Limits) (input : KBytes) (fields : List MixedFlat.Field)
    (remaining ordinal rows offset : Nat) : Except Error (Option (Decoded fields)) := do
  let envelope ← (readEnvelope limits.observation.ipc input offset).mapError
    (fun cause => .message ordinal offset (.envelope cause))
  match envelope with
  | .eos =>
    if offset + 8 = input.len then return none
    else throw (.message ordinal offset .trailingBytes)
  | .metadata size =>
    if remaining = 0 then throw (.message ordinal offset .batchLimit)
    match read : Stream.readRecord limits input fields rows offset size with
    | .error cause => throw (.message ordinal offset cause)
    | .ok record =>
      have shape : record.observed.columns.map Prod.fst = fields ∧
          ∀ pair ∈ record.observed.columns, (cells pair.2).length = record.observed.rowCount := by
        obtain ⟨_, _, _, _, _, parsed, _⟩ := (Stream.readRecord_iff _ _ _ _ _ _ _).mp read
        exact MixedFlat.Events.readParsed_shape parsed
      return some ⟨record, ofObserved fields record.observed shape.1 shape.2,
        by exact MixedFlat.Events.ofObserved_agrees fields record.observed shape.1 shape.2⟩

/-- Open holds the immutable carrier and checked schema. The cursor records
the next original offset and the remaining observation budgets. -/
inductive Cursor : Scan.Schema MixedFlat.Field Unit → Type where
  | at (input : KBytes) (fields : List MixedFlat.Field) (remaining ordinal rows offset : Nat) :
      Cursor (schema fields)

def admit (limits : MixedFlat.Limits) (input : KBytes) : Except Error (List MixedFlat.Field × Nat) :=
  if !input.wf then .error (.openError .source)
  else (Stream.readSchemaFrame limits.observation.ipc input).mapError .openError

def reader (limits : MixedFlat.Limits) :
    Arrow.Events.BatchReader KBytes MixedFlat.Field (fun _ => Cell) Error Cursor where
  openInput input :=
    (admit limits input).map fun (fields, offset) =>
      ⟨schema fields, .at input fields limits.observation.ipc.batches 0 0 offset⟩
  next
    | .at input fields remaining ordinal rows offset =>
      (readNext limits input fields remaining ordinal rows offset).map (Option.map fun decoded =>
        (decoded.event, .at input fields (remaining - 1) (ordinal + 1)
          (rows + decoded.record.observed.rowCount) decoded.record.range.next))
  close _ := .ok ()

/-- Collect through the first failure or exact EOS. The generic driver has
one call beyond the maximum allowed number of RecordBatch messages. -/
def readAll (limits : MixedFlat.Limits) (input : KBytes) : EventStream :=
  (reader limits).read (limits.observation.ipc.batches + 1) input

/-- Completed pulls link consecutive original byte ranges and budget states.
The terminal attempt is kept separate from this successfully delivered prefix. -/
inductive Prefix (limits : MixedFlat.Limits) (input : KBytes) (fields : List MixedFlat.Field) :
    Nat → Nat → Nat → Nat → List (MixedFlat.Events.Batch (schema fields)) →
    Nat → Nat → Nat → Nat → Prop where
  | stop {remaining ordinal rows offset} :
      Prefix limits input fields remaining ordinal rows offset [] remaining ordinal rows offset
  | next {fuel ordinal rows offset decoded rest remaining finalOrdinal finalRows finalOffset} :
      readNext limits input fields (fuel + 1) ordinal rows offset = .ok (some decoded) →
      Prefix limits input fields fuel (ordinal + 1)
        (rows + decoded.record.observed.rowCount) decoded.record.range.next rest
        remaining finalOrdinal finalRows finalOffset →
      Prefix limits input fields (fuel + 1) ordinal rows offset (decoded.event :: rest)
        remaining finalOrdinal finalRows finalOffset

end Silmaril.Formats.Arrow.MixedFlat.Stream.Events
