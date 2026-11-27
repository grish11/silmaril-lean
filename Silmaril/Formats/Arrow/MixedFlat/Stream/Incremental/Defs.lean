module

public import Silmaril.Formats.Arrow.Framing.Incremental.Defs
public import Silmaril.Formats.Arrow.MixedFlat.Stream.Events.Defs
import Silmaril.Formats.Arrow.MixedFlat.Events.Thms

/-! Typed mixed-flat events over ordered native IPC fragments. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental

open MixedFlat.Events
open Arrow.Framing.Incremental (Frame)

structure Limits where
  mixed : MixedFlat.Limits := {}
  totalDataBuffers : Nat := 4096
  deriving Repr

inductive BatchError where
  | record (cause : Stream.BatchError)
  | dataBufferLimit
  deriving DecidableEq, Repr

inductive Error where
  | framing (ordinal : Option Nat) (cause : Arrow.Framing.Incremental.Failure)
  | schema (offset : Nat) (cause : Arrow.Error)
  | expectedSchema (offset : Nat)
  | batch (ordinal offset : Nat) (cause : BatchError)
  deriving DecidableEq, Repr

structure Running where
  ordinal : Nat := 0
  rows : Nat := 0
  dataBuffers : Nat := 0
  deriving DecidableEq, Repr

inductive Phase where
  | schema
  | records (fields : List MixedFlat.Field) (running : Running)

def Phase.ordinal : Phase → Option Nat
  | .schema => none
  | .records _ running => some running.ordinal

structure Cursor where
  limits : Limits
  input : Arrow.Framing.Incremental.State
  phase : Phase

def start (limits : Limits) : Cursor := ⟨limits, Arrow.Framing.Incremental.start 0, .schema⟩

def Cursor.position (cursor : Cursor) : Nat := cursor.input.position

/-- Original start of the pending message. After provisional EOS this is
the EOS marker's start, while position includes its eight bytes. -/
def Cursor.messageOffset (cursor : Cursor) : Nat :=
  match cursor.input with
  | .prefix offset _ | .metadata offset _ _ | .body offset _ _ _ => offset
  | .ended offset => offset - 8

structure Delivered (fields : List MixedFlat.Field) where
  record : Stream.Batch
  event : MixedFlat.Events.Batch (schema fields)
  aligned : Agrees (schema fields) record.observed event
  dataBuffers : Nat

inductive Progress where
  | wait (cursor : Cursor)
  | advance (cursor : Cursor) (rest : KBytes)
  | schema (fields : List MixedFlat.Field) (range : Stream.BatchRange) (cursor : Cursor) (rest : KBytes)
  | batch (fields : List MixedFlat.Field) (value : Delivered fields) (cursor : Cursor) (rest : KBytes)

/-- One successful reply retains an original immutable reference window
for the pending input and any returned suffix. -/
def Progress.Continues (input : KBytes) (before : Cursor) (chunk : KBytes)
    (next : Cursor) (rest : KBytes) : Prop :=
  next.input.InCarrier before.limits.mixed.observation.ipc input ∧
    next.limits = before.limits ∧
    Arrow.Framing.Incremental.Window input next.position rest ∧
    next.position + rest.len = before.position + chunk.len

/-- A batch step identifies the old pull result at the same original ordinal
and offset. The leaf is the immutable reference representation. Input
chunks and their split points have no such restriction. -/
def Progress.Refines (size packed : Nat) (before : Cursor) (chunk : KBytes) : Progress → Prop
  | .wait next =>
    next.input.InCarrier before.limits.mixed.observation.ipc (.leaf size packed) ∧
      next.limits = before.limits ∧ next.phase = before.phase ∧
      next.messageOffset = before.messageOffset ∧ next.position = before.position + chunk.len
  | .advance next rest =>
    Progress.Continues (.leaf size packed) before chunk next rest ∧
      next.phase = before.phase ∧ next.messageOffset = before.messageOffset
  | .schema fields range next rest =>
    Progress.Continues (.leaf size packed) before chunk next rest ∧ before.phase = .schema ∧
      next.phase = .records fields {} ∧ next.messageOffset = range.next ∧
      (before.messageOffset = 0 →
        Stream.readSchemaFrame before.limits.mixed.observation.ipc (.leaf size packed) =
          .ok (fields, range.next))
  | .batch fields value next rest =>
    Progress.Continues (.leaf size packed) before chunk next rest ∧
      ∃ running,
        before.phase = .records fields running ∧
        next.phase = .records fields
          ⟨running.ordinal + 1, running.rows + value.event.rowCount, running.dataBuffers + value.dataBuffers⟩ ∧
        value.record.range.offset = before.messageOffset ∧ next.messageOffset = value.record.range.next ∧
        ∃ pulled,
          Stream.Events.readNext before.limits.mixed (.leaf size packed) fields
            (before.limits.mixed.observation.ipc.batches - running.ordinal) running.ordinal
            running.rows before.messageOffset = .ok (some pulled) ∧
          pulled.record = value.record ∧ pulled.event = value.event

/-- The range is in the original byte stream, independently of the
representation chosen for the completed metadata and body. -/
def frameRange (frame : Frame) : Stream.BatchRange :=
  ⟨frame.offset, frame.metadata.len, frame.body.len⟩

/-- Decode the checked frame after applying the stream-wide batch, data-buffer
and row/cell budgets. The mixed metadata limit still applies per batch. -/
def decode (limits : Limits) (fields : List MixedFlat.Field) (running : Running) (frame : Frame) :
    Except BatchError (Delivered fields) := do
  let ipc := limits.mixed.observation.ipc
  if running.ordinal ≥ ipc.batches then throw (.record .batchLimit)
  let metadata ← (MixedFlat.readMetadata ipc limits.mixed.view.dataBuffers limits.mixed.totalDataBuffers
    fields (Arrow.Framing.Incremental.metadataBytes frame.metadata)).mapError
      fun cause => .record (.metadata cause)
  let count := metadata.counts.sum
  if running.dataBuffers + count > limits.totalDataBuffers then throw .dataBufferLimit
  (Body.checkBudget limits.mixed.observation fields.length (running.rows + metadata.batch.rowCount)).mapError
    fun cause => .record (.budget cause)
  let packedBody := KBytes.leaf frame.body.len (frame.body.read 0 frame.body.len)
  match parsed : MixedFlat.readParsed limits.mixed fields metadata packedBody with
  | .error cause => throw (.record (.decode cause))
  | .ok observed =>
    have shape : observed.columns.map Prod.fst = fields ∧
        ∀ pair ∈ observed.columns, (cells pair.2).length = observed.rowCount := by
      exact MixedFlat.Events.readParsed_shape parsed
    return ⟨⟨frameRange frame, observed⟩, ofObserved fields observed shape.1 shape.2,
      by exact MixedFlat.Events.ofObserved_agrees fields observed shape.1 shape.2, count⟩

/-- Each reply can publish at most one schema or batch. A late error cannot
take back a batch already published by an earlier reply. -/
def feed (cursor : Cursor) (chunk : KBytes) : Except Error Progress := do
  let ipc := cursor.limits.mixed.observation.ipc
  let outcome ← (Arrow.Framing.Incremental.feed ipc cursor.input chunk).mapError
    (.framing cursor.phase.ordinal)
  match outcome with
  | .wait pending => return .wait { cursor with input := pending }
  | .advance pending rest => return .advance { cursor with input := pending } rest
  | .frame frame pending rest =>
    match cursor.phase with
    | .schema =>
      let fields ← (MixedFlat.readSchema ipc
        (Arrow.Framing.Incremental.metadataBytes frame.metadata)).mapError (.schema frame.offset)
      if frame.body.len ≠ 0 then throw (.schema frame.offset (.malformed .bodyLength))
      return .schema fields (frameRange frame)
        { cursor with input := pending, phase := .records fields {} } rest
    | .records fields running =>
      let value ← (decode cursor.limits fields running frame).mapError (.batch running.ordinal frame.offset)
      let after : Running := ⟨running.ordinal + 1, running.rows + value.event.rowCount,
        running.dataBuffers + value.dataBuffers⟩
      return .batch fields value { cursor with input := pending, phase := .records fields after } rest

/-- Final success requires a checked schema and a complete modern EOS.
Passing EOS through feed leaves the cursor able to reject later tail bytes. -/
def finish (cursor : Cursor) : Except Error Nat := do
  let last ← (Arrow.Framing.Incremental.finish cursor.input).mapError (.framing cursor.phase.ordinal)
  match cursor.phase with
  | .schema => throw (.expectedSchema (last - 8))
  | .records .. => return last


/-- Actual calls through the first published Schema, including all waits
and request transitions caused by splitting its bytes. -/
inductive SchemaSteps (size packed : Nat) (fields : List MixedFlat.Field) :
    Cursor → Cursor → Prop where
  | publish {before next chunk range rest} :
      Arrow.Framing.Incremental.Window (.leaf size packed) before.position chunk →
      feed before chunk = .ok (.schema fields range next rest) →
      SchemaSteps size packed fields before next
  | wait {before next last chunk} :
      Arrow.Framing.Incremental.Window (.leaf size packed) before.position chunk →
      feed before chunk = .ok (.wait next) →
      SchemaSteps size packed fields next last →
      SchemaSteps size packed fields before last
  | advance {before next last chunk rest} :
      Arrow.Framing.Incremental.Window (.leaf size packed) before.position chunk →
      feed before chunk = .ok (.advance next rest) →
      SchemaSteps size packed fields next last →
      SchemaSteps size packed fields before last

/-- The checked Schema and the cursor at its exact first record offset. -/
def SchemaAgreement (size packed : Nat) (fields : List MixedFlat.Field) (limits : Limits)
    (opened : Cursor) : Prop :=
  opened.input.InCarrier limits.mixed.observation.ipc (.leaf size packed) ∧ opened.limits = limits ∧
    opened.phase = .records fields {} ∧
    Stream.readSchemaFrame limits.mixed.observation.ipc (.leaf size packed) =
      .ok (fields, opened.messageOffset)

/-- The finite successful calls after a checked Schema, with only the
published batches in their original order. Every input window begins
exactly where the cursor stopped. A failed call leaves this prefix intact. -/
inductive RecordSteps (size packed : Nat) (fields : List MixedFlat.Field) :
    Cursor → List (Delivered fields) → Cursor → Prop where
  | stop (cursor : Cursor) : RecordSteps size packed fields cursor [] cursor
  | wait {before next last chunk batches} :
      Arrow.Framing.Incremental.Window (.leaf size packed) before.position chunk →
      feed before chunk = .ok (.wait next) →
      RecordSteps size packed fields next batches last →
      RecordSteps size packed fields before batches last
  | advance {before next last chunk rest batches} :
      Arrow.Framing.Incremental.Window (.leaf size packed) before.position chunk →
      feed before chunk = .ok (.advance next rest) →
      RecordSteps size packed fields next batches last →
      RecordSteps size packed fields before batches last
  | batch {before next last chunk rest value batches} :
      Arrow.Framing.Incremental.Window (.leaf size packed) before.position chunk →
      feed before chunk = .ok (.batch fields value next rest) →
      RecordSteps size packed fields next batches last →
      RecordSteps size packed fields before (value :: batches) last

/-- The corresponding immutable pull prefix and the eager suffix equation.
The equation is useful after EOS and also preserves the original eager
result when a later immutable read fails. -/
def RecordAgreement (size packed : Nat) (fields : List MixedFlat.Field) (before : Cursor)
    (running : Running) (batches : List (Delivered fields)) (last : Cursor) : Prop :=
  let input := KBytes.leaf size packed
  let limits := before.limits.mixed
  let available := limits.observation.ipc.batches - running.ordinal
  ∃ after : Running,
    last.input.InCarrier limits.observation.ipc input ∧ last.limits = before.limits ∧
    last.phase = .records fields after ∧
    Stream.Events.Prefix limits input fields available running.ordinal running.rows before.messageOffset
      (batches.map Delivered.event) (limits.observation.ipc.batches - after.ordinal)
      after.ordinal after.rows last.messageOffset ∧
    Stream.readBatches limits input fields available running.ordinal running.rows before.messageOffset =
      (Stream.readBatches limits input fields (limits.observation.ipc.batches - after.ordinal)
        after.ordinal after.rows last.messageOffset).map (batches.map Delivered.record ++ ·)

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental
