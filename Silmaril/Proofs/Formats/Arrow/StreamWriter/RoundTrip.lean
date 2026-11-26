module

public import Silmaril.Formats.Arrow.StreamWriter.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Window.Defs
import Silmaril.Formats.Arrow.Body.Thms
import Silmaril.Formats.Arrow.Framing.Thms
import Silmaril.Formats.Arrow.Layout.Thms
import Silmaril.Formats.Arrow.MetadataWriter.Thms
import Silmaril.Formats.Arrow.Writer.Thms
import Silmaril.Proofs.Formats.Arrow.StreamWriter.Framing
import Silmaril.Proofs.Formats.Arrow.StreamWriter.Transport
import Silmaril.Proofs.Formats.Arrow.StreamWriter.Windows
import Init.Data.List.Monadic
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.StreamWriter

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.StreamWriter

theorem emitBatchFrame_at {limits : ObservationLimits}
    {input : Writer.BatchInput} {physical : BatchFrame input.fields}
    {part whole : KBytes} {start : Nat}
    (written : Writer.emitBatch limits input = .ok physical)
    (framed : emitFrame limits.ipc ⟨.recordBatch physical.metadata, physical.body.len⟩
      physical.body = .ok part)
    (atRecord : Window part whole start) (aligned : start % 8 = 0) :
    let size := MetadataWriter.wireSize ⟨.recordBatch physical.metadata, physical.body.len⟩
    ∃ (raw : KBytes) (batch : BatchFrame input.fields),
      part.wf = true ∧ part.len = 8 + size + physical.body.len ∧ part.len % 8 = 0 ∧
      readEnvelope limits.ipc whole start = .ok (.metadata size) ∧
      readMessage limits.ipc (whole.slice (start + 8) size) =
        .ok ⟨.recordBatch batch.metadata, physical.body.len⟩ ∧
      readBody limits.ipc whole (start + 8 + size) physical.body.len = .ok raw ∧
      validateBatch input.fields batch.metadata raw = .ok batch ∧
      batch.metadata.rowCount = input.rowCount ∧
      decodeBatch limits batch = .ok input.observe ∧ input.observe.length = input.rowCount := by
  let message : Message := ⟨.recordBatch physical.metadata, physical.body.len⟩
  let size := MetadataWriter.wireSize message
  obtain ⟨partWf, length, prefixRead, metadataRead, raw, bodyRead, _⟩ := emitFrame_exact framed
  obtain ⟨count, bodyAligned, rows⟩ := Writer.emitBatch_roundtrip written
  have sizeAligned := (MetadataWriter.wireSize_aligned message).2
  have metadataIn : 8 + size ≤ part.len := by
    change part.len = 8 + size + physical.body.len at length
    omega
  have rawFull := emitFrame_bodyFull framed bodyRead
  have bodyWf := (emitFrame_bodyWindow framed).1
  have sameLength : raw.len = physical.body.len := by rw [rawFull, KBytes.len_slice]
  have fits : physical.metadata.Fits input.fields raw.len := sameLength ▸ physical.layout
  let batch : BatchFrame input.fields := ⟨physical.metadata, raw, fits⟩
  have rowLength := ((decodeBatch_iff limits physical input.observe).1 rows).2.shape.1.trans count
  refine ⟨raw, batch, partWf, length, ?_, Window.readEnvelope_at atRecord aligned partWf prefixRead,
    ?_, ?_, ?_, count, ?_, rowLength⟩
  · change part.len = 8 + size + physical.body.len at length
    change size % 8 = 0 at sizeAligned
    omega
  · rwa [Window.slice atRecord 8 size metadataIn]
  · simpa only [Nat.add_assoc] using Window.readBody_at atRecord aligned bodyRead
  · simp only [validateBatch, dite_eq_left fits, batch]
  · exact (decodeBatch_fullSlice limits physical bodyWf batch rfl rawFull).trans rows

private theorem readRecord_at {limits : ObservationLimits} {fields : List Field}
    {input : Writer.BatchInput} {part whole : KBytes} {start : Nat}
    (written : emitRecord limits fields input = .ok part)
    (atRecord : Window part whole start) (aligned : start % 8 = 0) :
    ∃ (size : Nat) (message : Message) (raw : KBytes) (batch : BatchFrame fields),
      part.wf = true ∧ part.len = 8 + size + message.bodyLength ∧ part.len % 8 = 0 ∧
      readEnvelope limits.ipc whole start = .ok (.metadata size) ∧
      readMessage limits.ipc (whole.slice (start + 8) size) = .ok message ∧
      message.header = .recordBatch batch.metadata ∧
      readBody limits.ipc whole (start + 8 + size) message.bodyLength = .ok raw ∧
      validateBatch fields batch.metadata raw = .ok batch ∧
      batch.metadata.rowCount = input.rowCount ∧
      decodeBatch limits batch = .ok input.observe ∧ input.observe.length = input.rowCount := by
  by_cases schema : input.fields = fields
  · subst fields
    cases physical : Writer.emitBatch limits input with
    | error error => simp [emitRecord, physical, bind, Except.bind] at written
    | ok frame =>
      simp [emitRecord, physical, bind, Except.bind] at written
      obtain ⟨raw, batch, wf, extent, frameAligned, envelope, metadata, body, layout, count, rows,
        lengths⟩ := emitBatchFrame_at physical written atRecord aligned
      exact ⟨_, _, raw, batch, wf, extent, frameAligned, envelope, metadata, rfl, body, layout,
        count, rows, lengths⟩
  · simp [emitRecord, schema, bind, Except.bind] at written

private theorem readBatches_written (limits : ObservationLimits) (fields : List Field) (whole : KBytes)
    {inputs : List Writer.BatchInput} {pieces : List KBytes} {fuel start : Nat}
    (reversed : List (BatchFrame fields))
    (written : inputs.mapM (emitRecord limits fields) = .ok pieces)
    (position : Suffix (pieces.foldr (· ++ ·) eos) whole start)
    (aligned : start % 8 = 0) (budget : inputs.length ≤ fuel) :
    ∃ frames : List (BatchFrame fields),
      (pieces.foldr (· ++ ·) eos).wf = true ∧
      Stream.readBatches limits.ipc whole fields fuel start reversed = .ok (reversed.reverse ++ frames) ∧
      frames.map (·.metadata.rowCount) = inputs.map (·.rowCount) ∧
      frames.mapM (decodeBatch limits) = .ok (inputs.map Writer.BatchInput.observe) ∧
      (inputs.map Writer.BatchInput.observe).map List.length = inputs.map (·.rowCount) := by
  induction inputs generalizing pieces fuel start reversed with
  | nil =>
    have empty : pieces = [] := by simpa [pure, Except.pure] using written.symm
    subst pieces
    have read := Window.readEnvelope_at position.window aligned (by rfl) (read_eos limits.ipc)
    have stop : start + 8 = whole.len := position.endOffset
    refine ⟨[], rfl, ?_, rfl, rfl, rfl⟩
    cases fuel <;> simp [Stream.readBatches, read, stop, bind, Except.bind, pure, Except.pure]
  | cons input inputs ih =>
    cases fuel with
    | zero => simp at budget
    | succ fuel =>
      cases first : emitRecord limits fields input with
      | error error => simp [List.mapM_cons, first, bind, Except.bind] at written
      | ok part =>
        cases rest : inputs.mapM (emitRecord limits fields) with
        | error error => simp [List.mapM_cons, first, rest, bind, Except.bind] at written
        | ok pieces' =>
          simp only [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] at written
          subst pieces
          change Suffix (part ++ pieces'.foldr (· ++ ·) eos) whole start at position
          obtain ⟨size, message, raw, batch, partWf, length, frameAligned, envelope, metadata, header,
            body, layout, count, rows, rowLength⟩ := readRecord_at first position.frameWindow aligned
          have next := position.dropFrame
          have nextAligned : (start + part.len) % 8 = 0 := by omega
          obtain ⟨tail, tailWf, read, counts, observed, lengths⟩ :=
            ih (batch :: reversed) rest next nextAligned (by simpa using budget)
          refine ⟨batch :: tail, KBytes.wf_append partWf tailWf, ?_, ?_, ?_, ?_⟩
          · have shift : start + 8 + size + message.bodyLength = start + part.len := by omega
            simp [Stream.readBatches, envelope, metadata, header, body, layout,
              bind, Except.bind, shift, read, List.reverse_cons, List.append_assoc]
          · simp [count, counts]
          · simp [rows, observed, bind, Except.bind, pure, Except.pure]
          · simpa only [List.map_cons, rowLength] using congrArg (input.rowCount :: ·) lengths

theorem emit_roundtrip {limits : ObservationLimits} {fields : List Field}
    {inputs : List Writer.BatchInput} {wire : KBytes} (written : emit limits fields inputs = .ok wire) :
    ∃ stream : Stream, readStream limits.ipc wire = .ok stream ∧ stream.fields = fields ∧
      stream.batches.map (·.metadata.rowCount) = inputs.map (·.rowCount) ∧
      readRows limits wire = .ok ⟨fields, inputs.map Writer.BatchInput.observe⟩ ∧
      (inputs.map Writer.BatchInput.observe).map List.length = inputs.map (·.rowCount) := by
  by_cases cap : inputs.length > limits.ipc.batches
  · simp [emit, cap, bind, Except.bind] at written
  cases aggregate : Body.checkBudget limits fields.length (inputs.map (·.rowCount)).sum with
  | error error => simp [emit, cap, aggregate, bind, Except.bind] at written
  | ok success =>
    cases success
    cases schema : emitFrame limits.ipc ⟨.schema fields, 0⟩ KBytes.empty with
    | error error => simp [emit, cap, aggregate, schema, bind, Except.bind] at written
    | ok front =>
      cases records : inputs.mapM (emitRecord limits fields) with
      | error error => simp [emit, cap, aggregate, schema, records, bind, Except.bind] at written
      | ok pieces =>
        simp [emit, cap, aggregate, schema, records, bind, Except.bind, pure, Except.pure] at written
        subst wire
        let tail := pieces.foldr (· ++ ·) eos
        obtain ⟨frontWf, len, envelope, metadata, _⟩ := emitFrame_exact schema
        let size := MetadataWriter.wireSize ⟨.schema fields, 0⟩
        have frontLength : front.len = 8 + size := len
        have aligned : front.len % 8 = 0 := by
          rw [frontLength]
          have := (MetadataWriter.wireSize_aligned ⟨.schema fields, 0⟩).2
          change size % 8 = 0 at this
          omega
        have position : Suffix tail (front ++ tail) front.len := .right front .self
        have window : Window front (front ++ tail) 0 := .left .self tail
        have prefixRead : readEnvelope limits.ipc (front ++ tail) 0 = .ok (.metadata size) :=
          Window.readEnvelope_at window (by decide) frontWf envelope
        have metadataRead :
            readMessage limits.ipc ((front ++ tail).slice 8 size) = .ok ⟨.schema fields, 0⟩ := by
          rw [show (front ++ tail).slice 8 size = front.slice 8 size from
            Window.slice window 8 size (by omega)]
          exact metadata
        obtain ⟨frames, tailWf, read, count, rows, lengths⟩ :=
          readBatches_written limits fields (front ++ tail) [] records position aligned
            (Nat.le_of_not_gt cap)
        have wf : (front ++ tail).wf = true := KBytes.wf_append frontWf tailWf
        have streamRead : readStream limits.ipc (front ++ tail) = .ok ⟨fields, frames⟩ := by
          rw [frontLength] at read
          simp [readStream, wf, prefixRead, metadataRead, bind, Except.bind, read, pure, Except.pure]
        refine ⟨⟨fields, frames⟩, streamRead, rfl, count, ?_, lengths⟩
        change readRows limits (front ++ tail) = .ok ⟨fields, inputs.map Writer.BatchInput.observe⟩
        simp [readRows, streamRead, bind, Except.bind, count, aggregate, rows, pure, Except.pure]

end Silmaril.Proofs.Formats.Arrow.StreamWriter
