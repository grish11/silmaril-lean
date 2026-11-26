module

public import Silmaril.Formats.Arrow.StreamWriter.Defs
import Silmaril.Formats.Arrow.Framing.Thms
import Silmaril.Formats.Arrow.Layout.Thms
import Silmaril.Formats.Arrow.MetadataWriter.Thms
public import Silmaril.Proofs.Formats.Arrow.StreamWriter.Windows
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.StreamWriter

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.StreamWriter

theorem Window.readEnvelope_at {part whole : KBytes} {start : Nat}
    (atPart : Window part whole start) (aligned : start % 8 = 0)
    {limits : Limits} {envelope : Envelope}
    (partWf : part.wf = true) (read : readEnvelope limits part 0 = .ok envelope) :
    readEnvelope limits whole start = .ok envelope := by
  have spec := (readEnvelope_iff _ _ _ _ partWf).1 read
  have span : 8 ≤ part.len := by
    have enough := spec.2.1
    rw [KBytes.length_toList _ partWf] at enough
    exact enough
  have marker : whole.read start 4 = 0xffffffff := by
    have same := atPart.read 0 4 (by omega) (by decide)
    rw [Nat.add_zero] at same
    rw [same, KBytes.read_eq part 0 4 partWf (by omega)]
    exact spec.2.2.1
  have count := atPart.read 4 4 (by omega) (by decide)
  have localCount := KBytes.read_eq part 4 4 partWf (by omega)
  have wholeSpan := atPart.extent
  have wholeEnough : ¬ start + 8 > whole.len := by omega
  cases envelope with
  | eos =>
    have empty := spec.2.2.2
    change KBytes.leVal ((part.toList.drop 4).take 4) = 0 at empty
    simp [readEnvelope, aligned, wholeEnough, marker, count, localCount, empty]
  | metadata size =>
    obtain ⟨value, positive, signed, padded, budget, endOfFrame⟩ := spec.2.2.2
    change KBytes.leVal ((part.toList.drop 4).take 4) = size at value
    rw [KBytes.length_toList _ partWf] at endOfFrame
    have enough : ¬ start + 8 + size > whole.len := by omega
    simp [readEnvelope, aligned, wholeEnough, marker, count, localCount, value,
      show size ≠ 0 by omega, show ¬ (2^31 ≤ size ∨ size % 8 ≠ 0) by omega,
      show ¬ size > limits.metadataBytes by omega, enough]

theorem Window.readBody_at {part whole : KBytes} {start offset size : Nat}
    (atPart : Window part whole start) (aligned : start % 8 = 0)
    {limits : Limits} {extracted : KBytes}
    (read : readBody limits part offset size = .ok extracted) :
    readBody limits whole (start + offset) size = .ok extracted := by
  obtain ⟨offAlign, sizeAlign, budget, within, result⟩ := (readBody_iff _ _ _ _ _).1 read
  exact (readBody_iff _ _ _ _ _).2 ⟨by omega, sizeAlign, budget,
    by have := atPart.extent; omega, result.trans (atPart.slice offset size within).symm⟩

theorem emitFrame_bodyWindow {limits : Limits} {message : Message} {body wire : KBytes}
    (written : emitFrame limits message body = .ok wire) :
    body.wf = true ∧ Window body wire (8 + MetadataWriter.wireSize message) := by
  cases checked : checkBody limits message body with
  | error e => simp [emitFrame, checked, bind, Except.bind] at written
  | ok success =>
    cases success
    cases encoded : MetadataWriter.emit limits message with
    | error e => simp [emitFrame, checked, encoded, bind, Except.bind] at written
    | ok metadata =>
      simp only [emitFrame, checked, encoded, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at written
      subst wire
      have wf : body.wf = true := by
        unfold checkBody at checked
        split at checked <;> try contradiction
        split at checked <;> try contradiction
        simp_all
      have len := (MetadataWriter.emit_exact encoded).2.2.1
      rw [← len]
      exact ⟨wf, .right (envelopeBytes metadata.len) (.right metadata .self)⟩

theorem emitFrame_bodyFull {limits : Limits} {metadata : RecordBatch} {body wire extracted : KBytes}
    (written : emitFrame limits ⟨.recordBatch metadata, body.len⟩ body = .ok wire)
    (read : readBody limits wire (8 + MetadataWriter.wireSize ⟨.recordBatch metadata, body.len⟩)
      body.len = .ok extracted) :
    extracted = body.slice 0 body.len := by
  have exactWindow := (emitFrame_bodyWindow written).2.slice 0 body.len (by omega)
  simpa only [Nat.add_zero] using (readBody_iff _ _ _ _ _).1 read |>.2.2.2.2 |>.trans exactWindow

private theorem readColumns_fullSlice (body : KBytes) (wf : body.wf = true)
    (fields : List Field) (nodes : List FieldNode) (descriptors : List Buffer)
    (within : ∀ b ∈ descriptors, b.offset + b.length ≤ body.len) :
    Body.readColumns (body.slice 0 body.len) fields nodes descriptors =
      Body.readColumns body fields nodes descriptors := by
  have sliceOne (buffer : Buffer) (fits : buffer.offset + buffer.length ≤ body.len) :
      Body.sliceBuffer (body.slice 0 body.len) buffer = Body.sliceBuffer body buffer :=
    slice_full_slice body wf buffer.offset buffer.length fits
  induction fields generalizing nodes descriptors with
  | nil => cases nodes <;> cases descriptors <;> rfl
  | cons field fields ih =>
    cases nodes with
    | nil => cases descriptors <;> rfl
    | cons node nodes =>
      cases descriptors with
      | nil => obtain ⟨_, _, type⟩ := field; cases type <;> rfl
      | cons validity rest =>
        cases rest with
        | nil => obtain ⟨_, _, type⟩ := field; cases type <;> rfl
        | cons first rest =>
          cases field with
          | mk name nullable type =>
            cases type with
            | int32 =>
              simp only [Body.readColumns, Body.nextColumn,
                sliceOne validity (within _ (by simp)), sliceOne first (within _ (by simp))]
              rw [ih nodes rest (fun b member => within b (by simp [member]))]
            | utf8 =>
              cases rest with
              | nil => rfl
              | cons second rest =>
                simp only [Body.readColumns, Body.nextColumn, sliceOne validity (within _ (by simp)),
                  sliceOne first (within _ (by simp)), sliceOne second (within _ (by simp))]
                rw [ih nodes rest (fun b member => within b (by simp [member]))]

theorem decodeBatch_fullSlice (limits : ObservationLimits) {fields : List Field}
    (frame : BatchFrame fields) (wf : frame.body.wf = true)
    (sliced : BatchFrame fields) (metadata : sliced.metadata = frame.metadata)
    (body : sliced.body = frame.body.slice 0 frame.body.len) :
    decodeBatch limits sliced = decodeBatch limits frame := by
  unfold decodeBatch
  have length : sliced.body.len = frame.body.len := by rw [body, KBytes.len_slice]
  have slicedWf : sliced.body.wf = true := by
    rw [body]
    exact KBytes.wf_slice _ _ _ wf (by omega)
  have budget : Body.checkBatch limits sliced = Body.checkBatch limits frame := by
    simp only [Body.checkBatch, metadata, length, slicedWf, wf]
  have reads := readColumns_fullSlice frame.body wf fields frame.metadata.nodes frame.metadata.buffers
    (fun desc member => (frame.layout.2.2.2.mem_fits member).2.2)
  rw [budget, metadata, body, reads]

end Silmaril.Proofs.Formats.Arrow.StreamWriter
