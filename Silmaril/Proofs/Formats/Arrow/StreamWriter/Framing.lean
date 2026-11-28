module

public import Silmaril.Formats.Arrow.StreamWriter.Defs
import Silmaril.Formats.Arrow.MetadataWriter.Thms
import Silmaril.Prelude.Bytes.Thms
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.StreamWriter

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.StreamWriter

private theorem append_length (a b : KBytes) : (a ++ b).len = a.len + b.len := rfl

private theorem read_left {left right : KBytes} {offset width : Nat}
    (within : offset + width ≤ left.len) :
    (left ++ right).read offset width = left.read offset width := by
  change (KBytes.node _ left right).read offset width = _
  simp only [KBytes.read, ite_eq_left within]

private theorem slice_left {left right : KBytes} {offset width : Nat}
    (within : offset + width ≤ left.len) :
    (left ++ right).slice offset width = left.slice offset width := by
  change (KBytes.node _ left right).slice offset width = _
  simp only [KBytes.slice, ite_eq_left within]

private theorem slice_right {left right : KBytes} {offset width : Nat}
    (starts : left.len ≤ offset) (positive : 0 < width) :
    (left ++ right).slice offset width = right.slice (offset - left.len) width := by
  change (KBytes.node _ left right).slice offset width = _
  have beyond : ¬ offset + width ≤ left.len := by omega
  simp only [KBytes.slice, ite_eq_right beyond, ite_eq_left starts]

private theorem envelope_length (size : Nat) : (envelopeBytes size).len = 8 := rfl

private theorem metadataWindow (metadata body : KBytes) (positive : 0 < metadata.len) :
    (envelopeBytes metadata.len ++ (metadata ++ body)).slice 8 metadata.len =
      metadata.slice 0 metadata.len := by
  rw [slice_right (offset := 8) (by rw [envelope_length]; decide) positive,
    envelope_length]
  exact slice_left (by omega : 0 + metadata.len ≤ metadata.len)

private theorem envelope_marker (size : Nat) : (envelopeBytes size).read 0 4 = 0xffffffff :=
  rfl

private theorem envelope_size (size : Nat) (bound : size < 2^31) :
    (envelopeBytes size).read 4 4 = size := by
  change size % 2^32 = size
  exact Nat.mod_eq_of_lt (by omega)

theorem read_eos (limits : Limits) : readEnvelope limits eos 0 = .ok .eos := rfl

private theorem envelope_read (limits : Limits) (size : Nat) (tail : KBytes)
    (positive : 0 < size) (signed : size < 2^31) (aligned : size % 8 = 0)
    (budget : size ≤ limits.metadataBytes) (extent : size ≤ tail.len) :
    readEnvelope limits (envelopeBytes size ++ tail) 0 = .ok (.metadata size) := by
  have noTruncation : ¬ 8 + size > (envelopeBytes size ++ tail).len := by
    rw [append_length]
    change ¬ 8 + size > 8 + tail.len
    omega
  have initial : ¬ 8 > (envelopeBytes size ++ tail).len := by
    rw [append_length]
    change ¬ 8 > 8 + tail.len
    omega
  have marker : (envelopeBytes size ++ tail).read 0 4 = 0xffffffff :=
    (read_left (by rw [envelope_length]; decide)).trans (envelope_marker size)
  have count : (envelopeBytes size ++ tail).read 4 4 = size :=
    (read_left (by rw [envelope_length]; decide)).trans (envelope_size size signed)
  simp [readEnvelope, readPrefix, initial, marker, count, show size ≠ 0 by omega,
    show ¬ (2^31 ≤ size ∨ size % 8 ≠ 0) by omega,
    show ¬ size > limits.metadataBytes by omega, noTruncation]

private theorem checkedBody {limits : Limits} {message : Message} {body : KBytes}
    (checked : checkBody limits message body = .ok ()) :
    message.bodyLength = body.len ∧ body.len % 8 = 0 ∧ body.wf = true ∧
      body.len ≤ limits.bodyBytes := by
  unfold checkBody at checked
  split at checked <;> try contradiction
  split at checked <;> try contradiction
  split at checked <;> try contradiction
  simp_all

theorem emitFrame_exact {limits : Limits} {message : Message} {body wire : KBytes}
    (written : emitFrame limits message body = .ok wire) :
    let size := MetadataWriter.wireSize message
    wire.wf = true ∧ wire.len = 8 + size + message.bodyLength ∧
      readEnvelope limits wire 0 = .ok (.metadata size) ∧
      readMessage limits (wire.slice 8 size) = .ok message ∧
      ∃ extracted, readBody limits wire (8 + size) message.bodyLength = .ok extracted ∧
        extracted.toList = body.toList := by
  cases checked : checkBody limits message body with
  | error reason => simp [emitFrame, checked, bind, Except.bind] at written
  | ok _ =>
    cases encoded : MetadataWriter.emit limits message with
    | error reason => simp [emitFrame, checked, encoded, bind, Except.bind] at written
    | ok metadata =>
      simp only [emitFrame, checked, encoded, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at written
      subst wire
      obtain ⟨read, metadataWf, len, positive, signed, aligned, budget⟩ :=
        MetadataWriter.emit_exact encoded
      obtain ⟨bodyLen, bodyAligned, bodyWf, bodyBudget⟩ := checkedBody checked
      rw [← len, bodyLen]
      have wf := KBytes.wf_append (a := envelopeBytes metadata.len) (by rfl)
        (KBytes.wf_append metadataWf bodyWf)
      have length : (envelopeBytes metadata.len ++ (metadata ++ body)).len =
          8 + metadata.len + body.len := by simp only [append_length, envelope_length]; omega
      refine ⟨wf, length, envelope_read limits _ _ positive signed aligned budget
        (by rw [append_length]; omega), ?_, ?_⟩
      · rwa [metadataWindow metadata body positive]
      · have start : (8 + metadata.len) % 8 = 0 := by omega
        have inBounds : 8 + metadata.len + body.len ≤
            (envelopeBytes metadata.len ++ (metadata ++ body)).len := by omega
        refine ⟨(envelopeBytes metadata.len ++ (metadata ++ body)).slice
          (8 + metadata.len) body.len, ?_, ?_⟩
        · simp [readBody, start, bodyAligned, Nat.not_lt_of_ge bodyBudget, Nat.not_lt_of_ge inBounds]
        · rw [KBytes.toList_slice _ _ _ wf inBounds]
          rw [KBytes.toList_append, KBytes.toList_append]
          have prefixLength : (envelopeBytes metadata.len).toList.length = 8 :=
            KBytes.length_toList _ rfl
          have metadataLength := KBytes.length_toList metadata metadataWf
          have dataLength := KBytes.length_toList body bodyWf
          rw [← prefixLength, ← metadataLength, ← List.drop_drop, List.drop_append_length,
            List.drop_append_length, ← dataLength, List.take_length]

end Silmaril.Proofs.Formats.Arrow.StreamWriter
