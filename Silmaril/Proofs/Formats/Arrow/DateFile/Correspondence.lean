module

public import Silmaril.Formats.Arrow.DateFile.Defs
import Silmaril.Formats.Arrow.DateStream.Thms
import Silmaril.Formats.Arrow.DateValues.Thms
import Silmaril.Formats.Arrow.Framing.Thms
import Silmaril.Prelude.Bytes.Thms
import Silmaril.Proofs.Formats.Arrow.DateFile.Body
import Silmaril.Proofs.Formats.Arrow.DateFile.Index
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Arrow.DateFile

open Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.DateFile

private theorem corresponding_eq {limits : Limits} {input stream : KBytes}
    {field : DateStream.Field} {fuel offset : Nat} {streamDates : List DateValues.Column}
    (wire : DateStream.BatchesWire limits stream field fuel offset streamDates)
    {blocks : List FileBlock} {fileDates : List DateValues.Column}
    (fileWf : input.wf = true) (streamWf : stream.wf = true)
    (aligned : BatchesCorrespond limits input stream offset blocks)
    (ordered : List.Forall₂ (fun block dates => readRecord limits input field block = .ok dates)
      blocks fileDates) : fileDates = streamDates := by
  induction wire generalizing blocks fileDates with
  | eos ended _ =>
    cases aligned with
    | eos =>
      cases ordered
      rfl
    | batch parsed =>
      rw [ended] at parsed
      cases parsed
  | @next fuel offset size next dates tail framed decoded _ ih =>
    cases aligned with
    | eos ended =>
      rw [ended] at framed
      cases framed
    | @batch _ matchSize block rest matched width messages bodies later =>
      have sizeEq : matchSize = size :=
        Envelope.metadata.inj (Except.ok.inj (matched.symm.trans framed))
      subst matchSize
      cases ordered with
      | @cons _ fileColumn _ fileTail fileRead restRead =>
        obtain ⟨fileBatch, _, fileMeta, fileBody, fileValues⟩ := readRecord_checked fileRead
        obtain ⟨streamBatch, length, body, view, streamMeta, streamBody, nextEq, viewEq,
            check, observation⟩ := (DateStream.readBatch_iff _ _ _ _ _ _ _).mp decoded
        have declared : streamBatch = fileBatch ∧ length = block.bodyLength := by
          rw [streamMeta, fileMeta] at messages
          simpa using messages
        obtain ⟨batchEq, lengthEq⟩ := declared
        subst streamBatch
        subst length
        have streamValues : DateValues.decodeBatch limits field.decoder field.descriptor fileBatch body =
            .ok dates :=
          (DateValues.decodeBatch_iff _ _ _ _ _ _).mpr ⟨view, viewEq, check, observation⟩
        obtain ⟨_, _, _, boundedFile, fileSlice⟩ := (readBody_iff _ _ _ _ _).mp fileBody
        obtain ⟨_, _, _, boundedStream, streamSlice⟩ := (readBody_iff _ _ _ _ _).mp streamBody
        have fileBodyWf : (bodySlice input block).wf = true := by
          rw [fileSlice]
          exact KBytes.wf_slice _ _ _ fileWf boundedFile
        have streamBodyWf : body.wf = true := by
          rw [streamSlice]
          exact KBytes.wf_slice _ _ _ streamWf boundedStream
        have sameBody : (bodySlice input block).toList = body.toList := by
          rw [streamSlice, show offset + 8 + size = offset + block.metadataLength by omega]
          exact bodies.symm
        have headEq := sameDecodedBody fileBodyWf streamBodyWf sameBody fileValues streamValues
        have alignedTail : BatchesCorrespond limits input stream next rest := by
          rwa [nextEq, show offset + 8 + size = offset + block.metadataLength by omega]
        exact congrArg₂ List.cons headEq (ih alignedTail restRead)

theorem readAt_stream {limits : Limits} {input : KBytes} (index : Index input)
    {stream : KBytes} {start : Nat} {observed : DateStream.Stream} {dates : List DateValues.Column}
    (schema : DateStream.readSchema limits stream = .ok (index.field, start))
    (matched : BatchesCorrespond limits input stream start index.blocks)
    (streamRead : DateStream.read limits stream = .ok observed)
    (sequential : index.blocks.mapM (readRecord limits input index.field) = .ok dates) (n : Nat) :
    index.readAt limits n = .ok observed.batches[n]? := by
  obtain ⟨streamWf, offset, readSchema, wire⟩ := (DateStream.read_iff _ _ _).mp streamRead
  obtain ⟨fieldEq, rfl⟩ := Prod.mk.inj (Except.ok.inj (schema.symm.trans readSchema))
  rw [← fieldEq] at wire
  have equal := corresponding_eq wire index.span.source streamWf matched
    (List.mapM_eq_ok_iff_forall₂.mp sequential)
  rw [← equal]
  exact readAt_sequential index sequential n

end Silmaril.Proofs.Formats.Arrow.DateFile
