module

public import Silmaril.Formats.Arrow.DateBatch.Defs
import Silmaril.Formats.Arrow.DateValues.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.DateBatch

open Silmaril Silmaril.Formats.Arrow Silmaril.Formats.Arrow.DateBatch

private theorem mapError_ok_iff {E F A : Type} (f : E → F) (result : Except E A) (value : A) :
    result.mapError f = .ok value ↔ result = .ok value := by
  cases result <;> simp [Except.mapError]

theorem decode_iff (limits : Limits) (schemaMetadata recordMetadata body : KBytes)
    (dates : DateValues.Column) :
    decode limits schemaMetadata recordMetadata body = .ok dates ↔
      ∃ endian name nullable unit batch view,
        SchemaReader.readMessage limits schemaMetadata =
          .ok ⟨endian, [⟨name, nullable, .date unit⟩]⟩ ∧
        readMessage limits recordMetadata = .ok ⟨.recordBatch batch, body.len⟩ ∧
        body.len % 8 = 0 ∧
        DateValues.batchView limits batch body = .ok view ∧
        DateValues.check limits (dateDecoder unit) (descriptor endian unit nullable) view = .ok () ∧
        DateValues.ColumnWire (dateDecoder unit) view dates := by
  cases schemaRead : SchemaReader.readMessage limits schemaMetadata with
  | error cause => simp [decode, schemaRead, Except.mapError, bind, Except.bind]
  | ok schema =>
    obtain ⟨endian, fields⟩ := schema
    cases fields with
    | nil => simp [decode, schemaRead, Except.mapError, bind, Except.bind]
    | cons field rest =>
      cases rest with
      | cons next rest => simp [decode, schemaRead, Except.mapError, bind, Except.bind]
      | nil =>
        obtain ⟨name, nullable, kind⟩ := field
        cases kind with
        | primitive kind => simp [decode, schemaRead, Except.mapError, bind, Except.bind]
        | date unit =>
          cases recordRead : readMessage limits recordMetadata with
          | error cause =>
            simp [decode, schemaRead, recordRead, Except.mapError, bind, Except.bind]
          | ok message =>
            obtain ⟨header, length⟩ := message
            cases header with
            | schema fields =>
              simp [decode, schemaRead, recordRead, Except.mapError, bind, Except.bind]
            | recordBatch batch =>
              by_cases same : length = body.len
              · subst length
                by_cases aligned : body.len % 8 = 0
                · have bound : decode limits schemaMetadata recordMetadata body =
                      (DateValues.decodeBatch limits (dateDecoder unit)
                        (descriptor endian unit nullable) batch body).mapError Error.values := by
                    simp [decode, schemaRead, recordRead, aligned, bind, Except.bind, Except.mapError]
                  rw [bound, mapError_ok_iff]
                  simpa [-Bool.exists_bool, aligned] using
                    (DateValues.decodeBatch_iff limits (dateDecoder unit)
                      (descriptor endian unit nullable) batch body dates)
                · simp [-Bool.exists_bool, decode, schemaRead, recordRead, aligned, Except.mapError,
                    bind, Except.bind]
              · simp [-Bool.exists_bool, decode, schemaRead, recordRead, same, Except.mapError,
                  bind, Except.bind]

theorem decode_counts {limits : Limits} {schemaMetadata recordMetadata body : KBytes}
    {dates : DateValues.Column} (decoded : decode limits schemaMetadata recordMetadata body = .ok dates) :
    ∃ batch node, readMessage limits recordMetadata = .ok ⟨.recordBatch batch, body.len⟩ ∧
      batch.nodes = [node] ∧ dates.length = batch.rowCount ∧
      dates.countP Option.isNone = node.nullCount := by
  obtain ⟨_, _, _, _, batch, _, _, read, _, arranged, _, wire⟩ := (decode_iff _ _ _ _ _).mp decoded
  obtain ⟨node, _, _, nodes, _, rows, _, rfl⟩ := DateValues.batchView_layout arranged
  exact ⟨batch, node, read, nodes, wire.counts.1.trans rows, wire.counts.2⟩

end Silmaril.Proofs.Formats.Arrow.DateBatch
