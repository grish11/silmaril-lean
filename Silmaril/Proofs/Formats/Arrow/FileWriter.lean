module

public import Silmaril.Formats.Arrow.FileWriter.Defs
import Silmaril.Formats.Arrow.StreamWriter.Thms
import Silmaril.Formats.Arrow.FooterWriter.Thms
import Silmaril.Formats.Arrow.Writer.Thms
import Silmaril.Formats.Arrow.MetadataWriter.Thms
import Init.Data.List.Monadic
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.FileWriter

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.FileWriter

private theorem append_length (left right : KBytes) : (left ++ right).len = left.len + right.len := rfl

private theorem emitRecord_fits {limits : ObservationLimits} {fields : List Field}
    {input : Writer.BatchInput} {record : RecordFrame}
    (written : emitRecord limits fields input = .ok record) : record.Fits := by
  by_cases schema : input.fields = fields
  · cases physical : Writer.emitBatch limits input with
    | error error => simp [emitRecord, schema, physical, bind, Except.bind] at written
    | ok batch =>
      let message : Message := ⟨.recordBatch batch.metadata, batch.body.len⟩
      cases framed : StreamWriter.emitFrame limits.ipc message batch.body with
      | error error =>
        simp [emitRecord, schema, physical, show StreamWriter.emitFrame limits.ipc
          ⟨.recordBatch batch.metadata, batch.body.len⟩ batch.body = .error error from framed,
          bind, Except.bind] at written
      | ok wire =>
        simp [emitRecord, schema, physical, show StreamWriter.emitFrame limits.ipc
          ⟨.recordBatch batch.metadata, batch.body.len⟩ batch.body = .ok wire from framed,
          bind, Except.bind, pure, Except.pure] at written
        subst record
        obtain ⟨_, extent, _⟩ := StreamWriter.emitFrame_exact framed
        have metaAligned := (MetadataWriter.wireSize_aligned message).2
        have bodyAligned := (Writer.emitBatch_roundtrip physical).2.1
        have aligned : (8 + MetadataWriter.wireSize message) % 8 = 0 := by omega
        exact ⟨extent, by change 8 ≤ 8 + MetadataWriter.wireSize message; omega,
          aligned, bodyAligned⟩
  · simp [emitRecord, schema, bind, Except.bind] at written

private theorem mapRecords_fits {limits : ObservationLimits} {fields : List Field}
    {inputs : List Writer.BatchInput} {records : List RecordFrame}
    (written : inputs.mapM (emitRecord limits fields) = .ok records) :
    records.length = inputs.length ∧ ∀ record ∈ records, record.Fits := by
  induction inputs generalizing records with
  | nil =>
    have empty : records = [] := by simpa [pure, Except.pure] using written.symm
    subst records
    simp
  | cons input tail ih =>
    cases first : emitRecord limits fields input with
    | error error => simp [first, bind, Except.bind] at written
    | ok record =>
      cases rest : tail.mapM (emitRecord limits fields) with
      | error error => simp [first, rest, bind, Except.bind] at written
      | ok output =>
        simp [first, rest, bind, Except.bind, pure, Except.pure] at written
        subst records
        obtain ⟨length, fits⟩ := ih rest
        refine ⟨by simp [length], fun item member => ?_⟩
        rcases List.mem_cons.mp member with same | inRest
        · subst item
          exact emitRecord_fits first
        · exact fits item inRest

theorem packRecords_exact (offset : Nat) (records : List RecordFrame)
    (aligned : offset % 8 = 0) (fits : ∀ record ∈ records, record.Fits) :
    let (blocks, wire) := packRecords offset records
    FileReader.BlocksFit (offset + wire.len) offset blocks ∧ blocks.length = records.length ∧
      blocks.map (fun block => (block.metadataLength, block.bodyLength)) =
        records.map (fun record => (record.metadataLength, record.bodyLength)) := by
  induction records generalizing offset with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons first rest ih =>
    let block := first.block offset
    obtain ⟨extent, hasPrefix, metaAlign, bodyAlign⟩ := fits first (by simp)
    have advance : block.endOffset = offset + first.bytes.len := by
      change offset + first.metadataLength + first.bodyLength = offset + first.bytes.len
      omega
    have nextAligned : block.endOffset % 8 = 0 := by
      change (offset + first.metadataLength + first.bodyLength) % 8 = 0
      omega
    have next := ih block.endOffset nextAligned (fun record member => fits record (by simp [member]))
    cases packed : packRecords block.endOffset rest with
    | mk blocks wire =>
      rw [packed] at next
      change FileReader.BlocksFit (block.endOffset + wire.len) block.endOffset blocks ∧
        blocks.length = rest.length ∧
        blocks.map (fun block => (block.metadataLength, block.bodyLength)) =
          rest.map (fun record => (record.metadataLength, record.bodyLength)) at next
      have sameEnd : offset + (first.bytes ++ wire).len = block.endOffset + wire.len := by
        rw [append_length, advance]
        omega
      simp only [packRecords, show packRecords (first.block offset).endOffset rest = (blocks, wire)
        from packed, sameEnd, FileReader.BlocksFit, List.length_cons]
      refine ⟨⟨rfl, aligned, hasPrefix, metaAlign, bodyAlign,
        by change block.endOffset ≤ block.endOffset + wire.len; omega, next.1⟩, ?_, ?_⟩
      · rw [next.2.1]
      · simpa only [List.map_cons, RecordFrame.block] using
          congrArg ((first.metadataLength, first.bodyLength) :: ·) next.2.2

theorem assemble_extent {limits : ObservationLimits} {fields : List Field}
    {inputs : List Writer.BatchInput} {plan : Assembly}
    (written : assemble limits fields inputs = .ok plan) :
    plan.footer.fields = fields ∧ plan.footer.blocks.length = inputs.length ∧
      FileReader.BlocksFit plan.footerStart plan.schemaEnd plan.footer.blocks ∧
      plan.footerLength = FooterWriter.wireSize plan.footer ∧
      plan.footerStart + plan.footerLength + 10 = plan.bytes.len := by
  by_cases cap : inputs.length > limits.ipc.batches
  · simp [assemble, cap, bind, Except.bind] at written
  cases budget : Body.checkBudget limits fields.length (inputs.map (·.rowCount)).sum with
  | error error => simp [assemble, cap, budget, bind, Except.bind] at written
  | ok success =>
    cases schemaRead : StreamWriter.emitFrame limits.ipc ⟨.schema fields, 0⟩ KBytes.empty with
    | error error => simp [assemble, cap, budget, schemaRead, bind, Except.bind] at written
    | ok schema =>
      cases recordsRead : inputs.mapM (emitRecord limits fields) with
      | error error => simp [assemble, cap, budget, schemaRead, recordsRead, bind, Except.bind] at written
      | ok records =>
        cases packed : packRecords (8 + schema.len) records with
        | mk blocks body =>
          cases encoded : FooterWriter.serialize limits.ipc ⟨fields, blocks⟩ with
          | error error =>
            simp [assemble, cap, budget, schemaRead, recordsRead, packed, encoded, bind, Except.bind] at written
          | ok metadata =>
            simp [assemble, cap, budget, schemaRead, recordsRead, packed, encoded, bind, Except.bind,
              pure, Except.pure] at written
            subst plan
            obtain ⟨_, schemaLength, _⟩ := StreamWriter.emitFrame_exact schemaRead
            have metaAligned := (MetadataWriter.wireSize_aligned ⟨.schema fields, 0⟩).2
            have start : (8 + schema.len) % 8 = 0 := by
              change schema.len = 8 + MetadataWriter.wireSize ⟨.schema fields, 0⟩ + 0 at schemaLength
              omega
            obtain ⟨count, fits⟩ := mapRecords_fits recordsRead
            have ranges := packRecords_exact (8 + schema.len) records start fits
            rw [packed] at ranges
            have footerLength := (FooterWriter.serialize_extent encoded).2.1
            refine ⟨rfl, ranges.2.1.trans count, ranges.1, footerLength, ?_⟩
            change 8 + schema.len + body.len + metadata.len + 10 =
              (KBytes.leaf 8 FileReader.magic ++ (schema ++ (body ++ (metadata ++
                (KBytes.leaf 4 metadata.len ++ KBytes.leaf 6 FileReader.magic))))).len
            simp only [append_length, KBytes.len.eq_1]
            omega

theorem emit_index_exact {limits : ObservationLimits} {fields : List Field}
    {inputs : List Writer.BatchInput} {wire : KBytes}
    (written : emit limits fields inputs = .ok wire) :
    ∃ plan : Assembly, assemble limits fields inputs = .ok plan ∧ plan.bytes = wire ∧
      ∃ index : FileReader.Index wire, FileReader.readIndex limits.ipc wire = .ok index ∧
        index.footer = plan.footer ∧ index.schemaEnd = plan.schemaEnd ∧
        index.span.start = plan.footerStart ∧ index.span.length = plan.footerLength := by
  cases planned : assemble limits fields inputs with
  | error error => simp [emit, planned, bind, Except.bind] at written
  | ok plan =>
    cases checked : FileReader.readIndex limits.ipc plan.bytes with
    | error error => simp [emit, planned, checked, bind, Except.bind] at written
    | ok index =>
      simp [emit, planned, checked, bind, Except.bind, pure, Except.pure] at written
      split at written <;> try contradiction
      rename_i same
      cases written
      exact ⟨plan, rfl, rfl, index, checked, same⟩

end Silmaril.Proofs.Formats.Arrow.FileWriter
