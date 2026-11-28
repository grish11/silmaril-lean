module

public import Silmaril.Formats.Arrow.FileWriter.Defs
import Silmaril.Proofs.Formats.Arrow.FileWriter
import Silmaril.Formats.Arrow.MetadataWriter.Thms
import Silmaril.Formats.Arrow.StreamWriter.Thms
import Init.Data.List.Monadic
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.FileWriter

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.FileWriter
open Silmaril.Formats.Arrow.StreamWriter (Window)

private theorem window_inside {part middle whole : KBytes} {offset start : Nat}
    (inner : Window part middle offset) (outer : Window middle whole start) :
    Window part whole (start + offset) := by
  induction outer with
  | self => simpa only [Nat.zero_add] using inner
  | left _ back ih => exact .left ih back
  | right front _ ih => simpa only [Nat.add_assoc] using Window.right front ih

private theorem transfer_batch {limits : ObservationLimits} {fromFields toFields : List Field}
    (schema : fromFields = toFields) {batch : BatchFrame fromFields} {raw : KBytes}
    {count : Nat} {rows : List Row}
    (layout : validateBatch fromFields batch.metadata raw = .ok batch)
    (rowCount : batch.metadata.rowCount = count)
    (decoded : decodeBatch limits batch = .ok rows) :
    let transported : BatchFrame toFields := schema ▸ batch
    validateBatch toFields batch.metadata raw = .ok transported ∧
      transported.metadata.rowCount = count ∧ decodeBatch limits transported = .ok rows := by
  cases schema
  exact ⟨layout, rowCount, decoded⟩

private theorem readRecord_at {limits : ObservationLimits} {wire : KBytes}
    (index : FileReader.Index wire) {input : Writer.BatchInput} {record : RecordFrame} {offset : Nat}
    (written : emitRecord limits index.footer.fields input = .ok record)
    (position : Window record.bytes wire offset) (aligned : offset % 8 = 0)
    (member : record.block offset ∈ index.footer.blocks) :
    ∃ batch, index.readBlock limits.ipc (record.block offset) member = .ok batch ∧
      (record.block offset).endOffset = offset + record.bytes.len ∧
      (record.block offset).endOffset % 8 = 0 ∧
      batch.metadata.rowCount = input.rowCount ∧ decodeBatch limits batch = .ok input.observe ∧
      input.observe.length = input.rowCount := by
  by_cases schema : input.fields = index.footer.fields
  · cases physical : Writer.emitBatch limits input with
    | error error => simp [emitRecord, schema, physical, bind, Except.bind] at written
    | ok frame =>
      let message : Message := ⟨.recordBatch frame.metadata, frame.body.len⟩
      let size := MetadataWriter.wireSize message
      cases framed : StreamWriter.emitFrame limits.ipc message frame.body with
      | error error =>
        simp [emitRecord, schema, physical, show StreamWriter.emitFrame limits.ipc
          ⟨.recordBatch frame.metadata, frame.body.len⟩ frame.body = .error error from framed,
          bind, Except.bind] at written
      | ok part =>
        simp [emitRecord, schema, physical, show StreamWriter.emitFrame limits.ipc
          ⟨.recordBatch frame.metadata, frame.body.len⟩ frame.body = .ok part from framed,
          bind, Except.bind, pure, Except.pure] at written
        subst record
        obtain ⟨raw, batch, _, length, frameAligned, envelope, metadata, body, layout, count, rows,
          observedLength⟩ := StreamWriter.emitBatchFrame_at physical framed position aligned
        obtain ⟨layout', count', rows'⟩ := transfer_batch schema layout count rows
        refine ⟨schema ▸ batch, ?_, ?_, ?_, count', rows', observedLength⟩
        ·
          simp [FileReader.Index.readBlock, RecordFrame.block, envelope, metadata, layout',
            show offset + (8 + size) = offset + 8 + size by omega, body, size, message,
            bind, Except.bind]
        · change offset + (8 + size) + frame.body.len = offset + part.len
          change part.len = 8 + size + frame.body.len at length
          omega
        · change (offset + (8 + size) + frame.body.len) % 8 = 0
          change part.len = 8 + size + frame.body.len at length
          omega
  · simp [emitRecord, schema, bind, Except.bind] at written

private theorem readPacked {limits : ObservationLimits} {wire : KBytes}
    (index : FileReader.Index wire)
    {inputs : List Writer.BatchInput} {records : List RecordFrame} {offset : Nat}
    (written : inputs.mapM (emitRecord limits index.footer.fields) = .ok records)
    (position : Window (packRecords offset records).2 wire offset) (aligned : offset % 8 = 0)
    (member : ∀ block ∈ (packRecords offset records).1, block ∈ index.footer.blocks) :
    ∃ batches, ((packRecords offset records).1.attachWith _ member).mapM
        (fun block => index.readBlock limits.ipc block.val block.property) = .ok batches ∧
      batches.map (·.metadata.rowCount) = inputs.map (·.rowCount) ∧
      batches.mapM (decodeBatch limits) = .ok (inputs.map Writer.BatchInput.observe) ∧
      (inputs.map Writer.BatchInput.observe).map List.length = inputs.map (·.rowCount) := by
  induction inputs generalizing records offset with
  | nil =>
    have empty : records = [] := by simpa [pure, Except.pure] using written.symm
    subst records
    exact ⟨[], rfl, rfl, rfl, rfl⟩
  | cons input rest ih =>
    cases first : emitRecord limits index.footer.fields input with
    | error error => simp [first, bind, Except.bind] at written
    | ok record =>
      cases tail : rest.mapM (emitRecord limits index.footer.fields) with
      | error error => simp [first, tail, bind, Except.bind] at written
      | ok records' =>
        simp [first, tail, bind, Except.bind, pure, Except.pure] at written
        subst records
        let block := record.block offset
        let packed := packRecords block.endOffset records'
        change Window (record.bytes ++ packed.2) wire offset at position
        have headAt : Window record.bytes wire offset :=
          Nat.add_zero offset ▸ window_inside (.left .self packed.2) position
        have prefixMember : ∀ b ∈ block :: packed.1, b ∈ index.footer.blocks :=
          fun b h => member b h
        have headMember : block ∈ index.footer.blocks := prefixMember _ List.mem_cons_self
        obtain ⟨batch, read, next, nextAligned, count, rows, observedLength⟩ :=
          readRecord_at index first headAt aligned headMember
        have tailAt : Window packed.2 wire block.endOffset := by
          rw [next]
          exact window_inside (Window.right record.bytes .self) position
        have tailMember : ∀ b ∈ packed.1, b ∈ index.footer.blocks := fun b h =>
          prefixMember b (List.mem_cons_of_mem _ h)
        obtain ⟨batches, batchesRead, counts, observed, lengths⟩ :=
          ih tail tailAt nextAligned tailMember
        refine ⟨batch :: batches, ?_, ?_, ?_, ?_⟩
        · change ((block :: packed.1).attachWith _ prefixMember).mapM _ = _
          simp only [List.attachWith_cons, List.mapM_cons]
          rw [read, show (packed.1.attachWith _ tailMember).mapM
            (fun b => index.readBlock limits.ipc b.val b.property) = .ok batches from batchesRead]
          rfl
        · simp [count, counts]
        · simp [rows, observed, bind, Except.bind, pure, Except.pure]
        · simp [observedLength, lengths]

theorem emit_roundtrip {limits : ObservationLimits} {fields : List Field}
    {inputs : List Writer.BatchInput} {wire : KBytes} (written : emit limits fields inputs = .ok wire) :
    ∃ (index : FileReader.Index wire) (batches : List (BatchFrame index.footer.fields)),
      FileReader.readIndex limits.ipc wire = .ok index ∧ index.footer.fields = fields ∧
      index.readBatches limits.ipc = .ok batches ∧
      batches.map (·.metadata.rowCount) = inputs.map (·.rowCount) ∧
      FileReader.readRows limits wire = .ok ⟨fields, inputs.map Writer.BatchInput.observe⟩ ∧
      (inputs.map Writer.BatchInput.observe).map List.length = inputs.map (·.rowCount) := by
  obtain ⟨plan, planned, rfl, index, checked, exactFooter, _⟩ := emit_index_exact written
  by_cases cap : inputs.length > limits.ipc.batches
  · simp [assemble, cap, bind, Except.bind] at planned
  cases budget : Body.checkBudget limits fields.length (inputs.map (·.rowCount)).sum with
  | error error => simp [assemble, cap, budget, bind, Except.bind] at planned
  | ok success =>
    cases success
    cases schemaRead : StreamWriter.emitFrame limits.ipc ⟨.schema fields, 0⟩ KBytes.empty with
    | error error => simp [assemble, cap, budget, schemaRead, bind, Except.bind] at planned
    | ok schema =>
      cases recordsRead : inputs.mapM (emitRecord limits fields) with
      | error error => simp [assemble, cap, budget, schemaRead, recordsRead, bind, Except.bind] at planned
      | ok records =>
        let offset := 8 + schema.len
        let packed := packRecords offset records
        cases packedEq : packRecords (8 + schema.len) records with
        | mk blocks body =>
          cases encoded : FooterWriter.serialize limits.ipc ⟨fields, blocks⟩ with
          | error error =>
            simp [assemble, cap, budget, schemaRead, recordsRead, packedEq, encoded,
              bind, Except.bind] at planned
          | ok metadata =>
            simp [assemble, cap, budget, schemaRead, recordsRead, packedEq, encoded,
              bind, Except.bind, pure, Except.pure] at planned
            subst plan
            have fieldsEq : index.footer.fields = fields := congrArg FileFooter.fields exactFooter
            have blocksEq : index.footer.blocks = packed.1 := by
              change index.footer.blocks = (packRecords (8 + schema.len) records).1
              rw [packedEq]
              exact congrArg FileFooter.blocks exactFooter
            let carrier := KBytes.leaf 8 FileReader.magic ++ (schema ++ (body ++
              (metadata ++ (KBytes.leaf 4 metadata.len ++ KBytes.leaf 6 FileReader.magic))))
            have position : Window packed.2 carrier offset := by
              change Window (packRecords (8 + schema.len) records).2 carrier (8 + schema.len)
              rw [packedEq]
              simpa only [Nat.add_zero, KBytes.len.eq_1] using
                Window.right (KBytes.leaf 8 FileReader.magic)
                  (Window.right schema (Window.left (Window.self (part := body))
                    (metadata ++ (KBytes.leaf 4 metadata.len ++ KBytes.leaf 6 FileReader.magic))))
            obtain ⟨_, schemaLength, _⟩ := StreamWriter.emitFrame_exact schemaRead
            have metaAligned := (MetadataWriter.wireSize_aligned ⟨.schema fields, 0⟩).2
            have aligned : offset % 8 = 0 := by
              change (8 + schema.len) % 8 = 0
              change schema.len = 8 + MetadataWriter.wireSize ⟨.schema fields, 0⟩ + 0 at schemaLength
              omega
            have member : ∀ block ∈ packed.1, block ∈ index.footer.blocks := by
              rw [blocksEq]
              exact fun _ h => h
            have recordsRead' : inputs.mapM (emitRecord limits index.footer.fields) = .ok records :=
              fieldsEq.symm ▸ recordsRead
            obtain ⟨batches, read, counts, observed, lengths⟩ :=
              readPacked index recordsRead' position aligned member
            have batchesRead : index.readBatches limits.ipc = .ok batches := by
              unfold FileReader.Index.readBatches
              have attached : index.footer.blocks.attach = packed.1.attachWith _ member :=
                List.attachWith_congr blocksEq
              rw [attached]
              exact read
            refine ⟨index, batches, checked, fieldsEq, batchesRead, counts, ?_, lengths⟩
            simp [FileReader.readRows, checked, batchesRead, fieldsEq, counts, budget, observed,
              bind, Except.bind, pure, Except.pure]

end Silmaril.Proofs.Formats.Arrow.FileWriter
