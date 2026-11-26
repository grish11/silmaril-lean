module

public import Silmaril.Formats.Arrow.FileWriter.Defs
import Silmaril.Proofs.Formats.Arrow.FileWriter

@[expose] public section

namespace Silmaril.Formats.Arrow.FileWriter

theorem packRecords_exact (offset : Nat) (records : List RecordFrame)
    (aligned : offset % 8 = 0) (fits : ∀ record ∈ records, record.Fits) :
    let (blocks, wire) := packRecords offset records
    FileReader.BlocksFit (offset + wire.len) offset blocks ∧ blocks.length = records.length ∧
      blocks.map (fun block => (block.metadataLength, block.bodyLength)) =
        records.map (fun record => (record.metadataLength, record.bodyLength)) :=
  Proofs.Formats.Arrow.FileWriter.packRecords_exact offset records aligned fits

/-- The planned blocks are contiguous, aligned and ordered, with one block
per input batch. The footer ends immediately before the length and magic. -/
theorem assemble_extent {limits : ObservationLimits} {fields : List Field}
    {inputs : List Writer.BatchInput} {plan : Assembly}
    (written : assemble limits fields inputs = .ok plan) :
    plan.footer.fields = fields ∧ plan.footer.blocks.length = inputs.length ∧
      FileReader.BlocksFit plan.footerStart plan.schemaEnd plan.footer.blocks ∧
      plan.footerLength = FooterWriter.wireSize plan.footer ∧
      plan.footerStart + plan.footerLength + 10 = plan.bytes.len :=
  Proofs.Formats.Arrow.FileWriter.assemble_extent written

/-- A successful checked file write round-trips its entire planned footer
and all byte boundaries to the existing file reader. -/
theorem emit_index_exact {limits : ObservationLimits} {fields : List Field}
    {inputs : List Writer.BatchInput} {wire : KBytes}
    (written : emit limits fields inputs = .ok wire) :
    ∃ plan : Assembly, assemble limits fields inputs = .ok plan ∧ plan.bytes = wire ∧
      ∃ index : FileReader.Index wire, FileReader.readIndex limits.ipc wire = .ok index ∧
        index.footer = plan.footer ∧ index.schemaEnd = plan.schemaEnd ∧
        index.span.start = plan.footerStart ∧ index.span.length = plan.footerLength :=
  Proofs.Formats.Arrow.FileWriter.emit_index_exact written

end Silmaril.Formats.Arrow.FileWriter
