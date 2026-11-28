module

public import Silmaril.Formats.Arrow.FileReader.FooterOnly.Defs
import Silmaril.Formats.Arrow.FileReader.Thms
import Silmaril.Proofs.Formats.Arrow.FileReader.FooterOnly.Index

@[expose] public section

namespace Silmaril.Formats.Arrow.FileReader.FooterOnly

/-- The retained declarations and blocks come from the exact bounded footer. -/
theorem readIndex_exact {limits : Limits} {input : KBytes} {index : Index input}
    (read : readIndex limits input = .ok index) :
    FileReader.readFooterSpan limits input = .ok index.span ∧
      readFileFooter limits (input.slice index.span.start index.span.length) = .ok index.footer ∧
      readEnvelope limits input (index.span.start - 8) = .ok .eos ∧
      checkFirstRecord limits input index.footer.blocks = .ok () :=
  Proofs.Formats.Arrow.FileReader.FooterOnly.readIndex_exact read

theorem Index.footer_bytes_exact {input : KBytes} (index : Index input) :
    (input.slice index.span.start index.span.length).toList =
      (input.toList.drop index.span.start).take index.span.length :=
  index.span.bytes_exact

/-- Footer order is the physical order, and the checked ranges do not overlap. -/
theorem Index.block_order {input : KBytes} (index : Index input) :
    List.Pairwise (fun earlier later : FileBlock => earlier.endOffset ≤ later.offset)
      index.footer.blocks :=
  index.fits.block_order

/-- With no blocks, the eight-byte file header is followed by modern EOS. -/
theorem readIndex_schema_only {limits : Limits} {input : KBytes} {index : Index input}
    (read : readIndex limits input = .ok index) (empty : index.footer.blocks = []) :
    index.span.start = 16 ∧ readEnvelope limits input 8 = .ok .eos :=
  Proofs.Formats.Arrow.FileReader.FooterOnly.readIndex_schema_only read empty

/-- A nonempty index starts at byte 8 with a checked RecordBatch Message. -/
theorem readIndex_firstRecord {limits : Limits} {input : KBytes} {index : Index input}
    {block : FileBlock} {rest : List FileBlock} (read : readIndex limits input = .ok index)
    (first : index.footer.blocks = block :: rest) :
    block.offset = 8 ∧
      readEnvelope limits input 8 = .ok (.metadata (block.metadataLength - 8)) ∧
      ∃ record, readMessage limits (input.slice 16 (block.metadataLength - 8)) =
        .ok ⟨.recordBatch record, block.bodyLength⟩ :=
  Proofs.Formats.Arrow.FileReader.FooterOnly.readIndex_firstRecord read first

/-- The selected entry uses the original file's prefix, metadata and body. -/
theorem Index.readBatchAt_exact {input : KBytes} (index : Index input) {limits : Limits} {n : Nat}
    {frame : BatchFrame index.footer.fields} (read : index.readBatchAt limits n = .ok (some frame)) :
    ∃ block, index.footer.blocks[n]? = some block ∧
      8 ≤ block.offset ∧ block.endOffset ≤ index.span.start ∧
      readEnvelope limits input block.offset = .ok (.metadata (block.metadataLength - 8)) ∧
      (input.slice (block.offset + 8) (block.metadataLength - 8)).toList =
        (input.toList.drop (block.offset + 8)).take (block.metadataLength - 8) ∧
      readMessage limits (input.slice (block.offset + 8) (block.metadataLength - 8)) =
        .ok ⟨.recordBatch frame.metadata, block.bodyLength⟩ ∧
      frame.body.len = block.bodyLength ∧ frame.body.toList =
        (input.toList.drop (block.offset + block.metadataLength)).take block.bodyLength :=
  Proofs.Formats.Arrow.FileReader.FooterOnly.readBatchAt_exact index read

theorem Index.readRowsAt_exact {input : KBytes} (index : Index input) {limits : ObservationLimits}
    {n : Nat} {rows : List Row} (read : index.readRowsAt limits n = .ok (some rows)) :
    ∃ frame, index.readBatchAt limits.ipc n = .ok (some frame) ∧
      decodeBatch limits frame = .ok rows :=
  Proofs.Formats.Arrow.FileReader.FooterOnly.readRowsAt_exact index read

end Silmaril.Formats.Arrow.FileReader.FooterOnly
