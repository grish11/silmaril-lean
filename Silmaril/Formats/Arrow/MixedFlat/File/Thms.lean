module

public import Silmaril.Formats.Arrow.MixedFlat.File.Defs
import Silmaril.Formats.Arrow.FileReader.Thms
import Silmaril.Proofs.Formats.Arrow.MixedFlat.File

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.File

/-- On admission the file's embedded Schema agrees exactly with the footer,
and the footer is immediately preceded by the modern EOS envelope. -/
theorem readIndex_exact {limits : Arrow.Limits} {input : KBytes} {index : Index input}
    (read : readIndex limits input = .ok index) :
    MixedFlat.readFileFooter limits (input.slice index.span.start index.span.length) = .ok index.footer ∧
      readEnvelope limits input 8 = .ok (.metadata index.schemaSize) ∧
      MixedFlat.readSchema limits index.schemaMetadata = .ok index.footer.fields ∧
      readEnvelope limits input (index.span.start - 8) = .ok .eos :=
  Proofs.Formats.Arrow.MixedFlat.File.readIndex_exact read

/-- The block's aligned prefix, metadata and body fit before the footer. -/
theorem Index.block_range {input : KBytes} (index : Index input)
    {block : FileBlock} (member : block ∈ index.footer.blocks) :
    16 + index.schemaSize ≤ block.offset ∧ block.offset % 8 = 0 ∧ 8 ≤ block.metadataLength ∧
      block.metadataLength % 8 = 0 ∧ block.bodyLength % 8 = 0 ∧ block.endOffset ≤ index.span.start :=
  index.fits.block_range member

theorem Index.block_order {input : KBytes} (index : Index input) :
    List.Pairwise (fun earlier later : FileBlock => earlier.endOffset ≤ later.offset) index.footer.blocks :=
  index.fits.block_order

/-- A successful indexed observation comes from the selected footer entry.
The declared metadata and body contain precisely the source octets, and
standalone decoding with the embedded Schema gives the same observation. -/
theorem Index.readAt_exact {limits : MixedFlat.Limits} {input : KBytes} {index : Index input}
    (checked : readIndex limits.observation.ipc input = .ok index)
    {n : Nat} {observed : MixedFlat.Observed} (read : index.readAt limits n = .ok (some observed)) :
    ∃ block, index.footer.blocks[n]? = some block ∧
      block.endOffset ≤ index.span.start ∧
      readEnvelope limits.observation.ipc input block.offset = .ok (.metadata (block.metadataLength - 8)) ∧
      (metadataSlice input block).toList =
        (input.toList.drop (block.offset + 8)).take (block.metadataLength - 8) ∧
      (bodySlice input block).toList =
        (input.toList.drop (block.offset + block.metadataLength)).take block.bodyLength ∧
      MixedFlat.readBatch limits index.schemaMetadata (metadataSlice input block) (bodySlice input block) =
        .ok observed :=
  Proofs.Formats.Arrow.MixedFlat.File.readAt_exact checked read

/-- An independent indexed read agrees with a successful sequential
traversal of checked blocks, including zero-row batches and absent entries. -/
theorem Index.readAt_sequential {limits : MixedFlat.Limits} {input : KBytes} (index : Index input)
    {observed : List MixedFlat.Observed}
    (sequential : index.footer.blocks.mapM (readRecord limits input index.footer.fields) = .ok observed)
    (n : Nat) : index.readAt limits n = .ok observed[n]? :=
  Proofs.Formats.Arrow.MixedFlat.File.readAt_sequential index sequential n

end Silmaril.Formats.Arrow.MixedFlat.File
