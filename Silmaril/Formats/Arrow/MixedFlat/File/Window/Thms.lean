module

public import Silmaril.Formats.Arrow.MixedFlat.File.Window.Defs
import Silmaril.Formats.Arrow.FileReader.Thms
import Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Window

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.File.Window

/-- The retained footer and embedded Schema are parsed from the original
carrier, and both yield exactly the same declared fields. -/
theorem readIndex_exact {limits : Arrow.Limits} {input : KBytes} {start stop : Nat}
    {index : Index input start stop} (read : readIndex limits input start stop = .ok index) :
    FileReader.readFooterSpan limits (input.slice start (stop - start)) = .ok index.span ∧
      MixedFlat.readFileFooter limits (input.slice index.footerStart index.span.length) = .ok index.footer ∧
      readEnvelope limits input (start + 8) = .ok (.metadata index.schemaSize) ∧
      MixedFlat.readSchema limits index.schemaMetadata = .ok index.footer.fields ∧
      readEnvelope limits input (index.footerStart - 8) = .ok .eos :=
  Proofs.Formats.Arrow.MixedFlat.File.Window.readIndex_exact read

theorem Index.footer_range {input : KBytes} {start stop : Nat} (index : Index input start stop) :
    start ≤ index.footerStart ∧ index.footerStart + index.span.length + 10 = stop ∧ stop ≤ input.len :=
  Proofs.Formats.Arrow.MixedFlat.File.Window.footer_range index

theorem Index.footer_bytes_exact {input : KBytes} {start stop : Nat} (index : Index input start stop) :
    (input.slice index.footerStart index.span.length).toList =
      (input.toList.drop index.footerStart).take index.span.length :=
  Proofs.Formats.Arrow.MixedFlat.File.Window.footer_bytes_exact index

/-- All three selected ranges fit at their original carrier addresses.
The entire block ends before the eight-byte EOS immediately before the footer. -/
theorem Index.block_ranges {input : KBytes} {start stop : Nat} (index : Index input start stop)
    {block : FileBlock} (member : block ∈ index.footer.blocks) :
    start ≤ block.offset ∧
      block.offset + 8 ≤ block.offset + block.metadataLength ∧
      block.offset + block.metadataLength ≤ block.endOffset ∧
      block.endOffset + 8 ≤ index.footerStart ∧ index.footerStart ≤ stop :=
  Proofs.Formats.Arrow.MixedFlat.File.Window.block_ranges index member

theorem Index.block_order {input : KBytes} {start stop : Nat} (index : Index input start stop) :
    List.Pairwise (fun earlier later : FileBlock => earlier.endOffset ≤ later.offset) index.footer.blocks :=
  index.fits.block_order

/-- The original prefix and the bounded metadata/body octets explain the
indexed observation through the standalone mixed batch reader. -/
theorem Index.readAt_exact {limits : MixedFlat.Limits} {input : KBytes} {start stop : Nat}
    {index : Index input start stop} (checked : readIndex limits.observation.ipc input start stop = .ok index)
    {n : Nat} {observed : MixedFlat.Observed} (read : index.readAt limits n = .ok (some observed)) :
    ∃ block, index.footer.blocks[n]? = some block ∧
      start ≤ block.offset ∧
      block.offset + 8 ≤ block.offset + block.metadataLength ∧
      block.offset + block.metadataLength ≤ block.endOffset ∧
      block.endOffset + 8 ≤ index.footerStart ∧ index.footerStart ≤ stop ∧
      readEnvelope limits.observation.ipc input block.offset = .ok (.metadata (block.metadataLength - 8)) ∧
      (input.slice block.offset 8).toList = (input.toList.drop block.offset).take 8 ∧
      (metadataSlice input block).toList =
        (input.toList.drop (block.offset + 8)).take (block.metadataLength - 8) ∧
      (bodySlice input block).toList =
        (input.toList.drop (block.offset + block.metadataLength)).take block.bodyLength ∧
      MixedFlat.readBatch limits index.schemaMetadata (metadataSlice input block) (bodySlice input block) =
        .ok observed :=
  Proofs.Formats.Arrow.MixedFlat.File.Window.readAt_exact checked read

end Silmaril.Formats.Arrow.MixedFlat.File.Window
