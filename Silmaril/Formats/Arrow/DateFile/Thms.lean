module

public import Silmaril.Formats.Arrow.DateFile.Defs
import Silmaril.Formats.Arrow.FileReader.Thms
import Silmaril.Proofs.Formats.Arrow.DateFile.Index
import Silmaril.Proofs.Formats.Arrow.DateFile.Correspondence

public section

namespace Silmaril.Formats.Arrow.DateFile

/-- Both metadata locations describe the same little-endian DATE field, with
the exact name, nullability and normalized unit stored in the index. -/
theorem readIndex_exact {limits : Limits} {input : KBytes} {index : Index input}
    (admitted : readIndex limits input = .ok index) :
    SchemaReader.readFileFooter limits (input.slice index.span.start index.span.length) =
      .ok ⟨index.schema, index.blocks⟩ ∧
      readEnvelope limits input 8 = .ok (.metadata index.schemaSize) ∧
      SchemaReader.readMessage limits index.schemaMetadata = .ok index.schema ∧
      readEnvelope limits input (index.span.start - 8) = .ok .eos :=
  Proofs.Formats.Arrow.DateFile.readIndex_exact admitted

/-- A successful read selects exactly the original metadata and body octets
and agrees with standalone DATE decoding using the embedded Schema. -/
theorem Index.readAt_exact {limits : Limits} {input : KBytes} {index : Index input}
    (admitted : readIndex limits input = .ok index)
    {n : Nat} {dates : DateValues.Column} (read : index.readAt limits n = .ok (some dates)) :
    ∃ block, index.blocks[n]? = some block ∧
      block.endOffset ≤ index.span.start ∧
      readEnvelope limits input block.offset = .ok (.metadata (block.metadataLength - 8)) ∧
      (metadataSlice input block).toList =
        (input.toList.drop (block.offset + 8)).take (block.metadataLength - 8) ∧
      (bodySlice input block).toList =
        (input.toList.drop (block.offset + block.metadataLength)).take block.bodyLength ∧
      DateBatch.decode limits index.schemaMetadata (metadataSlice input block) (bodySlice input block) =
        .ok dates :=
  Proofs.Formats.Arrow.DateFile.readAt_exact admitted read

theorem Index.readAt_absent_iff {limits : Limits} {input : KBytes} (index : Index input) (n : Nat) :
    index.readAt limits n = .ok none ↔ index.blocks[n]? = none :=
  Proofs.Formats.Arrow.DateFile.readAt_absent_iff index n

/-- The indexed cause is exactly the failure of the selected record. -/
theorem Index.readAt_error_iff {limits : Limits} {input : KBytes} (index : Index input)
    (n : Nat) (cause : BlockError) :
    index.readAt limits n = .error (.batch n cause) ↔
      ∃ block, index.blocks[n]? = some block ∧ readRecord limits input index.field block = .error cause :=
  Proofs.Formats.Arrow.DateFile.readAt_error_iff index n cause

/-- Successful traversal in footer order gives the same indexed observations,
including empty batches and absence. -/
theorem Index.readAt_sequential {limits : Limits} {input : KBytes} (index : Index input)
    {dates : List DateValues.Column}
    (sequential : index.blocks.mapM (readRecord limits input index.field) = .ok dates) (n : Nat) :
    index.readAt limits n = .ok dates[n]? :=
  Proofs.Formats.Arrow.DateFile.readAt_sequential index sequential n

/-- When the normalized Schema and each batch's parsed metadata and body
octets correspond, successful file and stream observations agree at every index. -/
theorem Index.readAt_stream {limits : Limits} {input : KBytes} (index : Index input)
    {stream : KBytes} {start : Nat} {observed : DateStream.Stream} {dates : List DateValues.Column}
    (schema : DateStream.readSchema limits stream = .ok (index.field, start))
    (matched : BatchesCorrespond limits input stream start index.blocks)
    (streamRead : DateStream.read limits stream = .ok observed)
    (sequential : index.blocks.mapM (readRecord limits input index.field) = .ok dates) (n : Nat) :
    index.readAt limits n = .ok observed.batches[n]? :=
  Proofs.Formats.Arrow.DateFile.readAt_stream index schema matched streamRead sequential n

end Silmaril.Formats.Arrow.DateFile
