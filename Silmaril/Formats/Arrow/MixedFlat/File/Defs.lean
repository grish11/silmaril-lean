module

public import Silmaril.Formats.Arrow.FileReader.Defs
public import Silmaril.Formats.Arrow.MixedFlat.Defs

/-! Checked random access for flat mixed Arrow IPC V5 files. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.File

inductive BlockError where
  | envelope (cause : Arrow.Error)
  | metadataLength
  | metadata (cause : MixedFlat.MetadataError)
  | bodyLength
  | body (cause : Arrow.Error)
  | decode (cause : MixedFlat.Error)
  deriving DecidableEq, Repr

inductive Error where
  | footer (cause : Arrow.Error)
  | schema (cause : Arrow.Error)
  | schemaMismatch
  | blockLayout
  | eos (cause : Arrow.Error)
  | batch (index : Nat) (cause : BlockError)
  deriving DecidableEq, Repr

/-- A footer index over the same immutable input used to admit its schema and ranges. -/
structure Index (input : KBytes) where
  span : FileReader.FooterSpan input
  footer : MixedFlat.FileFooter
  schemaSize : Nat
  fits : FileReader.BlocksFit span.start (16 + schemaSize) footer.blocks

def Index.schemaMetadata {input : KBytes} (index : Index input) : KBytes :=
  input.slice 16 index.schemaSize

def metadataSlice (input : KBytes) (block : FileBlock) : KBytes :=
  input.slice (block.offset + 8) (block.metadataLength - 8)

def bodySlice (input : KBytes) (block : FileBlock) : KBytes :=
  input.slice (block.offset + block.metadataLength) block.bodyLength

/-- Check file framing and exact agreement of the footer with the embedded
Schema. All blocks must be contiguous and followed by the EOS before the footer. -/
def readIndex (limits : Arrow.Limits) (input : KBytes) : Except Error (Index input) := do
  let span ← (FileReader.readFooterSpan limits input).mapError .footer
  let footer ← (MixedFlat.readFileFooter limits (input.slice span.start span.length)).mapError .footer
  let envelope ← (readEnvelope limits input 8).mapError .schema
  let .metadata size := envelope | throw (.schema (.malformed .schemaOrder))
  if 16 + size + 8 > span.start then throw (.schema (.malformed .truncated))
  let fields ← (MixedFlat.readSchema limits (input.slice 16 size)).mapError .schema
  if fields ≠ footer.fields then throw .schemaMismatch
  if fits : FileReader.BlocksFit span.start (16 + size) footer.blocks then
    let tail ← (readEnvelope limits input (span.start - 8)).mapError .eos
    let .eos := tail | throw (.eos (.malformed .trailingBytes))
    return ⟨span, footer, size, fits⟩
  else throw .blockLayout

/-- Check the selected block's continuation prefix and Message lengths before
decoding the body with the admitted fields and the existing per-batch budgets. -/
def readRecord (limits : MixedFlat.Limits) (input : KBytes) (fields : List Field)
    (block : FileBlock) : Except BlockError MixedFlat.Observed := do
  let ipc := limits.observation.ipc
  let frame ← (readEnvelope ipc input block.offset).mapError .envelope
  let .metadata size := frame | throw (.envelope (.malformed .schemaOrder))
  if 8 + size ≠ block.metadataLength then throw .metadataLength
  let record ← (readMetadata ipc limits.view.dataBuffers limits.totalDataBuffers fields
    (metadataSlice input block)).mapError .metadata
  if record.bodyLength ≠ block.bodyLength then throw .bodyLength
  let body ← (readBody ipc input (block.offset + block.metadataLength) block.bodyLength).mapError .body
  (readParsed limits fields record body).mapError .decode

/-- Return the observation of one indexed batch. An absent entry is `none`.
A present bad block reports its zero-based index, independently of other batches. -/
def Index.readAt {input : KBytes} (index : Index input) (limits : MixedFlat.Limits)
    (n : Nat) : Except Error (Option MixedFlat.Observed) :=
  index.footer.blocks[n]?.mapM fun block =>
    (readRecord limits input index.footer.fields block).mapError (.batch n)

end Silmaril.Formats.Arrow.MixedFlat.File
