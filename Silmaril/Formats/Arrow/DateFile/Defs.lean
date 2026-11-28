module

public import Silmaril.Formats.Arrow.FileReader.Defs
public import Silmaril.Formats.Arrow.DateStream.Defs

/-! # Checked indexed V5 IPC files with one flat DATE column -/

public section

namespace Silmaril.Formats.Arrow.DateFile

inductive BlockError where
  | envelope (cause : Arrow.Error)
  | metadataLength
  | metadata (cause : Arrow.Error)
  | expectedRecordBatch
  | bodyLength
  | body (cause : Arrow.Error)
  | values (cause : DateValues.Error)
  deriving DecidableEq, Repr

inductive Error where
  | footer (cause : Arrow.Error)
  | schema (cause : Arrow.Error)
  | schemaMismatch
  | bigEndian
  | fieldCount (actual : Nat)
  | fieldType (actual : DateBatch.FieldTypeError)
  | blockLayout
  | eos (cause : Arrow.Error)
  | batch (index : Nat) (cause : BlockError)
  deriving DecidableEq, Repr

/-- The retained field and block ranges refer to one immutable checked file. -/
structure Index (input : KBytes) where
  private mk ::
  span : FileReader.FooterSpan input
  field : DateStream.Field
  blocks : List FileBlock
  schemaSize : Nat
  fits : FileReader.BlocksFit span.start (16 + schemaSize) blocks

@[expose] def Index.schema {input : KBytes} (index : Index input) : SchemaReader.Schema :=
  ⟨.little, [⟨index.field.name, index.field.nullable, .date index.field.unit⟩]⟩

@[expose] def Index.schemaMetadata {input : KBytes} (index : Index input) : KBytes :=
  input.slice 16 index.schemaSize

@[expose] def metadataSlice (input : KBytes) (block : FileBlock) : KBytes :=
  input.slice (block.offset + 8) (block.metadataLength - 8)

@[expose] def bodySlice (input : KBytes) (block : FileBlock) : KBytes :=
  input.slice (block.offset + block.metadataLength) block.bodyLength

/-- Admit the footer and embedded Schema before inspecting any batch. -/
def readIndex (limits : Limits) (input : KBytes) : Except Error (Index input) := do
  let span ← (FileReader.readFooterSpan limits input).mapError .footer
  let footer ← (SchemaReader.readFileFooter limits (input.slice span.start span.length)).mapError .footer
  let envelope ← (readEnvelope limits input 8).mapError .schema
  let .metadata size := envelope | .error (.schema (.malformed .schemaOrder))
  if 16 + size + 8 > span.start then .error (.schema (.malformed .truncated)) else do
    let embedded ← (SchemaReader.readMessage limits (input.slice 16 size)).mapError .schema
    if embedded ≠ footer.schema then .error .schemaMismatch
    else if embedded.endianness ≠ .little then .error .bigEndian
    else do
      let [field] := embedded.fields | .error (.fieldCount embedded.fields.length)
      let unit ← (DateBatch.selectDateUnit field.type).mapError .fieldType
      if fits : FileReader.BlocksFit span.start (16 + size) footer.blocks then
        let tail ← (readEnvelope limits input (span.start - 8)).mapError .eos
        let .eos := tail | .error (.eos (.malformed .trailingBytes))
        return ⟨span, ⟨field.name, field.nullable, unit⟩, footer.blocks, size, fits⟩
      else .error .blockLayout

/-- Check the selected prefix and Message lengths before slicing its body. -/
@[expose] def readRecord (limits : Limits) (input : KBytes) (field : DateStream.Field)
    (block : FileBlock) : Except BlockError DateValues.Column := do
  let frame ← (readEnvelope limits input block.offset).mapError .envelope
  let .metadata size := frame | .error (.envelope (.malformed .schemaOrder))
  if 8 + size ≠ block.metadataLength then .error .metadataLength else do
    let message ← (Arrow.readMessage limits (metadataSlice input block)).mapError .metadata
    let .recordBatch batch := message.header | .error .expectedRecordBatch
    if message.bodyLength ≠ block.bodyLength then .error .bodyLength else do
      let body ← (readBody limits input (block.offset + block.metadataLength) block.bodyLength).mapError .body
      (DateValues.decodeBatch limits field.decoder field.descriptor batch body).mapError .values

/-- Look up one block. Absent indices and malformed selected batches are distinct. -/
@[expose] def Index.readAt {input : KBytes} (index : Index input) (limits : Limits)
    (n : Nat) : Except Error (Option DateValues.Column) :=
  index.blocks[n]?.mapM fun block => (readRecord limits input index.field block).mapError (.batch n)

/-- Correspondence of stream frames to footer blocks in order. Record metadata
must normalize to the same Message, and the body octets must agree. -/
inductive BatchesCorrespond (limits : Limits) (input stream : KBytes) :
    Nat → List FileBlock → Prop where
  | eos {offset} : readEnvelope limits stream offset = .ok .eos →
      BatchesCorrespond limits input stream offset []
  | batch {offset size block rest} :
      readEnvelope limits stream offset = .ok (.metadata size) →
      8 + size = block.metadataLength →
      Arrow.readMessage limits (stream.slice (offset + 8) size) =
        Arrow.readMessage limits (metadataSlice input block) →
      (stream.slice (offset + block.metadataLength) block.bodyLength).toList =
        (bodySlice input block).toList →
      BatchesCorrespond limits input stream (offset + block.metadataLength + block.bodyLength) rest →
      BatchesCorrespond limits input stream offset (block :: rest)

end Silmaril.Formats.Arrow.DateFile
