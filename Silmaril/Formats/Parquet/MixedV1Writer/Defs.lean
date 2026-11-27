module

public import Silmaril.Formats.Parquet.FlatInt32Writer.Defs
public import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Defs

/-! One flat Parquet row group with one PLAIN V1 page per field, in INT32
then opaque BYTE_ARRAY order. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.MixedV1Writer

open Int32ByteArrayGroup (Field Row)
open FlatInt32Writer.Compact (ColumnIndex)

structure Input where
  intName : String
  integers : PlainV1Writer.Input
  byteName : String
  octets : PlainByteArrayV1Writer.Input

structure Limits where
  maxFileBytes : Nat
  footer : Footer.Limits
  intPage : PlainV1Writer.Limits
  bytePage : PlainByteArrayV1Writer.Limits
  readback : Int32ByteArrayGroup.Limits := {}

inductive Error where
  | schemaOrCount
  | fileLimit
  | intBudget
  | byteBudget
  | intPage (cause : PlainV1Writer.Error)
  | bytePage (cause : PlainByteArrayV1Writer.Error)
  | compact (cause : FlatInt32Writer.Compact.Error)
  | layout
  | readback (cause : Int32ByteArrayGroup.Error)
  | values
  deriving DecidableEq, Repr

def Input.intField (input : Input) : Field :=
  ⟨input.intName, match input.integers with | .required _ => .required | .optional _ => .optional⟩

def Input.byteField (input : Input) : Field :=
  ⟨input.byteName, match input.octets with | .required _ => .required | .optional _ => .optional⟩

def Input.rowCount (input : Input) : Nat := input.integers.numValues

def Input.rows (input : Input) : List Row := input.integers.slots.zip input.octets.slots

def Input.Valid (input : Input) (limits : Limits) : Prop :=
  input.intName ≠ "" ∧ input.byteName ≠ "" ∧ input.intName ≠ input.byteName ∧
    input.rowCount = input.octets.numValues ∧ 3 ≤ limits.footer.compact.maxCollectionSize ∧
    input.intName.utf8ByteSize ≤ limits.footer.compact.maxBinaryBytes ∧
    input.byteName.utf8ByteSize ≤ limits.footer.compact.maxBinaryBytes

instance (input : Input) (limits : Limits) : Decidable (input.Valid limits) := by
  unfold Input.Valid
  infer_instance

structure Encoded where
  bytes : Bytes
  footer : Footer.Span
  intPage : PlainV1Writer.Encoded
  bytePage : PlainByteArrayV1Writer.Encoded

def Encoded.intSpan (output : Encoded) : Footer.Span := ⟨4, 4 + output.intPage.wire.length⟩

def Encoded.byteSpan (output : Encoded) : Footer.Span :=
  ⟨output.intSpan.stop, output.intSpan.stop + output.bytePage.wire.length⟩

def columnIndex (field : Field) (span : Footer.Span) : ColumnIndex :=
  ⟨field.name, decide (field.layout = .optional), span⟩

namespace Compact

open FlatInt32Writer.Compact (Write field integer octet root text listHeader leaf chunkFor)

/-- BYTE_ARRAY has physical type code 6 and carries no logical annotation. -/
def byteLeaf (column : ColumnIndex) : Write Unit := do
  field 1 5
  integer .i32 6
  field 2 5
  integer .i32 (if column.optional then 1 else 0)
  field 1 8
  text column.name
  octet 0

structure GroupIndex where
  rows : Nat
  ints : ColumnIndex
  octets : ColumnIndex

def writeGroup (group : GroupIndex) : Write Unit := do
  field 1 9
  listHeader 12 2
  chunkFor 1 group.rows group.ints
  chunkFor 6 group.rows group.octets
  field 1 6
  integer .i64 (group.ints.size + group.octets.size)
  field 1 6
  integer .i64 group.rows
  octet 0

def footerGroups (ints octets : ColumnIndex) (groups : List GroupIndex) : Write Unit := do
  field 1 5
  integer .i32 1
  field 1 9
  listHeader 12 3
  root 2
  leaf ints
  byteLeaf octets
  field 1 6
  integer .i64 (groups.map GroupIndex.rows).sum
  field 1 9
  listHeader 12 groups.length
  for group in groups do writeGroup group
  octet 0

def footer (rows : Nat) (ints octets : ColumnIndex) : Write Unit :=
  footerGroups ints octets [⟨rows, ints, octets⟩]

def encodeGroups (limit : Nat) (ints octets : ColumnIndex) (groups : List GroupIndex) :
    Except FlatInt32Writer.Compact.Error Bytes :=
  ((footerGroups ints octets groups).run ⟨limit, .empty⟩).map (·.2.bytes)

def encode (limit rows : Nat) (ints octets : ColumnIndex) : Except FlatInt32Writer.Compact.Error Bytes :=
  encodeGroups limit ints octets [⟨rows, ints, octets⟩]

end Compact

def byteSchema (column : ColumnIndex) : Footer.SchemaElement :=
  { column.schema with physicalType := some .byteArray }

def byteChunk (column : ColumnIndex) (rows : Nat) : Footer.ColumnChunk :=
  let chunk := column.metadata rows
  { chunk with metadata := { chunk.metadata with physicalType := .byteArray } }

def metadata (input : Input) (output : Encoded) : Footer.Metadata :=
  let ints := columnIndex input.intField output.intSpan
  let octets := columnIndex input.byteField output.byteSpan
  ⟨1, [FlatInt32Writer.Compact.schemaRoot 2, ints.schema, byteSchema octets], input.rowCount,
    [⟨[ints.metadata input.rowCount, byteChunk octets input.rowCount],
      ints.size + octets.size, input.rowCount, none, none⟩], none⟩

def frame (span : Footer.Span) (page : PlainV1Writer.Encoded) : Page.Frame :=
  let split := span.start + page.headerBytes.length
  ⟨page.header, ⟨span.start, split⟩, ⟨split, span.stop⟩⟩

def pageLimits (limits : PlainV1Writer.Limits) : Page.Limits :=
  ⟨limits.headerBytes, 1, limits.header⟩

def Encoded.Checked (output : Encoded) (limits : Limits) (input : Input) : Prop :=
  let ints := columnIndex input.intField output.intSpan
  let octets := columnIndex input.byteField output.byteSpan
  let intFrame := frame output.intSpan output.intPage
  let byteFrame := frame output.byteSpan output.bytePage
  output.bytes.length ≤ limits.maxFileBytes ∧ output.bytes.length < 2^63 ∧
    output.footer.start = output.byteSpan.stop ∧
    Footer.readFooter limits.footer output.bytes = .ok (output.footer, metadata input output) ∧
    Page.columnSpan output.footer.start (ints.metadata input.rowCount).metadata = some output.intSpan ∧
    Page.columnSpan output.footer.start (byteChunk octets input.rowCount).metadata = some output.byteSpan ∧
    Page.readChunk (pageLimits limits.intPage) output.bytes output.intSpan = .ok [intFrame] ∧
    Page.readChunk (pageLimits limits.bytePage.page) output.bytes output.byteSpan = .ok [byteFrame] ∧
    Footer.fileBytes output.bytes intFrame.payload.start intFrame.payload.stop = output.intPage.body ∧
    Footer.fileBytes output.bytes byteFrame.payload.start byteFrame.payload.stop = output.bytePage.body

instance (output : Encoded) (limits : Limits) (input : Input) : Decidable (output.Checked limits input) := by
  unfold Encoded.Checked
  infer_instance

def measuredBytePage (limits : PlainByteArrayV1Writer.Limits) (input : PlainByteArrayV1Writer.Input) :
    Except Error Nat := do
  if ¬ input.Fits limits then throw .byteBudget
  let some header := PlainV1Writer.encodeHeader input.numValues input.bodySize | throw .byteBudget
  if limits.page.headerBytes < header.length then throw .byteBudget
  return header.length + input.bodySize

/-- Check the combined data extent before encoding either page. The remaining
file budget bounds Compact serialization before the final concatenation. -/
def assemble (limits : Limits) (input : Input) : Except Error Encoded := do
  let intSize ← (FlatInt32Writer.measuredPage limits.intPage input.integers).mapError (fun _ => .intBudget)
  let byteSize ← measuredBytePage limits.bytePage input.octets
  let fileLimit := min limits.maxFileBytes (2 ^ 63 - 1)
  if fileLimit < 4 + intSize + byteSize + 8 then throw .fileLimit
  let intPage ← (PlainV1Writer.emit limits.intPage input.integers).mapError .intPage
  let bytePage ← (PlainByteArrayV1Writer.emit limits.bytePage input.octets).mapError .bytePage
  let pages : Encoded := ⟨.empty, ⟨0, 0⟩, intPage, bytePage⟩
  let start := pages.byteSpan.stop
  if fileLimit < start + 8 then throw .fileLimit
  let footerLimit := min (min limits.footer.maxFooterBytes (2 ^ 32 - 1)) (fileLimit - start - 8)
  let footer ← (Compact.encode footerLimit input.rowCount (columnIndex input.intField pages.intSpan)
    (columnIndex input.byteField pages.byteSpan)).mapError .compact
  let bytes := ((((Footer.magic.append intPage.wire).append bytePage.wire).append footer).append
    (Bytes.ofList (KBytes.unpack 4 footer.length))).append Footer.magic
  return { pages with bytes, footer := ⟨start, start + footer.length⟩ }

def readback (limits : Int32ByteArrayGroup.Limits) (input : Input) (output : Encoded) :
    Except Int32ByteArrayGroup.Error (List Row) :=
  (Int32ByteArrayGroup.openFile limits output.bytes input.intField input.byteField).bind
    (fun checked => checked.readGroup limits 0)

/-- Return only a complete file whose schema, offsets and page bodies check
and whose existing mixed reader recovers the two original columns in order. -/
def emit (limits : Limits) (input : Input) : Except Error Encoded :=
  if input.Valid limits then do
    let output ← assemble limits input
    if output.Checked limits input then
      let rows ← (readback limits.readback input output).mapError .readback
      if rows = input.rows then return output else throw .values
    else throw .layout
  else .error .schemaOrCount

end Silmaril.Formats.Parquet.MixedV1Writer
