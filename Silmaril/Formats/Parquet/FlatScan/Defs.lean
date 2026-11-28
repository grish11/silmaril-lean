module

public import Silmaril.Formats.Parquet.Footer.Defs
public import Silmaril.Formats.Parquet.Page.Checksum.Scan.Defs
public import Silmaril.Formats.Parquet.FlatPage.Defs

/-! Checked assembly for flat INT32 columns. A supplied scalar page reader
owns payload semantics. This layer binds it to the file metadata and checks
the returned slots before assembling rows. -/

public section

namespace Silmaril.Formats.Parquet.FlatScan

structure Field where
  name : String
  layout : FlatPage.Layout
  deriving DecidableEq, Repr

/-- The callback receives one checked data-page header and its exact on-disk
payload, for a flat INT32 column. It returns row slots in page order.
The scan checks count and nullability independently. -/
abbrev DecodePage (ε : Type) :=
  Field → Page.Header → Bytes → Except ε (List (Option Int32))

structure Limits where
  footer : Footer.Limits := {}
  page : Page.Limits := {}
  maxRows : Nat := 1024 * 1024
  maxColumns : Nat := 256
  maxCells : Nat := 16 * 1024 * 1024
  maxPageBytes : Nat := 16 * 1024 * 1024

inductive Error (ε : Type) where
  | footer (error : Footer.Error)
  | version
  | schema
  | duplicateField
  | columnLimit
  | groupIndex
  | rowCount
  | rowLimit
  | cellLimit
  | columnArity
  | columnPath (expected : String) (actual : List String)
  | columnType (field : String)
  | columnCount (field : String)
  | columnEncoding (field : String)
  | columnCodec (field : String)
  | columnBounds (field : String)
  | page (error : Page.Error)
  | unsupportedKind
  | unsupportedPageEncoding
  | crcUnsupported
  | checksum (reason : Page.Checksum.FrameFailure)
  | pageByteLimit
  | pageSize
  | pageCount
  | pageNulls
  | decoder (error : ε)
  deriving DecidableEq, Repr

structure ColumnValues (rowCount : Nat) where
  cells : Array (Option Int32)
  sized : cells.size = rowCount

/-- Page failures carry their ordinal in the chunk and absolute header offset. -/
inductive ColumnFailure (ε : Type) where
  | column (reason : Error ε)
  | atPage (index headerOffset : Nat) (reason : Error ε)
  deriving DecidableEq, Repr

private def ColumnFailure.reason {ε : Type} : ColumnFailure ε → Error ε
  | .column reason | .atPage _ _ reason => reason

/-- Columns are in schema order. The row count is explicit even for zero columns. -/
structure Batch where
  rowCount : Nat
  columns : List (Field × ColumnValues rowCount)

def Batch.rows (batch : Batch) : List (List (Option Int32)) :=
  let reversed := batch.columns.foldl (fun rows (_, column) =>
    List.zipWith (fun row cell => cell :: row) rows column.cells.toList)
    (List.replicate batch.rowCount [])
  reversed.map List.reverse

private def flatField {ε : Type} (node : Footer.SchemaElement) : Except (Error ε) Field := do
  if node.physicalType != some .int32 || node.numChildren.getD 0 != 0 then throw .schema
  match node.repetition with
  | some .required => pure (⟨node.name, .required⟩ : Field)
  | some .optional => pure ⟨node.name, .optional⟩
  | _ => throw .schema

/-- Validate the footer schema for this profile and return the leaves in wire
order. An opener can check the ordered names and layouts without reading any
row groups. `limits.maxColumns` bounds the schema width. -/
def flatSchema {ε : Type} (limits : Limits) (schema : List Footer.SchemaElement) :
    Except (Error ε) (List Field) := do
  let root :: children := schema | throw .schema
  if children.length > limits.maxColumns then throw .columnLimit
  if root.physicalType.isSome || root.typeLength.isSome ||
      (root.repetition != none && root.repetition != some .required) ||
      root.numChildren != some (Int.ofNat children.length) then throw .schema
  let fields ← children.mapM flatField
  if !(fields.map (·.name)).Nodup then throw .duplicateField
  pure fields

private def admitsValueEncoding (allowDelta : Bool) (encoding : Int) : Bool :=
  encoding == 0 || (allowDelta && encoding == 5)

/-- The scanner rejects every non-data page. The opt-in delta profile also
requires the page's actual scalar encoding to occur in column metadata. -/
private def checkPage {ε : Type} (limits : Limits) (field : Field) (header : Page.Header)
    (rejectCRC allowDelta : Bool) (advertised : List Int) (requiredCodec : Int) :
    Except (Error ε) (Nat × Option Nat) := do
  if rejectCRC && header.crc.isSome then throw .crcUnsupported
  if header.compressedSize > limits.maxPageBytes || header.uncompressedSize > limits.maxPageBytes then
    throw .pageByteLimit
  if requiredCodec == 0 && header.compressedSize != header.uncompressedSize then throw .pageSize
  let admits := fun encoding =>
    admitsValueEncoding allowDelta encoding && (!allowDelta || advertised.contains encoding)
  match header.kind with
  | .dataV1 info =>
    if !admits info.encoding || info.definitionLevelEncoding != 3 || info.repetitionLevelEncoding != 3 then
      throw .unsupportedPageEncoding
    pure (info.numValues, none)
  | .dataV2 info =>
    if !admits info.encoding then throw .unsupportedPageEncoding
    if info.numValues != info.numRows then throw .pageCount
    if info.repetitionBytes != 0 ||
        (field.layout == .required && (info.numNulls != 0 || info.definitionBytes != 0)) then
      throw .pageNulls
    pure (info.numValues, some info.numNulls)
  | .dictionary _ | .skipped _ => throw .unsupportedKind

private def frameColumn {ε : Type} (checksumLimit : Option Nat) (allowDelta : Bool) (requiredCodec : Int)
    (limits : Limits) (source : Bytes) (footerStart : Nat) (field : Field) (rowCount : Nat)
    (column : Footer.ColumnChunk) : Except (Error ε) (List Page.Frame) :=
  let metadata := column.metadata
  if rowCount > limits.maxRows then .error .rowLimit
  else if metadata.pathInSchema != [field.name] then .error (.columnPath field.name metadata.pathInSchema)
  else if metadata.physicalType != .int32 then .error (.columnType field.name)
  else if metadata.numValues != (rowCount : Int) then .error (.columnCount field.name)
  else if metadata.codec != requiredCodec then .error (.columnCodec field.name)
  else if !metadata.encodings.all (fun id => admitsValueEncoding allowDelta id || id == 3) ||
      (rowCount != 0 && !metadata.encodings.any (admitsValueEncoding allowDelta)) then
    .error (.columnEncoding field.name)
  else if metadata.dictionaryPageOffset.isSome || metadata.indexPageOffset.isSome then .error .unsupportedKind
  else
    match Page.columnSpan footerStart metadata with
    | none => .error (.columnBounds field.name)
    | some span =>
      match checksumLimit with
      | none => (Page.readChunk limits.page source span).mapError .page
      | some cap =>
        (Page.Checksum.readChunkWithCRC limits.page (fun _ => min cap limits.maxPageBytes) source span).mapError
          (fun | .page reason => .page reason | .checksum reason => .checksum reason)

private def readFrame {ε : Type} (limits : Limits) (decoder : DecodePage ε) (source : Bytes)
    (field : Field) (frame : Page.Frame) (remaining : Nat) (rejectCRC allowDelta : Bool)
    (advertised : List Int) (requiredCodec : Int) : Except (Error ε) (Nat × List (Option Int32)) := do
  let (count, nulls) ← checkPage limits field frame.value rejectCRC allowDelta advertised requiredCodec
  if remaining < count then throw .pageCount
  let payload := Footer.fileBytes source frame.payload.start frame.payload.stop
  let values ← (decoder field frame.value payload).mapError .decoder
  if values.length != count then throw .pageCount
  if (field.layout == .required && values.any Option.isNone) ||
      nulls.any (fun n => values.countP Option.isNone != n) then throw .pageNulls
  pure (count, values)

private def scanColumnCore {ε : Type} (checksumLimit : Option Nat) (allowDelta : Bool) (requiredCodec : Int)
    (limits : Limits) (decoder : DecodePage ε) (source : Bytes) (footerStart : Nat) (field : Field)
    (rowCount : Nat) (column : Footer.ColumnChunk) : Except (ColumnFailure ε) (ColumnValues rowCount) := do
  let frames ← (frameColumn checksumLimit allowDelta requiredCodec limits source footerStart field
    rowCount column).mapError .column
  let mut remaining := rowCount
  let mut cells := #[]
  for (frame, index) in frames.zipIdx do
    let (count, values) ← (readFrame limits decoder source field frame remaining
      checksumLimit.isNone allowDelta column.metadata.encodings requiredCodec).mapError (.atPage index frame.header.start)
    remaining := remaining - count
    cells := cells ++ values.toArray
  if remaining != 0 then throw (.column .pageCount)
  if sized : cells.size = rowCount then
    pure ⟨cells, sized⟩
  else throw (.column .pageCount)

/-- Validate and scan one PLAIN column in wire order. CRC-bearing pages are rejected. -/
def scanColumn {ε : Type} (limits : Limits) (decoder : DecodePage ε) (source : Bytes)
    (footerStart : Nat) (field : Field) (rowCount : Nat) (column : Footer.ColumnChunk) :
    Except (Error ε) (ColumnValues rowCount) :=
  (scanColumnCore none false 0 limits decoder source footerStart field rowCount column).mapError ColumnFailure.reason

/-- Verify the original framed pages before decoding any of their PLAIN bodies. -/
def scanColumnWithCRC {ε : Type} (checksumLimit : Nat) (limits : Limits) (decoder : DecodePage ε)
    (source : Bytes) (footerStart : Nat) (field : Field) (rowCount : Nat) (column : Footer.ColumnChunk) :
    Except (Error ε) (ColumnValues rowCount) :=
  (scanColumnCore (some checksumLimit) false 0 limits decoder source footerStart field rowCount column).mapError
    ColumnFailure.reason

/-- Scan one uncompressed flat INT32 column admitting PLAIN and DELTA_BINARY_PACKED
data pages. The callback consumes the original body. This profile rejects page CRCs. -/
def scanColumnPlainDelta {ε : Type} (limits : Limits) (decoder : DecodePage ε)
    (source : Bytes) (footerStart : Nat) (field : Field) (rowCount : Nat) (column : Footer.ColumnChunk) :
    Except (ColumnFailure ε) (ColumnValues rowCount) :=
  scanColumnCore none true 0 limits decoder source footerStart field rowCount column

/-- Scan a flat PLAIN INT32 column whose checked footer codec is Snappy (1).
The callback receives each exact on-disk body. CRC-bearing pages are rejected. -/
def scanColumnSnappy {ε : Type} (limits : Limits) (decoder : DecodePage ε)
    (source : Bytes) (footerStart : Nat) (field : Field) (rowCount : Nat) (column : Footer.ColumnChunk) :
    Except (ColumnFailure ε) (ColumnValues rowCount) :=
  scanColumnCore none false 1 limits decoder source footerStart field rowCount column

private def scanColumns {ε : Type} (limits : Limits) (decoder : DecodePage ε) (source : Bytes)
    (footerStart rowCount : Nat) (pairs : List (Field × Footer.ColumnChunk)) :
    Except (Error ε) (List (Field × ColumnValues rowCount)) :=
  pairs.mapM fun (field, column) => do
    let values ← scanColumn limits decoder source footerStart field rowCount column
    pure (field, values)

/-- Check a row group against the flat schema and the footer position. Schema,
metadata and output columns share the same order. Zero columns retain the
advertised row count, subject to the row budget. -/
def scanRowGroup {ε : Type} (limits : Limits) (decoder : DecodePage ε) (source : Bytes)
    (footerStart : Nat) (schema : List Footer.SchemaElement) (group : Footer.RowGroup) :
    Except (Error ε) Batch := do
  let fields ← flatSchema limits schema
  if group.numRows < 0 then throw .rowCount
  let rowCount := group.numRows.toNat
  if rowCount > limits.maxRows then throw .rowLimit
  if rowCount * fields.length > limits.maxCells then throw .cellLimit
  if fields.length != group.columns.length then throw .columnArity
  let columns ← scanColumns limits decoder source footerStart rowCount (fields.zip group.columns)
  pure ⟨rowCount, columns⟩

/-- Open the plaintext footer and scan one group from the same immutable file. -/
def scanFileRowGroup {ε : Type} (limits : Limits) (decoder : DecodePage ε) (source : Bytes)
    (groupIndex : Nat) : Except (Error ε) Batch := do
  let (span, metadata) ← (Footer.readFooter limits.footer source).mapError .footer
  if metadata.version != 1 && metadata.version != 2 then throw .version
  if !(metadata.rowGroups.all fun group => 0 ≤ group.numRows) ||
      (metadata.rowGroups.map (·.numRows)).sum != metadata.numRows then throw .rowCount
  let some group := metadata.rowGroups[groupIndex]? | throw .groupIndex
  scanRowGroup limits decoder source span.start metadata.schema group

end Silmaril.Formats.Parquet.FlatScan
