module

public import Silmaril.Formats.Parquet.Footer.Defs
public import Silmaril.Formats.Parquet.Page.Defs
public import Silmaril.Formats.Parquet.FlatPage.Defs

/-! Checked assembly for flat PLAIN INT32 columns. A supplied scalar page
reader owns payload semantics. This layer binds it to the file metadata and
checks the returned slots before assembling rows. -/

public section

namespace Silmaril.Formats.Parquet.FlatScan

structure Field where
  name : String
  layout : FlatPage.Layout
  deriving DecidableEq, Repr

/-- The callback receives one checked data-page header and its exact on-disk
payload, for an uncompressed flat PLAIN INT32 column. It returns row slots in
page order. The scan checks count and nullability independently. -/
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
  | pageByteLimit
  | pageSize
  | pageCount
  | pageNulls
  | decoder (error : ε)
  deriving DecidableEq, Repr

structure ColumnValues (rowCount : Nat) where
  cells : Array (Option Int32)
  sized : cells.size = rowCount

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

/-- The scanner rejects every non-data page. CRC-bearing pages require a
checksum policy supplied by a later profile. -/
private def checkPage {ε : Type} (limits : Limits) (field : Field) (header : Page.Header) :
    Except (Error ε) (Nat × Option Nat) := do
  if header.crc.isSome then throw .crcUnsupported
  if header.compressedSize > limits.maxPageBytes || header.uncompressedSize > limits.maxPageBytes then
    throw .pageByteLimit
  if header.compressedSize != header.uncompressedSize then throw .pageSize
  match header.kind with
  | .dataV1 info =>
    if info.encoding != 0 || info.definitionLevelEncoding != 3 || info.repetitionLevelEncoding != 3 then
      throw .unsupportedPageEncoding
    pure (info.numValues, none)
  | .dataV2 info =>
    if info.encoding != 0 then throw .unsupportedPageEncoding
    if info.numValues != info.numRows then throw .pageCount
    if info.repetitionBytes != 0 ||
        (field.layout == .required && (info.numNulls != 0 || info.definitionBytes != 0)) then
      throw .pageNulls
    pure (info.numValues, some info.numNulls)
  | .dictionary _ | .skipped _ => throw .unsupportedKind

/-- Validate one column against its schema field and row-group count, then
consume the checked page frames in their wire order. -/
def scanColumn {ε : Type} (limits : Limits) (decoder : DecodePage ε) (source : Bytes)
    (footerStart : Nat) (field : Field) (rowCount : Nat) (column : Footer.ColumnChunk) :
    Except (Error ε) (ColumnValues rowCount) := do
  if rowCount > limits.maxRows then throw .rowLimit
  let metadata := column.metadata
  if metadata.pathInSchema != [field.name] then
    throw (.columnPath field.name metadata.pathInSchema)
  if metadata.physicalType != .int32 then throw (.columnType field.name)
  if metadata.numValues != (rowCount : Int) then throw (.columnCount field.name)
  if metadata.codec != 0 then throw (.columnCodec field.name)
  if !metadata.encodings.all (fun id => id == 0 || id == 3) ||
      (rowCount != 0 && !metadata.encodings.contains 0) then throw (.columnEncoding field.name)
  if metadata.dictionaryPageOffset.isSome || metadata.indexPageOffset.isSome then throw .unsupportedKind
  let some span := Page.columnSpan footerStart metadata | throw (.columnBounds field.name)
  let frames ← (Page.readChunk limits.page source span).mapError .page
  let mut remaining := rowCount
  let mut cells := #[]
  for frame in frames do
    let (count, nulls) ← checkPage limits field frame.value
    if remaining < count then throw .pageCount
    let payload := Footer.fileBytes source frame.payload.start frame.payload.stop
    let values ← (decoder field frame.value payload).mapError .decoder
    if values.length != count then throw .pageCount
    if (field.layout == .required && values.any Option.isNone) ||
        nulls.any (fun n => values.countP Option.isNone != n) then throw .pageNulls
    remaining := remaining - count
    cells := cells ++ values.toArray
  if remaining != 0 then throw .pageCount
  if sized : cells.size = rowCount then
    pure ⟨cells, sized⟩
  else throw .pageCount

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
