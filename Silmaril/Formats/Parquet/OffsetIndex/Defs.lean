module

public import Silmaril.Formats.Parquet.Snapshot.Defs
public import Silmaril.Formats.Parquet.Page.Defs

/-! Checked OffsetIndex metadata for flat INT32 columns in a local plaintext snapshot. -/

public section

namespace Silmaril.Formats.Parquet.OffsetIndex

open ThriftCompact
open Traversal (Reader Field)

structure Limits where
  snapshot : Snapshot.Limits := {}
  page : Page.Limits := {}
  compact : Traversal.Limits := {}
  varintMode : VarintMode := .canonical
  maxFileBytes : Nat := 256 * 1024 * 1024
  maxChunkBytes : Nat := 128 * 1024 * 1024
  maxIndexBytes : Nat := 1024 * 1024
  maxLocations : Nat := 65536
  maxRows : Nat := 4 * 1024 * 1024

inductive Error where
  | fileByteLimit
  | snapshot (reason : Snapshot.Error Unit)
  | groupIndex (index : Nat)
  | columnIndex (index : Nat)
  | unsupportedColumn
  | unsupportedChunk
  | columnCount
  | rowLimit
  | partialReference
  | indexByteLimit
  | indexBounds
  | indexOverlapsChunk
  | chunkBounds
  | chunkByteLimit
  | compact (reason : Traversal.Error)
  | missingField (id : Int)
  | duplicateField (id : Int)
  | fieldType (id : Int) (actual : FieldType)
  | fieldExtent (id : Int)
  | invalidLocationField (id : Int)
  | byteArraySizesUnsupported
  | trailingIndexBytes
  | page (reason : Page.Error)
  | locationCount
  | unsupportedPage (index : Nat)
  | invalidPageRows (index : Nat)
  | pageOffset (index indexed framed : Nat)
  | pageSize (index indexed framed : Nat)
  | firstRow (index indexed expected : Nat)
  | rowCount (expected actual : Nat)
  deriving DecidableEq, Repr

structure Location where
  offset : Nat
  compressedSize : Nat
  firstRow : Nat
  deriving DecidableEq, Repr

structure Entry where
  location : Location
  frame : Page.Frame
  rowCount : Nat
  deriving DecidableEq, Repr

def Entry.rowStop (entry : Entry) : Nat :=
  entry.location.firstRow + entry.rowCount

structure Index where
  span : Footer.Span
  pages : List Entry
  deriving DecidableEq, Repr

private def requireField (fields : List Field) (id : Int) (type : ValueType) : Except Error Field :=
  match fields.filter (·.id == id) with
  | [] => .error (.missingField id)
  | [field] =>
    if field.type = .payload type then .ok field else .error (.fieldType id field.type)
  | _ => .error (.duplicateField id)

private def locationField (reader : Reader) (fields : List Field) (id : Int)
    (width : Width) (type : ValueType) (minimum : Int) : Except Error Nat := do
  let field ← requireField fields id type
  let (value, next) ← (readSigned width reader.mode reader.source field.start).mapError
    (fun error => .compact (.compact error))
  if next ≠ field.stop then return ← throw (.fieldExtent id)
  if value < minimum then return ← throw (.invalidLocationField id)
  pure value.toNat

private def readLocation (reader : Reader) (start : Nat) : Except Error (Location × Nat) := do
  let (fields, next) ← (Traversal.readStruct reader start).mapError .compact
  let offset ← locationField reader fields 1 .i64 .i64 0
  let compressedSize ← locationField reader fields 2 .i32 .i32 1
  let firstRow ← locationField reader fields 3 .i64 .i64 0
  pure (⟨offset, compressedSize, firstRow⟩, next)

/-- Read the Compact struct from a bounded slice. Apply the location cap to
the structural pass as well as the typed list reader. -/
def readPrefix (limits : Limits) (source : Bytes) : Except Error (List Location × Nat) := do
  if source.length > limits.maxIndexBytes then return ← throw .indexByteLimit
  let cap := min limits.compact.maxCollectionSize limits.maxLocations
  let compact := { limits.compact with maxCollectionSize := cap }
  let reader : Reader := ⟨source, compact, limits.varintMode⟩
  let (fields, next) ← (Traversal.readStruct reader 0).mapError .compact
  if fields.any (·.id == 2) then return ← throw .byteArraySizesUnsupported
  let field ← requireField fields 1 .list
  let (locations, stop) ← Traversal.readList reader Error.compact .struct (readLocation reader) field.start
  if stop ≠ field.stop then return ← throw (.fieldExtent 1)
  pure (locations, next)

/-- Consume the entire advertised slice, including the final Compact STOP. -/
def readExact (limits : Limits) (source : Bytes) : Except Error (List Location) := do
  let (locations, next) ← readPrefix limits source
  if next ≠ source.length then return ← throw .trailingIndexBytes
  pure locations

/-- The first profile requires a flat footer schema. Other flat siblings may
have different physical types. Select the INT32 leaf by the same ordinal as
the column chunk, and check its one-component schema path. -/
def select (limits : Limits) (snapshot : Snapshot.Checked) (groupIndex columnIndex : Nat) :
    Except Error (Footer.RowGroup × Footer.ColumnChunk) := do
  let some group := snapshot.groupAt groupIndex | throw (.groupIndex groupIndex)
  let some column := group.columns[columnIndex]? | throw (.columnIndex columnIndex)
  let root :: leaves := snapshot.metadata.schema | throw .unsupportedColumn
  let some leaf := leaves[columnIndex]? | throw .unsupportedColumn
  let metadata := column.metadata
  if ¬ (root.numChildren = some (Int.ofNat leaves.length) ∧
      leaf.physicalType = some .int32 ∧ leaf.typeLength = none ∧
      leaf.numChildren.getD 0 = 0 ∧ (leaf.repetition = some .required ∨ leaf.repetition = some .optional) ∧
      metadata.physicalType = .int32 ∧ metadata.pathInSchema = [leaf.name]) then
    return ← throw .unsupportedColumn
  if ¬ (metadata.dictionaryPageOffset = none ∧ metadata.indexPageOffset = none) then
    return ← throw .unsupportedChunk
  if ¬ (0 ≤ group.numRows ∧ metadata.numValues = group.numRows) then
    return ← throw .columnCount
  if group.numRows.toNat > limits.maxRows then return ← throw .rowLimit
  pure (group, column)

structure Selection (limits : Limits) (snapshot : Snapshot.Checked) (groupIndex columnIndex : Nat)
    (group : Footer.RowGroup) (column : Footer.ColumnChunk) : Prop where
  groupAt : snapshot.groupAt groupIndex = some group
  columnAt : group.columns[columnIndex]? = some column
  flatInt32 : ∃ (root : Footer.SchemaElement) (leaves : List Footer.SchemaElement)
      (leaf : Footer.SchemaElement),
    snapshot.metadata.schema = root :: leaves ∧ root.numChildren = some (Int.ofNat leaves.length) ∧
    leaves[columnIndex]? = some leaf ∧ leaf.physicalType = some .int32 ∧ leaf.typeLength = none ∧
    leaf.numChildren.getD 0 = 0 ∧ (leaf.repetition = some .required ∨ leaf.repetition = some .optional) ∧
    column.metadata.physicalType = .int32 ∧ column.metadata.pathInSchema = [leaf.name]
  dataChunk : column.metadata.dictionaryPageOffset = none ∧ column.metadata.indexPageOffset = none
  columnCount : column.metadata.numValues = group.numRows
  rowBounds : 0 ≤ group.numRows ∧ group.numRows.toNat ≤ limits.maxRows

/-- Header-declared row counts in a schema with maximum repetition level zero. -/
inductive FlatRows : Page.Kind → Nat → Prop where
  | v1 (info : Page.DataV1) : FlatRows (.dataV1 info) info.numValues
  | v2 (info : Page.DataV2) (counts : info.numValues = info.numRows) (flat : info.repetitionBytes = 0) :
      FlatRows (.dataV2 info) info.numRows

private def pageRows (index : Nat) (kind : Page.Kind) : Except Error Nat :=
  match kind with
  | .dataV1 info => .ok info.numValues
  | .dataV2 info =>
    if info.numValues = info.numRows ∧ info.repetitionBytes = 0 then .ok info.numRows
    else .error (.invalidPageRows index)
  | _ => .error (.unsupportedPage index)

/-- Pair the wire locations with framed pages in order. Rows use half-open
intervals within the selected row group and each indexed page contributes rows. -/
inductive Partition : Nat → Nat → List Entry → Prop where
  | nil (row : Nat) : Partition row row []
  | cons {start stop : Nat} {entry : Entry} {rest : List Entry}
      (first : entry.location.firstRow = start) (positive : 0 < entry.rowCount)
      (rows : FlatRows entry.frame.value.kind entry.rowCount)
      (offset : entry.location.offset = entry.frame.header.start)
      (size : entry.location.compressedSize = entry.frame.payload.stop - entry.frame.header.start)
      (next : Partition entry.rowStop stop rest) :
      Partition start stop (entry :: rest)

def matchPages (groupRows : Nat) (locations : List Location) (frames : List Page.Frame) :
    Except Error (List Entry) :=
  go 0 0 [] locations frames
where
  go (index first : Nat) (reversed : List Entry) : List Location → List Page.Frame → Except Error (List Entry)
    | [], [] => if first = groupRows then .ok reversed.reverse else .error (.rowCount groupRows first)
    | location :: locations, frame :: frames => do
      if location.offset ≠ frame.header.start then
        return ← throw (.pageOffset index location.offset frame.header.start)
      let framedSize := frame.payload.stop - frame.header.start
      if location.compressedSize ≠ framedSize then
        return ← throw (.pageSize index location.compressedSize framedSize)
      if location.firstRow ≠ first then return ← throw (.firstRow index location.firstRow first)
      let rows ← pageRows index frame.value.kind
      if rows = 0 then return ← throw (.invalidPageRows index)
      let stop := first + rows
      if groupRows < stop then return ← throw (.rowCount groupRows stop)
      go (index + 1) stop (⟨location, frame, rows⟩ :: reversed) locations frames
    | _, _ => .error .locationCount

/-- Read the referenced index and frame the selected chunk from the same
snapshot. The supported index placement follows the selected chunk. -/
private def validateAt (limits : Limits) (snapshot : Snapshot.Checked) (group : Footer.RowGroup)
    (column : Footer.ColumnChunk) (offset size : Int) : Except Error Index := do
  if (limits.maxIndexBytes : Int) < size then return ← throw .indexByteLimit
  let some span := Footer.checkDataSpan snapshot.footer.start offset size | throw .indexBounds
  let some chunk := Page.columnSpan snapshot.footer.start column.metadata | throw .chunkBounds
  if span.start < chunk.stop then return ← throw .indexOverlapsChunk
  if chunk.stop - chunk.start > limits.maxChunkBytes then return ← throw .chunkByteLimit
  if snapshot.bytes.length < span.stop then return ← throw .indexBounds
  let bytes := Footer.fileBytes snapshot.bytes span.start span.stop
  let locations ← readExact limits bytes
  let frames ← (Page.readChunk limits.page snapshot.bytes chunk).mapError .page
  pure ⟨span, ← matchPages group.numRows.toNat locations frames⟩

structure Evidence (limits : Limits) (snapshot : Snapshot.Checked) (groupIndex columnIndex : Nat)
    (result : Index) (group : Footer.RowGroup) (column : Footer.ColumnChunk)
    (chunk : Footer.Span) (bytes : Bytes) : Prop where
  selected : Selection limits snapshot groupIndex columnIndex group column
  offset : column.offsetIndexOffset = some (Int.ofNat result.span.start)
  size : column.offsetIndexLength = some (Int.ofNat (result.span.stop - result.span.start))
  bounds : 4 ≤ result.span.start ∧ result.span.start < result.span.stop ∧
    result.span.stop ≤ snapshot.footer.start
  separate : chunk.stop ≤ result.span.start
  caps : bytes.length ≤ limits.maxIndexBytes ∧ chunk.stop - chunk.start ≤ limits.maxChunkBytes
  slice : snapshot.bytes.slice? result.span.start (some result.span.stop) = some bytes
  index : readPrefix limits bytes = .ok (result.pages.map Entry.location, bytes.length)
  columnSpan : Page.columnSpan snapshot.footer.start column.metadata = some chunk
  frames : Page.readChunk limits.page snapshot.bytes chunk = .ok (result.pages.map Entry.frame)
  rows : Partition 0 group.numRows.toNat result.pages

/-- A complete but invalid reference produces an error. An absent pair returns
`none` after selecting the supported column, without scanning its pages. -/
def validate (limits : Limits) (snapshot : Snapshot.Checked) (groupIndex columnIndex : Nat) :
    Except Error (Option Index) := do
  let (group, column) ← select limits snapshot groupIndex columnIndex
  match column.offsetIndexOffset, column.offsetIndexLength with
  | none, none => pure none
  | some offset, some size => some <$> validateAt limits snapshot group column offset size
  | _, _ => throw .partialReference

/-- Open the immutable bytes with the common plaintext footer validation,
then check the selected index. Footer failures include partial references. -/
def readFile (limits : Limits) (source : Bytes) (groupIndex columnIndex : Nat) :
    Except Error (Option Index) := do
  if source.length > limits.maxFileBytes then return ← throw .fileByteLimit
  let snapshot ← (Snapshot.check limits.snapshot source).mapError Error.snapshot
  validate limits snapshot groupIndex columnIndex

end Silmaril.Formats.Parquet.OffsetIndex
