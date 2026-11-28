module

public import Silmaril.Formats.Parquet.OffsetIndex.Defs

/-! Bounded ColumnIndex wire metadata for a flat INT32 column. -/

public section

namespace Silmaril.Formats.Parquet.ColumnIndex

open ThriftCompact
open Traversal (Reader Field)

structure Limits where
  offsetIndex : OffsetIndex.Limits := {}
  maxIndexBytes : Nat := 1024 * 1024
  maxEntries : Nat := 65536

inductive Error where
  | fileByteLimit
  | snapshot (reason : Snapshot.Error Unit)
  | groupIndex (index : Nat)
  | columnIndex (index : Nat)
  | partialReference
  | offsetIndex (reason : OffsetIndex.Error)
  | missingOffsetIndex
  | indexByteLimit
  | indexBounds
  | chunkBounds
  | overlapsChunk
  | overlapsOffsetIndex
  | compact (reason : Traversal.Error)
  | missingField (id : Int)
  | duplicateField (id : Int)
  | fieldType (id : Int) (actual : FieldType)
  | fieldExtent (id : Int)
  | boundaryOrder (tag : Int)
  | trailingBytes
  | entryCount (field : Int) (expected actual : Nat)
  | boundWidth
  | nullCount
  deriving DecidableEq, Repr

inductive BoundaryOrder where
  | unordered | ascending | descending
  deriving DecidableEq, Repr

structure Claim where
  allNull : Bool
  lower : Bytes
  upper : Bytes
  deriving DecidableEq

/-- Wire fields. Bounds retain the original bytes and order is an advertised tag. -/
structure Raw where
  nullPages : List Bool
  minValues : List Bytes
  maxValues : List Bytes
  order : BoundaryOrder
  nullCounts : Option (List Int)
  deriving DecidableEq

def Raw.claims (raw : Raw) : List Claim :=
  List.zipWith (fun allNull (lower, upper) => ⟨allNull, lower, upper⟩)
    raw.nullPages (raw.minValues.zip raw.maxValues)

structure Index where
  span : Footer.Span
  offsetIndex : OffsetIndex.Index
  raw : Raw
  deriving DecidableEq

/-- A successful validation gives exactly one claim for each checked page. -/
def Index.pages (index : Index) : List (OffsetIndex.Entry × Claim) :=
  index.offsetIndex.pages.zip index.raw.claims

private def field? (fields : List Field) (id : Int) : Except Error (Option Field) :=
  match fields.filter (·.id == id) with
  | [] => .ok none
  | [field] => .ok (some field)
  | _ => .error (.duplicateField id)

private def readField {α : Type} (type : ValueType)
    (read : Nat → Except Error (α × Nat)) (field : Field) : Except Error α := do
  if field.type ≠ .payload type then return ← throw (.fieldType field.id field.type)
  let (value, next) ← read field.start
  if next ≠ field.stop then return ← throw (.fieldExtent field.id)
  pure value

private def require {α : Type} (fields : List Field) (id : Int) (type : ValueType)
    (read : Nat → Except Error (α × Nat)) : Except Error α := do
  let some field ← field? fields id | throw (.missingField id)
  readField type read field

private def fromCompact {α : Type} (read : Nat → Except ThriftCompact.Error (α × Nat))
    (offset : Nat) : Except Error (α × Nat) :=
  (read offset).mapError (fun error => .compact (.compact error))

private def project (reader : Reader) (fields : List Field) : Except Error Raw := do
  let binaries := Traversal.readList reader Error.compact .binary
    (fromCompact (readBinary reader.mode reader.limits.maxBinaryBytes reader.source))
  let flags ← require fields 1 .list
    (Traversal.readList reader Error.compact .bool (fromCompact (readBool reader.source)))
  let lower ← require fields 2 .list binaries
  let upper ← require fields 3 .list binaries
  let tag ← require fields 4 .i32 (fromCompact (readSigned .i32 reader.mode reader.source))
  let order ← match tag with
    | 0 => pure BoundaryOrder.unordered
    | 1 => pure .ascending
    | 2 => pure .descending
    | _ => throw (.boundaryOrder tag)
  let counts ← (← field? fields 5).mapM (readField .list
    (Traversal.readList reader Error.compact .i64
      (fromCompact (readSigned .i64 reader.mode reader.source))))
  pure ⟨flags, lower, upper, order, counts⟩

/-- The collection cap applies before both structural traversal and typed list reads. -/
def readPrefix (limits : Limits) (bytes : Bytes) : Except Error (Raw × Nat) := do
  if bytes.length > limits.maxIndexBytes then return ← throw .indexByteLimit
  let compact := limits.offsetIndex.compact
  let cap := min compact.maxCollectionSize limits.maxEntries
  let reader : Reader := ⟨bytes, { compact with maxCollectionSize := cap }, limits.offsetIndex.varintMode⟩
  let (fields, next) ← (Traversal.readStruct reader 0).mapError .compact
  pure (← project reader fields, next)

def readExact (limits : Limits) (bytes : Bytes) : Except Error Raw := do
  let (raw, next) ← readPrefix limits bytes
  if next ≠ bytes.length then return ← throw .trailingBytes
  pure raw

abbrev Claim.ValidWidth (claim : Claim) : Prop :=
  let width := if claim.allNull then 0 else 4
  claim.lower.length = width ∧ claim.upper.length = width

abbrev ValidNullCount (count : Int) (page : OffsetIndex.Entry) (allNull : Bool) : Prop :=
  0 ≤ count ∧ count ≤ (page.rowCount : Int) ∧ (allNull = true ↔ count = (page.rowCount : Int))

structure Aligned (raw : Raw) (pages : List OffsetIndex.Entry) : Prop where
  flags : raw.nullPages.length = pages.length
  lower : raw.minValues.length = pages.length
  upper : raw.maxValues.length = pages.length
  widths : ∀ claim ∈ raw.claims, claim.ValidWidth
  counts : ∀ counts, raw.nullCounts = some counts → counts.length = pages.length ∧
    ∀ entry ∈ counts.zip (pages.zip raw.nullPages), ValidNullCount entry.1 entry.2.1 entry.2.2

private def checkCounts (counts : Option (List Int)) (pages : List OffsetIndex.Entry)
    (flags : List Bool) : Except Error Unit :=
  match counts with
  | none => .ok ()
  | some counts =>
    if counts.length ≠ pages.length then .error (.entryCount 5 pages.length counts.length)
    else if (counts.zip (pages.zip flags)).all (fun entry => decide (ValidNullCount entry.1 entry.2.1 entry.2.2))
      then .ok ()
    else .error .nullCount

/-- Compare only the shape of the advertised fields to the checked page list. -/
def checkShape (raw : Raw) (pages : List OffsetIndex.Entry) : Except Error Unit := do
  let count := pages.length
  if raw.nullPages.length ≠ count then return ← throw (.entryCount 1 count raw.nullPages.length)
  if raw.minValues.length ≠ count then return ← throw (.entryCount 2 count raw.minValues.length)
  if raw.maxValues.length ≠ count then return ← throw (.entryCount 3 count raw.maxValues.length)
  if !raw.claims.all (fun claim => decide claim.ValidWidth) then return ← throw .boundWidth
  checkCounts raw.nullCounts pages raw.nullPages

private def validateAt (limits : Limits) (snapshot : Snapshot.Checked) (column : Footer.ColumnChunk)
    (index : OffsetIndex.Index) (offset size : Int) : Except Error Index := do
  if (limits.maxIndexBytes : Int) < size then return ← throw .indexByteLimit
  let some span := Footer.checkDataSpan snapshot.footer.start offset size | throw .indexBounds
  let some chunk := Page.columnSpan snapshot.footer.start column.metadata | throw .chunkBounds
  if span.start < chunk.stop then return ← throw .overlapsChunk
  if ¬ (span.stop ≤ index.span.start ∨ index.span.stop ≤ span.start) then
    return ← throw .overlapsOffsetIndex
  if snapshot.bytes.length < span.stop then return ← throw .indexBounds
  let bytes := Footer.fileBytes snapshot.bytes span.start span.stop
  let raw ← readExact limits bytes
  let _ ← checkShape raw index.pages
  pure ⟨span, index, raw⟩

/-- An absent pair reports absence at the selected ordinal. A present pair
requires a checked OffsetIndex for that same snapshot, group and column. -/
def validate (limits : Limits) (snapshot : Snapshot.Checked) (groupIndex columnIndex : Nat) :
    Except Error (Option Index) := do
  let some group := snapshot.groupAt groupIndex | throw (.groupIndex groupIndex)
  let some column := group.columns[columnIndex]? | throw (.columnIndex columnIndex)
  match column.columnIndexOffset, column.columnIndexLength with
  | none, none => pure none
  | some offset, some size =>
    let some index ← (OffsetIndex.validate limits.offsetIndex snapshot groupIndex columnIndex).mapError Error.offsetIndex
      | throw .missingOffsetIndex
    some <$> validateAt limits snapshot column index offset size
  | _, _ => throw .partialReference

def readFile (limits : Limits) (source : Bytes) (groupIndex columnIndex : Nat) :
    Except Error (Option Index) := do
  if source.length > limits.offsetIndex.maxFileBytes then return ← throw .fileByteLimit
  let snapshot ← (Snapshot.check limits.offsetIndex.snapshot source).mapError Error.snapshot
  validate limits snapshot groupIndex columnIndex

structure Evidence (limits : Limits) (snapshot : Snapshot.Checked) (g c : Nat)
    (result : Index) (group : Footer.RowGroup) (column : Footer.ColumnChunk)
    (chunk : Footer.Span) (offsetBytes bytes : Bytes) : Prop where
  offsets : OffsetIndex.Evidence limits.offsetIndex snapshot g c result.offsetIndex group column chunk offsetBytes
  offset : column.columnIndexOffset = some (Int.ofNat result.span.start)
  size : column.columnIndexLength = some (Int.ofNat (result.span.stop - result.span.start))
  bounds : 4 ≤ result.span.start ∧ result.span.start < result.span.stop ∧ result.span.stop ≤ snapshot.footer.start
  afterChunk : chunk.stop ≤ result.span.start
  separated : result.span.stop ≤ result.offsetIndex.span.start ∨ result.offsetIndex.span.stop ≤ result.span.start
  cap : bytes.length ≤ limits.maxIndexBytes
  slice : snapshot.bytes.slice? result.span.start (some result.span.stop) = some bytes
  parsed : readPrefix limits bytes = .ok (result.raw, bytes.length)
  shape : Aligned result.raw result.offsetIndex.pages

end Silmaril.Formats.Parquet.ColumnIndex
