module

public import Silmaril.Formats.Arrow.Stream.Defs
public import Init.Data.SInt.Basic

/-! Physical little-endian Int32 and Utf8 buffers and their ordered nullable
observation. Descriptor ordering and field-node length constraints come from
the checked metadata frame. -/

@[expose] public section

namespace Silmaril.Formats.Arrow

inductive Value where
  | int32 (value : Int32)
  | utf8 (value : String)
  deriving DecidableEq, Repr

abbrev Row := List (Option Value)
abbrev Column := List (Option Value)

/-- Per-batch IPC limits and aggregate budgets for materialized rows and cells.
Null cells and rows of a zero-column schema count toward the budgets. -/
structure ObservationLimits where
  ipc : Limits := {}
  totalRows : Nat := 1024 * 1024
  totalCells : Nat := 8 * 1024 * 1024
  deriving Repr

structure ObservedStream where
  fields : List Field
  batches : List (List Row)
  deriving DecidableEq, Repr

namespace Body

inductive ColumnBuffers where
  | int32 (validity values : KBytes)
  | utf8 (validity offsets data : KBytes)

def ColumnBuffers.validity : ColumnBuffers → KBytes
  | .int32 bitmap _ | .utf8 bitmap _ _ => bitmap

def ColumnBuffers.payloadError : ColumnBuffers → Malformed
  | .int32 .. => .bodyValues
  | .utf8 .. => .stringOffsets

/-- An omitted bitmap means every slot is valid. A materialized bitmap uses
least-significant-bit numbering within each octet. -/
def validAt (bitmap : KBytes) (index : Nat) : Option Bool :=
  if bitmap.len = 0 then some true
  else (bitmap.get? (index / 8)).map fun byte => byte.toNat.testBit (index % 8)

/-- Signed i32 offsets are represented as naturals after rejecting the sign bit. -/
def offsetAt (offsets : KBytes) (index : Nat) : Option Nat := do
  let word ← offsets.readLE (4 * index) 4
  if word < 2^31 then some word else none

def BitmapExtent (bitmap : KBytes) (rows : Nat) : Prop :=
  bitmap.len = 0 ∨ rows ≤ 8 * bitmap.len

instance (bitmap : KBytes) (rows : Nat) : Decidable (BitmapExtent bitmap rows) := by
  unfold BitmapExtent
  infer_instance

/-- Required logical extent. Buffer descriptors can include trailing padding.
Even an empty Utf8 column has one checked offset. -/
def PayloadExtent (buffers : ColumnBuffers) (rows : Nat) : Prop :=
  match buffers with
  | .int32 _ values => 4 * rows ≤ values.len
  | .utf8 _ offsets data =>
    4 * (rows + 1) ≤ offsets.len ∧
      ((offsetAt offsets 0).any fun first => decide (first ≤ data.len)) = true

instance (buffers : ColumnBuffers) (rows : Nat) : Decidable (PayloadExtent buffers rows) := by
  cases buffers <;> unfold PayloadExtent <;> infer_instance

def readCell (buffers : ColumnBuffers) (index : Nat) : Except Error (Option Value) := do
  let some valid := validAt buffers.validity index
    | throw (.malformed .validityBitmap)
  match buffers with
  | .int32 _ values =>
    let some word := values.readLE (4 * index) 4 | throw (.malformed .bodyValues)
    return if valid then some (.int32 (Int32.ofNat word)) else none
  | .utf8 _ offsets data =>
    let some lo := offsetAt offsets index | throw (.malformed .stringOffsets)
    let some hi := offsetAt offsets (index + 1) | throw (.malformed .stringOffsets)
    if ¬ (lo ≤ hi ∧ hi ≤ data.len) then throw (.malformed .stringOffsets)
    if !valid then return none
    let some text := String.fromUTF8? (data.slice lo (hi - lo)).toByteArray
      | throw (.malformed .invalidUtf8)
    return some (.utf8 text)

def readColumn (node : FieldNode) (buffers : ColumnBuffers) : Except Error Column := do
  if ¬ BitmapExtent buffers.validity node.length then throw (.malformed .validityBitmap)
  if ¬ PayloadExtent buffers node.length then throw (.malformed buffers.payloadError)
  let values ← (List.range node.length).mapM (readCell buffers)
  if values.countP Option.isNone ≠ node.nullCount then throw (.malformed .validityBitmap)
  return values

def sliceBuffer (body : KBytes) (buffer : Buffer) : KBytes :=
  body.slice buffer.offset buffer.length

/-- Consume successive descriptors in schema order. The caller has a checked
layout, so every slice is inside the batch body. -/
def nextColumn (body : KBytes) : FieldType → List Buffer → Option (ColumnBuffers × List Buffer)
  | .int32, bitmap :: values :: rest =>
    some (.int32 (sliceBuffer body bitmap) (sliceBuffer body values), rest)
  | .utf8, bitmap :: offsets :: data :: rest =>
    some (.utf8 (sliceBuffer body bitmap) (sliceBuffer body offsets) (sliceBuffer body data), rest)
  | _, _ => none

def readColumns (body : KBytes) :
    List Field → List FieldNode → List Buffer → Except Error (List Column)
  | [], [], [] => .ok []
  | field :: fields, node :: nodes, descriptors => do
    let some (buffers, rest) := nextColumn body field.type descriptors
      | throw (.malformed .batchLayout)
    let column ← readColumn node buffers
    let columns ← readColumns body fields nodes rest
    return column :: columns
  | _, _, _ => .error (.malformed .batchLayout)

/-- Preserve schema order and the row count, including at zero columns. -/
def rowsOfColumns (rowCount : Nat) (columns : List Column) : List Row :=
  columns.foldr (List.zipWith List.cons) (List.replicate rowCount [])

def checkBudget (limits : ObservationLimits) (fields rows : Nat) : Except Error Unit :=
  if rows > limits.totalRows then .error (.limit .totalRows)
  else if fields * rows > limits.totalCells then .error (.limit .totalCells)
  else .ok ()

def checkBatch (limits : ObservationLimits) {fields : List Field} (frame : BatchFrame fields) :
    Except Error Unit := do
  if !frame.body.wf then throw (.malformed .source)
  if fields.length > limits.ipc.fields then throw (.limit .fields)
  if frame.body.len > limits.ipc.bodyBytes then throw (.limit .bodyBytes)
  if frame.metadata.rowCount > limits.ipc.rows then throw (.limit .rows)
  checkBudget limits fields.length frame.metadata.rowCount

/-- A slot is observed only if its physical extent is valid. Utf8 offsets also
constrain null slots, whose data bytes have no observable value. -/
def CellWire (buffers : ColumnBuffers) (index : Nat) (value : Option Value) : Prop :=
  ∃ valid, validAt buffers.validity index = some valid ∧
    match buffers with
    | .int32 _ values =>
      ∃ word, values.readLE (4 * index) 4 = some word ∧
        value = (if valid then some (.int32 (Int32.ofNat word)) else none)
    | .utf8 _ offsets data =>
      ∃ lo hi, offsetAt offsets index = some lo ∧ offsetAt offsets (index + 1) = some hi ∧
        lo ≤ hi ∧ hi ≤ data.len ∧
        if valid then
          ∃ text, String.fromUTF8? (data.slice lo (hi - lo)).toByteArray = some text ∧
            value = some (.utf8 text)
        else value = none

def CellsWire (buffers : ColumnBuffers) : List Nat → Column → Prop
  | [], [] => True
  | index :: indices, value :: values =>
    CellWire buffers index value ∧ CellsWire buffers indices values
  | _, _ => False

def ColumnWire (node : FieldNode) (buffers : ColumnBuffers) (values : Column) : Prop :=
  BitmapExtent buffers.validity node.length ∧ PayloadExtent buffers node.length ∧
    CellsWire buffers (List.range node.length) values ∧
    values.countP Option.isNone = node.nullCount

/-- Column observations retain field order and consume every node and buffer. -/
def ColumnsWire (body : KBytes) :
    List Field → List FieldNode → List Buffer → List Column → Prop
  | [], [], [], [] => True
  | field :: fields, node :: nodes, descriptors, column :: columns =>
    ∃ buffers rest, nextColumn body field.type descriptors = some (buffers, rest) ∧
      ColumnWire node buffers column ∧ ColumnsWire body fields nodes rest columns
  | _, _, _, _ => False

end Body

/-- A batch denotes the transpose of its ordered, validated column observations. -/
def BatchWire {fields : List Field} (frame : BatchFrame fields) (rows : List Row) : Prop :=
  ∃ columns, Body.ColumnsWire frame.body fields frame.metadata.nodes frame.metadata.buffers columns ∧
    rows = Body.rowsOfColumns frame.metadata.rowCount columns

/-- Materialize a checked frame as ordered nullable rows. -/
def decodeBatch (limits : ObservationLimits) {fields : List Field} (frame : BatchFrame fields) :
    Except Error (List Row) := do
  Body.checkBatch limits frame
  let columns ← Body.readColumns frame.body fields frame.metadata.nodes frame.metadata.buffers
  return Body.rowsOfColumns frame.metadata.rowCount columns

/-- Parse framed metadata, then validate and materialize the physical buffers.
The stream budget is checked before rows or cells are allocated. -/
def readRows (limits : ObservationLimits) (input : KBytes) : Except Error ObservedStream := do
  let stream ← readStream limits.ipc input
  let rows := (stream.batches.map fun frame => frame.metadata.rowCount).sum
  Body.checkBudget limits stream.fields.length rows
  return ⟨stream.fields, ← stream.batches.mapM (decodeBatch limits)⟩

end Silmaril.Formats.Arrow
