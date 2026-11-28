module

public import Silmaril.Formats.Arrow.Body.Defs
public import Silmaril.Prelude.Bytes.Write.Defs
public import Init.Data.List.Scan.Basic

/-! Physical Arrow IPC batch writing for the flat Int32 and Utf8 profile.
The output is the aligned body and the metadata AST for one record batch.
The stream envelope and FlatBuffers serialization are separate. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.Writer

inductive ColumnValues where
  | int32 (values : List (Option Int32))
  | utf8 (values : List (Option String))
  deriving Repr

def ColumnValues.type : ColumnValues → FieldType
  | .int32 _ => .int32
  | .utf8 _ => .utf8

def ColumnValues.observe : ColumnValues → Column
  | .int32 values => values.map (Option.map Value.int32)
  | .utf8 values => values.map (Option.map Value.utf8)

def ColumnValues.length : ColumnValues → Nat
  | .int32 values => values.length
  | .utf8 values => values.length

def ColumnValues.nullCount : ColumnValues → Nat
  | .int32 values => values.countP Option.isNone
  | .utf8 values => values.countP Option.isNone

structure NamedColumn where
  name : String
  nullable : Bool
  values : ColumnValues
  deriving Repr

def NamedColumn.field (column : NamedColumn) : Field :=
  ⟨column.name, column.nullable, column.values.type⟩

def NamedColumn.node (column : NamedColumn) : FieldNode :=
  ⟨column.values.length, column.values.nullCount⟩

/-- Explicit row count preserves rows in a zero-column batch. -/
structure BatchInput where
  rowCount : Nat
  columns : List NamedColumn
  deriving Repr

def BatchInput.fields (input : BatchInput) : List Field :=
  input.columns.map NamedColumn.field

def BatchInput.observe (input : BatchInput) : List Row :=
  Body.rowsOfColumns input.rowCount (input.columns.map fun column => column.values.observe)

def padding (size : Nat) : Nat := (8 - size % 8) % 8

/-- Fixed-size little-endian chunks. The byte tree is balanced by the shared
kernel byte constructor. -/
def emitWords (width : Nat) (words : List Nat) : KBytes :=
  KBytes.ofChunks width (width * words.length) words

def lowBits : List Bool → Nat
  | [] => 0
  | value :: rest => (if value then 1 else 0) + 2 * lowBits rest

def bitmapWords (bits : List Bool) : List Nat :=
  if bits.isEmpty then [] else
    lowBits (bits.take 8) :: bitmapWords (bits.drop 8)
termination_by bits.length
decreasing_by
  have nonempty : bits ≠ [] := by simpa using ‹¬bits.isEmpty = true›
  simp [List.length_drop]
  cases bits <;> simp_all <;> omega

def emitBitmap {α : Type} (slots : List (Option α)) : KBytes :=
  emitWords 1 (bitmapWords (slots.map Option.isSome))

def utf8ByteCount (slots : List (Option String)) : Nat :=
  (slots.map fun value => (value.map String.utf8ByteSize).getD 0).sum

def utf8OffsetWords (start : Nat) (values : List (Option String)) : List Nat :=
  values.scanl (fun offset value => offset + (value.map String.utf8ByteSize).getD 0) start

def ColumnValues.bufferSizes : ColumnValues → List Nat
  | .int32 values => [(values.length + 7) / 8, 4 * values.length]
  | .utf8 values => [(values.length + 7) / 8, 4 * (values.length + 1), utf8ByteCount values]

def utf8Part (value : Option String) : List UInt8 :=
  (value.getD "").toByteArray.data.toList

def ColumnValues.encode : ColumnValues → Body.ColumnBuffers
  | .int32 values =>
    .int32 (emitBitmap values) (emitWords 4 (values.map fun value => (value.getD 0).toUInt32.toNat))
  | .utf8 values =>
    .utf8 (emitBitmap values) (emitWords 4 (utf8OffsetWords 0 values))
      (emitWords 1 ((values.flatMap utf8Part).map UInt8.toNat))

def bufferParts : Body.ColumnBuffers → List KBytes
  | .int32 bitmap values => [bitmap, values]
  | .utf8 bitmap offsets bytes => [bitmap, offsets, bytes]

def ColumnValues.emit (values : ColumnValues) : List KBytes :=
  bufferParts values.encode

/-- Buffer lengths exclude padding, including for zero-length buffers.
The returned body starts at the supplied absolute descriptor offset. -/
def packBuffers (offset : Nat) : List KBytes → List Buffer × KBytes
  | [] => ([], KBytes.empty)
  | first :: rest =>
    let gap := padding first.len
    let (descriptors, tail) := packBuffers (offset + first.len + gap) rest
    (⟨offset, first.len⟩ :: descriptors, first ++ (KBytes.zeros gap ++ tail))

def ColumnValues.OffsetFits : ColumnValues → Prop
  | .int32 _ => True
  | .utf8 values => utf8ByteCount values < 2^31

instance (values : ColumnValues) : Decidable values.OffsetFits := by
  cases values <;> unfold ColumnValues.OffsetFits <;> infer_instance

def BatchInput.bodySize (input : BatchInput) : Nat :=
  ((input.columns.flatMap fun column => column.values.bufferSizes).map
    fun size => size + padding size).sum

def BatchInput.Shape (input : BatchInput) : Prop :=
  ∀ column ∈ input.columns, column.node.Fits input.rowCount column.field

instance (input : BatchInput) : Decidable input.Shape := by
  unfold BatchInput.Shape
  infer_instance

def BatchInput.OffsetsFit (input : BatchInput) : Prop :=
  ∀ column ∈ input.columns, column.values.OffsetFits

instance (input : BatchInput) : Decidable input.OffsetsFit := by
  unfold BatchInput.OffsetsFit
  infer_instance

def BatchInput.WireSize (input : BatchInput) : Prop :=
  input.rowCount < 2^63 ∧ input.bodySize < 2^63

instance (input : BatchInput) : Decidable input.WireSize := by
  unfold BatchInput.WireSize
  infer_instance

/-- Shape, signed offset representability, and budgets for a physical batch. -/
structure Admitted (limits : ObservationLimits) (input : BatchInput) : Prop where
  fields : input.columns.length ≤ limits.ipc.fields
  rows : input.rowCount ≤ limits.ipc.rows
  budget : Body.checkBudget limits input.columns.length input.rowCount = .ok ()
  shape : input.Shape
  offsets : input.OffsetsFit
  bodyBytes : input.bodySize ≤ limits.ipc.bodyBytes
  wireSize : input.WireSize

def checkInput (limits : ObservationLimits) (input : BatchInput) : Except Error Unit := do
  if input.columns.length > limits.ipc.fields then throw (.limit .fields)
  if input.rowCount > limits.ipc.rows then throw (.limit .rows)
  Body.checkBudget limits input.columns.length input.rowCount
  if input.Shape then
    if input.OffsetsFit then
      if input.bodySize ≤ limits.ipc.bodyBytes then
        if input.WireSize then return ()
        else throw (.malformed .batchLayout)
      else throw (.limit .bodyBytes)
    else throw (.malformed .stringOffsets)
  else throw (.malformed .batchLayout)

/-- Emit descriptors and body, then construct a layout-checked batch frame. -/
def emitBatch (limits : ObservationLimits) (input : BatchInput) :
    Except Error (BatchFrame input.fields) := do
  checkInput limits input
  let (descriptors, body) := packBuffers 0 (input.columns.flatMap fun column => column.values.emit)
  validateBatch input.fields ⟨input.rowCount, input.columns.map NamedColumn.node, descriptors⟩ body

/-- The ordered physical buffer windows associated with a list of descriptors. -/
def PackedWire (bytes : List UInt8) : Nat → List KBytes → List Buffer → Prop
  | _, [], [] => True
  | offset, first :: rest, descriptor :: tail =>
    descriptor = ⟨offset, first.len⟩ ∧
      (bytes.drop offset).take first.len = first.toList ∧
      PackedWire bytes (offset + first.len + padding first.len) rest tail
  | _, _, _ => False

end Silmaril.Formats.Arrow.Writer
