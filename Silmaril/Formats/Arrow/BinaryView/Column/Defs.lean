module

public import Silmaril.Formats.Arrow.BinaryView.Defs
public import Silmaril.Formats.Arrow.Body.Defs

/-! A bounded nullable column over the little-endian Arrow view layout.
The caller supplies the field node, nullability and ordered physical buffers. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView.Column

structure Limits where
  rows : Nat := 65536
  dataBuffers : Nat := 1024
  bufferBytes : Nat := 64 * 1024 * 1024
  valueBytes : Nat := 1024 * 1024
  outputBytes : Nat := 64 * 1024 * 1024
  deriving Repr

structure Buffers where
  validity : KBytes
  payload : BinaryView.Buffers

inductive Error where
  | rowLimit
  | dataBufferLimit
  | bufferBytesLimit
  | outputBytesLimit
  | malformedSource
  | invalidBitmap
  | truncatedViews
  | invalidNullCount
  | slot (index : Nat) (cause : BinaryView.Error)
  | invalidUtf8
  deriving DecidableEq, Repr

def Buffers.byteCount (input : Buffers) : Nat :=
  input.payload.data.foldl (fun bytes data => bytes + data.len)
    (input.validity.len + input.payload.views.len)

/-- Cover every logical slot. Trailing descriptor padding is allowed.
An omitted bitmap represents a column with no nulls. -/
def BuffersFit (limits : Limits) (node : FieldNode) (nullable : Bool) (input : Buffers) : Prop :=
  node.length ≤ limits.rows ∧ input.payload.data.size ≤ limits.dataBuffers ∧
    input.byteCount ≤ limits.bufferBytes ∧
    (input.validity.wf = true ∧ input.payload.views.wf = true ∧
      input.payload.data.all (·.wf) = true) ∧
    Body.BitmapExtent input.validity node.length ∧
    16 * node.length ≤ input.payload.views.len ∧
    (node.nullCount ≤ node.length ∧ (nullable = true ∨ node.nullCount = 0))

def checkBuffers (limits : Limits) (node : FieldNode) (nullable : Bool) (input : Buffers) :
    Except Error Unit :=
  if ¬ node.length ≤ limits.rows then .error .rowLimit
  else if ¬ input.payload.data.size ≤ limits.dataBuffers then .error .dataBufferLimit
  else if ¬ input.byteCount ≤ limits.bufferBytes then .error .bufferBytesLimit
  else if ¬ (input.validity.wf = true ∧ input.payload.views.wf = true ∧
      input.payload.data.all (·.wf) = true) then .error .malformedSource
  else if ¬ Body.BitmapExtent input.validity node.length then .error .invalidBitmap
  else if ¬ 16 * node.length ≤ input.payload.views.len then .error .truncatedViews
  else if ¬ (node.nullCount ≤ node.length ∧ (nullable = true ∨ node.nullCount = 0)) then
    .error .invalidNullCount
  else .ok ()

def readSlot (input : Buffers) (index maxValueBytes : Nat) : Except Error (Option KBytes) :=
  match Body.validAt input.validity index with
  | none => .error .invalidBitmap
  | some false => .ok none
  | some true => ((BinaryView.readBinary input.payload index maxValueBytes).map some).mapError (.slot index)

def valueByteCount (values : List (Option KBytes)) : Nat :=
  (values.map fun value => (value.map KBytes.len).getD 0).sum

/-- Check the logical and physical input bounds before allocating slots.
Null slots contribute zero bytes. Overlapping views count for each
occurrence in the output budget. -/
def readBinary (limits : Limits) (node : FieldNode) (nullable : Bool) (input : Buffers) :
    Except Error (List (Option KBytes)) := do
  checkBuffers limits node nullable input
  let values ← (List.range node.length).mapM fun index => readSlot input index limits.valueBytes
  if values.countP Option.isNone ≠ node.nullCount then .error .invalidNullCount
  else if ¬ valueByteCount values ≤ limits.outputBytes then .error .outputBytesLimit
  else .ok values

def decodeUtf8 (bytes : KBytes) : Except Error String :=
  match String.fromUTF8? bytes.toByteArray with
  | some text => .ok text
  | none => .error .invalidUtf8

/-- Check the aggregate byte budget before materializing any strings. -/
def readUtf8 (limits : Limits) (node : FieldNode) (nullable : Bool) (input : Buffers) :
    Except Error (List (Option String)) := do
  let values ← readBinary limits node nullable input
  values.mapM (·.mapM decodeUtf8)

def SlotWire (input : Buffers) (index maxValueBytes : Nat) : Option KBytes → Prop
  | none => Body.validAt input.validity index = some false
  | some value => Body.validAt input.validity index = some true ∧
      BinaryView.Wire input.payload index maxValueBytes value

def SlotsWire (input : Buffers) (maxValueBytes : Nat) : List Nat → List (Option KBytes) → Prop
  | [], [] => True
  | index :: rest, value :: values =>
    SlotWire input index maxValueBytes value ∧ SlotsWire input maxValueBytes rest values
  | _, _ => False

def Wire (limits : Limits) (node : FieldNode) (nullable : Bool) (input : Buffers)
    (values : List (Option KBytes)) : Prop :=
  BuffersFit limits node nullable input ∧ SlotsWire input limits.valueBytes (List.range node.length) values ∧
    values.countP Option.isNone = node.nullCount ∧ valueByteCount values ≤ limits.outputBytes

end Silmaril.Formats.Arrow.BinaryView.Column
