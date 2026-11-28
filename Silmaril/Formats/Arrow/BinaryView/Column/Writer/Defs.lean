module

public import Silmaril.Formats.Arrow.BinaryView.Column.Defs
public import Silmaril.Formats.Arrow.Writer.Defs

/-! Canonical physical buffers for one nullable Arrow view column. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView.Column.Writer

inductive Error where
  | rowLimit
  | nullInRequired
  | valueLimit
  | signedExtent
  | dataBufferLimit
  | bufferBytesLimit
  | outputBytesLimit
  | malformedSource
  deriving DecidableEq, Repr

structure Emitted where
  node : FieldNode
  buffers : Column.Buffers

def bitmapBytes (rows : Nat) : Nat := (rows + 7) / 8

def longSize (length : Nat) : Nat := if 12 < length then length else 0

def valueSize {α : Type} (length : α → Nat) (value : Option α) : Nat :=
  (value.map length).getD 0

def longBytes {α : Type} (length : α → Nat) (values : List (Option α)) : Nat :=
  (values.map (longSize ∘ valueSize length)).sum

def dataCount (length : Nat) : Nat := if length = 0 then 0 else 1

/-- Check the entire input before allocating the bitmap, views, or data. The
signed bound on total long bytes bounds every length and external offset. -/
def checkInput {α : Type} (limits : Limits) (nullable : Bool) (length : α → Nat)
    (values : List (Option α)) : Except Error Unit :=
  if values.length > limits.rows then .error .rowLimit
  else if !nullable && values.any Option.isNone then .error .nullInRequired
  else if values.any (fun value => valueSize length value > limits.valueBytes) then .error .valueLimit
  else
    let dataBytes := longBytes length values
    if dataBytes ≥ 2^31 then .error .signedExtent
    else if dataCount dataBytes > limits.dataBuffers then .error .dataBufferLimit
    else if bitmapBytes values.length + 16 * values.length + dataBytes > limits.bufferBytes then
      .error .bufferBytesLimit
    else if (values.map (valueSize length)).sum > limits.outputBytes then .error .outputBytesLimit
    else .ok ()

/-- Join byte pieces with a balanced spine, sharing their existing subtrees. -/
def joinAux : Nat → List KBytes → KBytes
  | 0, pieces => pieces.foldr (· ++ ·) KBytes.empty
  | _ + 1, [] => KBytes.empty
  | _ + 1, [piece] => piece
  | fuel + 1, first :: second :: rest =>
    let pieces := first :: second :: rest
    let middle := pieces.length / 2
    joinAux fuel (pieces.take middle) ++ joinAux fuel (pieces.drop middle)

def join (pieces : List KBytes) : KBytes := joinAux (pieces.length.log2 + 1) pieces

def longPart (value : Option KBytes) : KBytes :=
  let bytes := value.getD KBytes.empty
  if 12 < bytes.len then bytes else KBytes.empty

/-- Both layouts occupy sixteen bytes. A null has a zero slot. -/
def slot (offset : Nat) (value : Option KBytes) : KBytes :=
  let bytes := value.getD KBytes.empty
  if bytes.len ≤ 12 then
    .leaf 4 bytes.len ++ (bytes ++ .leaf (12 - bytes.len) 0)
  else
    .leaf 4 bytes.len ++ (bytes.slice 0 4 ++ (.leaf 4 0 ++ .leaf 4 offset))

def slots : Nat → List (Option KBytes) → List KBytes
  | _, [] => []
  | offset, value :: rest => slot offset value :: slots (offset + (longPart value).len) rest

/-- Encode an already admitted column in field buffer order. -/
def encode (values : List (Option KBytes)) : Emitted :=
  let data := join (values.map longPart)
  let dataBuffers := if data.len = 0 then #[] else #[data]
  ⟨⟨values.length, values.countP Option.isNone⟩,
    ⟨Arrow.Writer.emitBitmap values, ⟨join (slots 0 values), dataBuffers⟩⟩⟩

def emitBinary (limits : Limits) (nullable : Bool) (values : List (Option KBytes)) :
    Except Error Emitted := do
  checkInput limits nullable KBytes.len values
  if !values.all (fun value => (value.map KBytes.wf).getD true) then throw .malformedSource
  return encode values

def utf8Bytes (text : String) : KBytes :=
  Arrow.Writer.emitWords 1 (text.toByteArray.data.toList.map UInt8.toNat)

def emitUtf8 (limits : Limits) (nullable : Bool) (values : List (Option String)) :
    Except Error Emitted := do
  checkInput limits nullable String.utf8ByteSize values
  return encode (values.map (·.map utf8Bytes))

/-- Canonical slot fields and payload windows on an emitted column. -/
def SlotEncoding (buffers : BinaryView.Column.Buffers) (index offset : Nat)
    (value : Option KBytes) : Prop :=
  let bytes := value.getD KBytes.empty
  let start := 16 * index
  Body.validAt buffers.validity index = some value.isSome ∧
    buffers.payload.views.read start 4 = bytes.len ∧ bytes.len < 2^31 ∧
    if bytes.len ≤ 12 then
      buffers.payload.views.read (start + 4 + bytes.len) (12 - bytes.len) = 0 ∧
      (buffers.payload.views.slice (start + 4) bytes.len).toList = bytes.toList
    else
      buffers.payload.views.read (start + 8) 4 = 0 ∧
      buffers.payload.views.read (start + 12) 4 = offset ∧ offset < 2^31 ∧
      ∃ data, buffers.payload.data[0]? = some data ∧ data.wf = true ∧
        offset + bytes.len ≤ data.len ∧
        buffers.payload.views.read (start + 4) 4 = data.read offset 4 ∧
        (data.slice offset bytes.len).toList = bytes.toList

structure Layout (limits : Limits) (nullable : Bool) (values : List (Option KBytes))
    (result : Emitted) : Prop where
  node : result.node = ⟨values.length, values.countP Option.isNone⟩
  fits : Column.BuffersFit limits result.node nullable result.buffers
  bitmap : result.buffers.validity = Arrow.Writer.emitBitmap values
  bitmapSize : result.buffers.validity.len = bitmapBytes values.length
  viewsSize : result.buffers.payload.views.len = 16 * values.length
  variadicCount : result.buffers.payload.data.size = dataCount (longBytes KBytes.len values)
  bufferSize : result.buffers.byteCount =
    bitmapBytes values.length + 16 * values.length + longBytes KBytes.len values
  dataBytes : result.buffers.payload.data.toList.flatMap KBytes.toList =
    values.flatMap (KBytes.toList ∘ longPart)
  signedExtent : longBytes KBytes.len values < 2^31
  valueBound : ∀ value ∈ values, valueSize KBytes.len value ≤ limits.valueBytes
  outputBound : valueByteCount values ≤ limits.outputBytes
  slot : ∀ (index : Nat) (bound : index < values.length),
    SlotEncoding result.buffers index (longBytes KBytes.len (values.take index)) values[index]

end Silmaril.Formats.Arrow.BinaryView.Column.Writer
