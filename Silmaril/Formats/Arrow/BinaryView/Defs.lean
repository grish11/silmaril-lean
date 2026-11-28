module

public import Silmaril.Prelude.Bytes.Defs
public import Init.Data.String.Decode

/-! A single non-null Arrow BinaryView or Utf8View slot in the little-endian
profile. Variadic buffers are supplied separately in wire order. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView

structure Buffers where
  views : KBytes
  data : Array KBytes

inductive Error where
  | malformedSource
  | truncatedSlot
  | negativeLength
  | valueLimit
  | invalidPadding
  | invalidReference
  | prefixMismatch
  | invalidUtf8
  deriving DecidableEq, Repr

/-- Read a 16-byte slot after checking its complete extent. Long views can
select any supplied data buffer and can overlap other valid views. -/
def readBinary (buffers : Buffers) (index maxValueBytes : Nat) : Except Error KBytes :=
  let start := 16 * index
  if buffers.views.wf ≠ true then .error .malformedSource
  else if ¬ start + 16 ≤ buffers.views.len then .error .truncatedSlot
  else
    let length := buffers.views.read start 4
    if ¬ length < 2^31 then .error .negativeLength
    else if ¬ length ≤ maxValueBytes then .error .valueLimit
    else if length ≤ 12 then
      if buffers.views.read (start + 4 + length) (12 - length) = 0 then
        .ok (buffers.views.slice (start + 4) length)
      else .error .invalidPadding
    else
      let bufferIndex := buffers.views.read (start + 8) 4
      let offset := buffers.views.read (start + 12) 4
      if ¬ (bufferIndex < 2^31 ∧ offset < 2^31) then .error .invalidReference
      else
        match buffers.data[bufferIndex]? with
        | none => .error .invalidReference
        | some data =>
          if data.wf ≠ true then .error .malformedSource
          else if ¬ offset + length ≤ data.len then .error .invalidReference
          else if buffers.views.read (start + 4) 4 ≠ data.read offset 4 then .error .prefixMismatch
          else .ok (data.slice offset length)

def readUtf8 (buffers : Buffers) (index maxValueBytes : Nat) : Except Error String := do
  let bytes ← readBinary buffers index maxValueBytes
  let some text := String.fromUTF8? bytes.toByteArray | throw .invalidUtf8
  return text

/-- The slot's length word determines its wire layout. The result is the
exact window specified by the inline layout or the selected buffer. -/
def Wire (buffers : Buffers) (index maxValueBytes : Nat) (value : KBytes) : Prop :=
  let start := 16 * index
  let length := buffers.views.read start 4
  let bufferIndex := buffers.views.read (start + 8) 4
  let offset := buffers.views.read (start + 12) 4
  buffers.views.wf = true ∧ start + 16 ≤ buffers.views.len ∧
    length < 2^31 ∧ length ≤ maxValueBytes ∧
    ((length ≤ 12 ∧ buffers.views.read (start + 4 + length) (12 - length) = 0 ∧
        buffers.views.slice (start + 4) length = value) ∨
      (12 < length ∧ (bufferIndex < 2^31 ∧ offset < 2^31) ∧
        ∃ data, buffers.data[bufferIndex]? = some data ∧
          data.wf = true ∧ offset + length ≤ data.len ∧
          buffers.views.read (start + 4) 4 = data.read offset 4 ∧
          data.slice offset length = value))

end Silmaril.Formats.Arrow.BinaryView
