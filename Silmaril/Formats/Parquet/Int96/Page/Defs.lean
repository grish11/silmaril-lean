module

public import Silmaril.Formats.Parquet.Int96.Defs
public import Silmaril.Formats.Parquet.Footer.Metadata.Defs
public import Silmaril.Formats.Parquet.Page.Header.Defs
public import Silmaril.Formats.Parquet.ScalarPage.Defs

/-! Nullable legacy INT96 values from a standalone, bounded PLAIN page. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Int96.Page

open Silmaril.Numeric.Timestamp

inductive Error where
  | schemaLevels
  | unsupportedCodec (id : Int)
  | unsupportedChecksum
  | unsupportedPage
  | scalar (cause : ScalarPage.Error)
  | invalidWord (slot : Nat)
  deriving DecidableEq, Repr

/-- Derive the only two admitted level schemas from a flat physical INT96 leaf. -/
def leafLevels? (leaf : Footer.SchemaElement) : Option FlatPage.LevelSchema :=
  if leaf.physicalType = some .int96 ∧ leaf.numChildren.getD 0 = 0 then
    match leaf.repetition with
    | some .required => some ⟨0, 0⟩
    | some .optional => some ⟨0, 1⟩
    | _ => none
  else none

/-- Retain the version-specific counts, sizes and encoding of the given
header. Codec and checksum admission is explicit at this boundary. -/
def parameters (leaf : Footer.SchemaElement) (codec : Int) (header : Parquet.Page.Header) :
    Except Error ScalarPage.Parameters := do
  let some levels := leafLevels? leaf | Except.error .schemaLevels
  if codec ≠ 0 then Except.error (.unsupportedCodec codec)
  if header.crc.isSome then Except.error .unsupportedChecksum
  let sizes : ScalarPage.Sizes := ⟨header.compressedSize, header.uncompressedSize⟩
  match header.kind with
  | .dataV1 info =>
    return ⟨sizes, levels, info.numValues, codec, info.encoding,
      .v1 info.definitionLevelEncoding info.repetitionLevelEncoding⟩
  | .dataV2 info =>
    return ⟨sizes, levels, info.numValues, codec, info.encoding,
      .v2 info.numNulls info.numRows info.repetitionBytes info.definitionBytes (some info.isCompressed)⟩
  | _ => Except.error .unsupportedPage

def decodeSlot (index : Nat) : Option Bytes → Except Error (Option Payload)
  | none => .ok none
  | some word =>
    match Payload.decode? word.toList with
    | some payload => .ok (some payload)
    | none => .error (.invalidWord index)

/-- The index advances across nulls as well as present words. -/
def decodeSlots (start : Nat) (raw : List (Option Bytes)) : Except Error (List (Option Payload)) :=
  (raw.zipIdx start).mapM fun (word, index) => decodeSlot index word

abbrev Value (policy : Policy) := Ticks policy.kind .nanosecond

/-- Read an exact page body for the given leaf and header. The caller supplies
UTC or local interpretation. The result retains mathematical nanoseconds,
including coordinates outside signed Int64. -/
def decode (policy : Policy) (leaf : Footer.SchemaElement) (codec : Int)
    (header : Parquet.Page.Header) (limits : ScalarPage.Limits) (body : Bytes) :
    Except Error (List (Option (Value policy))) := do
  let params ← parameters leaf codec header
  let words ← (ScalarPage.decode (.fixedLenBytes 12) params limits body).mapError .scalar
  let slots ← decodeSlots 0 words
  return slots.map (Option.map (·.toTicks policy))

end Silmaril.Formats.Parquet.Int96.Page
