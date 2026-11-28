module

public import Silmaril.Formats.Parquet.PlainV1Writer.Defs

/-! One flat, uncompressed PLAIN BYTE_ARRAY V1 data page. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.PlainByteArrayV1Writer

inductive Input where
  | required (values : List Bytes)
  | optional (slots : List (Option Bytes))

structure Limits where
  page : PlainV1Writer.Limits
  plain : Plain.ByteArray.Limits

inductive Error where
  | bodyBudget
  | headerBudget
  | headerInteger
  | header (cause : Page.HeaderError)
  | headerMismatch
  | plain (cause : Plain.Error)
  deriving DecidableEq, Repr

abbrev Encoded := PlainV1Writer.Encoded

def Input.slots : Input → List (Option Bytes)
  | .required values => values.map some
  | .optional slots => slots

def Input.values : Input → List Bytes
  | .required values => values
  | .optional slots => slots.filterMap id

def Input.numValues : Input → Nat
  | .required values => values.length
  | .optional slots => slots.length

def Input.schema : Input → FlatPage.LevelSchema
  | .required _ => ⟨0, 0⟩
  | .optional _ => ⟨0, 1⟩

def Input.definitionSize : Input → Nat
  | .required _ => 0
  | .optional slots => 2 * slots.length

def Input.bodySize (input : Input) : Nat :=
  (match input with | .required _ => 0 | .optional _ => 4 + input.definitionSize) +
    Plain.ByteArray.encodedSize input.values

/-- Bound the complete on-disk body, including the optional V1 level prefix,
before materializing any level or scalar bytes. -/
def Input.Fits (input : Input) (limits : Limits) : Prop :=
  input.numValues < Hybrid.runLimit ∧ input.numValues ≤ limits.page.scalar.levels.values ∧
    input.definitionSize ≤ limits.page.scalar.levels.bytes ∧ input.bodySize < 2 ^ 31 ∧
    input.bodySize ≤ limits.page.scalar.compressedBytes ∧ input.bodySize ≤ limits.page.scalar.uncompressedBytes

instance (input : Input) (limits : Limits) : Decidable (input.Fits limits) := by
  unfold Input.Fits
  infer_instance

def definitionOctets (mask : List Bool) : List UInt8 :=
  mask.flatMap fun present => (Hybrid.Run.repeated 1 (if present then 1 else 0)).wire 1

/-- Optional leaves carry a four-octet little-endian length and the exact
width-one hybrid runs. The scalar suffix contains only present values. -/
def Input.body (input : Input) (scalars : Bytes) : Bytes :=
  match input with
  | .required _ => scalars
  | .optional slots =>
    let levels := definitionOctets (slots.map Option.isSome)
    (Bytes.ofList (KBytes.unpack 4 levels.length ++ levels)).append scalars

def Input.parameters (input : Input) : ScalarPage.Parameters :=
  ⟨⟨input.bodySize, input.bodySize⟩, input.schema, input.numValues, Payload.Codec.uncompressed.id, 0, .v1 3 3⟩

def Input.header (input : Input) : Page.Header :=
  ⟨input.bodySize, input.bodySize, none, .dataV1 ⟨input.numValues, 0, 3, 3⟩⟩

/-- Reuse the Compact V1 header serializer and check its exact parsed extent.
The checked PLAIN encoder bounds each octet value and the whole scalar slice. -/
def emit (limits : Limits) (input : Input) : Except Error Encoded :=
  if input.Fits limits then
    match PlainV1Writer.encodeHeader input.numValues input.bodySize with
    | none => .error .headerInteger
    | some headerBytes =>
      if limits.page.headerBytes < headerBytes.length then .error .headerBudget
      else
        match Plain.ByteArray.encode limits.plain input.values with
        | .error cause => .error (.plain cause)
        | .ok scalars =>
          let page : Encoded := ⟨input.header, headerBytes, input.body scalars⟩
          match Page.readHeaderPrefix limits.page.header page.wire with
          | .error cause => .error (.header cause)
          | .ok parsed =>
            if parsed = (page.header, headerBytes.length) then .ok page else .error .headerMismatch
  else .error .bodyBudget

end Silmaril.Formats.Parquet.PlainByteArrayV1Writer
