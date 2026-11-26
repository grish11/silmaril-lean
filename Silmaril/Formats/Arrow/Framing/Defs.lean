module

public import Silmaril.Prelude.Bytes.Defs

/-! Modern Arrow IPC envelopes. Metadata includes its alignment padding. The
metadata decoder supplies the body length before the body is sliced. -/

@[expose] public section

namespace Silmaril.Formats.Arrow

inductive Malformed where
  | source | alignment | truncated | continuation | metadataLength | bodyLength
  | flatbuffer | invalidUtf8 | schemaOrder | trailingBytes | batchLayout
  | validityBitmap | bodyValues | stringOffsets
  deriving DecidableEq, Repr

inductive Unsupported where
  | legacyFraming | metadataVersion (value : Nat) | messageKind (tag : Nat)
  | endianness (value : Nat) | fieldType (tag : Nat) | fieldInteger
  | dictionary | nested | customMetadata | schemaFeatures | compression
  | variadicBuffers | unknownMetadataSlots
  deriving DecidableEq, Repr

inductive Resource where
  | metadataBytes | bodyBytes | fields | rows | batches | totalRows | totalCells
  deriving DecidableEq, Repr

inductive Error where
  | malformed (reason : Malformed)
  | unsupported (reason : Unsupported)
  | limit (resource : Resource)
  deriving DecidableEq, Repr

/-- Per-message byte budgets and per-stream schema/batch budgets. -/
structure Limits where
  metadataBytes : Nat := 1024 * 1024
  bodyBytes : Nat := 64 * 1024 * 1024
  fields : Nat := 1024
  rows : Nat := 1024 * 1024
  batches : Nat := 4096
  deriving Repr

/-- The continuation marker and length word occupy eight bytes in either case. -/
inductive Envelope where
  | eos
  | metadata (byteCount : Nat)
  deriving DecidableEq, Repr

def readEnvelope (limits : Limits) (input : KBytes) (offset : Nat) :
    Except Error Envelope :=
  if offset % 8 ≠ 0 then .error (.malformed .alignment)
  else if offset + 8 > input.len then .error (.malformed .truncated)
  else
    let marker := input.read offset 4
    let size := input.read (offset + 4) 4
    if marker ≠ 0xffffffff then
      if 0 < marker ∧ marker < 2^31 then .error (.unsupported .legacyFraming)
      else .error (.malformed .continuation)
    else if size = 0 then .ok .eos
    else if 2^31 ≤ size ∨ size % 8 ≠ 0 then .error (.malformed .metadataLength)
    else if size > limits.metadataBytes then .error (.limit .metadataBytes)
    else if offset + 8 + size > input.len then .error (.malformed .truncated)
    else .ok (.metadata size)

def readBody (limits : Limits) (input : KBytes) (offset byteCount : Nat) :
    Except Error KBytes :=
  if offset % 8 ≠ 0 then .error (.malformed .alignment)
  else if byteCount % 8 ≠ 0 then .error (.malformed .bodyLength)
  else if byteCount > limits.bodyBytes then .error (.limit .bodyBytes)
  else if offset + byteCount > input.len then .error (.malformed .truncated)
  else .ok (input.slice offset byteCount)

/-- Wire relation over octets for a modern Arrow IPC prefix and metadata span. -/
def EnvelopeWire (limits : Limits) (bytes : List UInt8) (offset : Nat) (envelope : Envelope) :
    Prop :=
  let wordAt := fun start => KBytes.leVal ((bytes.drop start).take 4)
  offset % 8 = 0 ∧ offset + 8 ≤ bytes.length ∧ wordAt offset = 0xffffffff ∧
    match envelope with
    | .eos => wordAt (offset + 4) = 0
    | .metadata size =>
      wordAt (offset + 4) = size ∧ 0 < size ∧ size < 2^31 ∧ size % 8 = 0 ∧
        size ≤ limits.metadataBytes ∧ offset + 8 + size ≤ bytes.length

end Silmaril.Formats.Arrow
