module

public import Silmaril.Formats.Arrow.TimestampStream.Defs
public import Silmaril.Formats.Arrow.TimestampBatch.Writer.Defs

/-! Native V5 IPC emission for a single flat TIMESTAMP field. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.TimestampStream.Writer

open Silmaril.Numeric.Timestamp (TickUnit)

inductive Error where
  | timezone (actual : Option String)
  | writer (cause : Arrow.Error)
  | record (index : Nat) (cause : TimestampBatch.Writer.Error)
  | readback (cause : TimestampStream.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

/-- Observe the exact field name, nullability, unit and annotation. -/
def descriptor (binding : TimestampBatch.Binding) : String × Bool × TickUnit × Option String :=
  (binding.name, binding.nullable, binding.metadata.unit, binding.metadata.timezone)

namespace Internal

open MetadataWriter.Wire

def unitCode : TickUnit → Nat
  | .second => 0
  | .millisecond => 1
  | .microsecond => 2
  | .nanosecond => 3

def nameFragmentSize (name : String) : Nat :=
  let size := 53 + name.utf8ByteSize
  size + Arrow.Writer.padding size

/-- The Timestamp table is at field-fragment offset 36. Its timezone slot
is at offset 44 and, when present, points past the padded name fragment. -/
def timestampType (unit : TickUnit) (zoneOffset : Option Nat) : KBytes :=
  words [halfwords 8 12, halfwords 4 (if zoneOffset.isSome then 8 else 0),
    8, unitCode unit, zoneOffset.getD 0]

def utcString : KBytes := words [3, 0x00435455]

def timestampField (binding : TimestampBatch.Binding) : KBytes :=
  let utc := binding.metadata.timezone == some "UTC"
  let zoneOffset := if utc then some (nameFragmentSize binding.name - 44) else none
  fieldFragment binding.name binding.nullable 10 (timestampType binding.metadata.unit zoneOffset) ++
    (if utc then utcString else KBytes.empty)

def schemaMetadata (binding : TimestampBatch.Binding) : KBytes :=
  messagePrefix 1 56 0 ++ schemaPayloadOf [timestampField binding]

def schemaSize (binding : TimestampBatch.Binding) : Nat :=
  72 + (nameFragmentSize binding.name + if binding.metadata.timezone == some "UTC" then 8 else 0)

def serializeSchema (limits : Limits) (binding : TimestampBatch.Binding) : Except Error KBytes := do
  if binding.metadata.timezone.isSome && binding.metadata.timezone != some "UTC" then
    throw (.timezone binding.metadata.timezone)
  if limits.fields = 0 then throw (.writer (.limit .fields))
  let size := schemaSize binding
  if size ≥ 2^31 then throw (.writer (.malformed .metadataLength))
  if size > limits.metadataBytes then throw (.writer (.limit .metadataBytes))
  return StreamWriter.envelopeBytes size ++ schemaMetadata binding

end Internal

/-- Emit a bodyless Schema frame and check the exact descriptor and extent
through the normalized TIMESTAMP schema reader. -/
def emitSchema (limits : Limits) (binding : TimestampBatch.Binding) : Except Error KBytes := do
  let frame ← Internal.serializeSchema limits binding
  let (read, next) ← (TimestampStream.readSchema limits frame).mapError .readback
  if next = frame.len ∧ descriptor read = descriptor binding then return frame
  else throw .readbackMismatch

namespace Internal

def emitRecord (limits : Limits) (binding : TimestampBatch.Binding)
    (slots : TimestampBatch.Column binding) (index : Nat) : Except Error KBytes :=
  (TimestampBatch.Writer.emitRecord limits binding slots).mapError (.record index)

def serialize (limits : ObservationLimits) (binding : TimestampBatch.Binding)
    (batches : List (TimestampBatch.Column binding)) : Except Error KBytes := do
  if batches.length > limits.ipc.batches then throw (.writer (.limit .batches))
  (Body.checkBudget limits 1 (batches.map List.length).sum).mapError .writer
  let schema ← emitSchema limits.ipc binding
  let records ← batches.zipIdx.mapM fun (slots, index) => emitRecord limits.ipc binding slots index
  return schema ++ records.foldr (· ++ ·) StreamWriter.eos

end Internal

/-- Emit the native Schema, every requested batch in order and exact EOS.
The checked reader certifies the descriptor and the nested nullable slots. -/
def emit (limits : ObservationLimits) (binding : TimestampBatch.Binding)
    (batches : List (TimestampBatch.Column binding)) : Except Error KBytes := do
  let wire ← Internal.serialize limits binding batches
  let read ← (TimestampStream.read limits.ipc wire).mapError .readback
  if descriptor read.binding = descriptor binding ∧
      read.batches.map TimestampBatch.Writer.tickCounts = batches.map TimestampBatch.Writer.tickCounts then
    return wire
  else throw .readbackMismatch

end Silmaril.Formats.Arrow.TimestampStream.Writer
