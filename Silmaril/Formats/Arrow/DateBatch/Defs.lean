module

public import Silmaril.Formats.Arrow.DateValues.Defs

/-! # Checked binding of one Arrow IPC DATE field to a record body -/

@[expose] public section

namespace Silmaril.Formats.Arrow.DateBatch

inductive Error where
  | schemaMetadata (cause : Arrow.Error)
  | fieldCount (actual : Nat)
  | fieldType (actual : Arrow.FieldType)
  | recordMetadata (cause : Arrow.Error)
  | expectedRecordBatch
  | bodyLength (declared actual : Nat)
  | unalignedBodyLength (actual : Nat)
  | values (cause : DateValues.Error)
  deriving DecidableEq, Repr

def dateDecoder : SchemaReader.DateUnit → DateValues.Unit
  | .day => .day
  | .millisecond => .millisecond

/-- DATE's union tag is 8 in Schema.fbs. Only the Schema supplies the unit,
byte order and nullability. -/
def descriptor (endian : SchemaReader.Endianness) (unit : SchemaReader.DateUnit)
    (nullable : Bool) : DateValues.Descriptor :=
  ⟨8, unit.code, endian.code, nullable⟩

/-- Accept padded Schema and RecordBatch message metadata and the corresponding
body slice. The caller supplies the message pairing. -/
def decode (limits : Limits) (schemaMetadata recordMetadata body : KBytes) :
    Except Error DateValues.Column := do
  let schema ← (SchemaReader.readMessage limits schemaMetadata).mapError .schemaMetadata
  let [field] := schema.fields | .error (.fieldCount schema.fields.length)
  match field.type with
  | .primitive kind => .error (.fieldType kind)
  | .date unit =>
    let message ← (Arrow.readMessage limits recordMetadata).mapError .recordMetadata
    let .recordBatch batch := message.header | .error .expectedRecordBatch
    if message.bodyLength ≠ body.len then .error (.bodyLength message.bodyLength body.len)
    else if body.len % 8 ≠ 0 then .error (.unalignedBodyLength body.len)
    else
      (DateValues.decodeBatch limits (dateDecoder unit)
        (descriptor schema.endianness unit field.nullable) batch body).mapError .values

end Silmaril.Formats.Arrow.DateBatch
