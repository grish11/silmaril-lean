module

public import Silmaril.Formats.Arrow.DateValues.Defs

/-! # Checked binding of one Arrow IPC DATE field to a record body -/

@[expose] public section

namespace Silmaril.Formats.Arrow.DateBatch

inductive FieldTypeError where
  | primitive (actual : Arrow.FieldType)
  | unsupported (actual : SchemaReader.FieldType)
  deriving DecidableEq, Repr

/-- Admit DATE from the normalized Schema type. Other normalized logical types
remain outside DATE decoding even as the schema reader learns about them. -/
def selectDateUnit (kind : SchemaReader.FieldType) : Except FieldTypeError SchemaReader.DateUnit :=
  if let .date unit := kind then .ok unit
  else if let .primitive primitive := kind then .error (.primitive primitive)
  else .error (.unsupported kind)

inductive Error where
  | schemaMetadata (cause : Arrow.Error)
  | fieldCount (actual : Nat)
  | fieldType (actual : Arrow.FieldType)
  | unsupportedFieldType (actual : SchemaReader.FieldType)
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
  let unit ← (selectDateUnit field.type).mapError fun
    | .primitive kind => .fieldType kind
    | .unsupported kind => .unsupportedFieldType kind
  let message ← (Arrow.readMessage limits recordMetadata).mapError .recordMetadata
  let .recordBatch batch := message.header | .error .expectedRecordBatch
  if message.bodyLength ≠ body.len then .error (.bodyLength message.bodyLength body.len)
  else if body.len % 8 ≠ 0 then .error (.unalignedBodyLength body.len)
  else
    (DateValues.decodeBatch limits (dateDecoder unit)
      (descriptor schema.endianness unit field.nullable) batch body).mapError .values

end Silmaril.Formats.Arrow.DateBatch
