module

public import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Defs
public import Silmaril.Formats.Arrow.BinaryView.Stream.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Defs

/-! Metadata and framing for one flat Arrow IPC V5 view field. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView.StreamWriter

namespace Wire

open MetadataWriter.Wire

/-- BinaryView and Utf8View both have empty type tables. -/
def schema (field : Schema.Field) : KBytes :=
  let emptyType := words [halfwords 4 4, 0, 8, 0, 0]
  messagePrefix 1 56 0 ++
    schemaPayloadOf [fieldFragment field.name field.nullable field.kind.tag emptyType]

/-- The singleton Schema vector ends at byte 72. The field fragment starts
there and includes a 53-byte prefix and terminator before padding. -/
def schemaSize (field : Schema.Field) : Nat :=
  let fragment := 53 + field.name.utf8ByteSize
  72 + fragment + Arrow.Writer.padding fragment

/-- The one-node RecordBatch uses a singleton int64 variadic count vector,
including in the zero-data case. Descriptors begin at metadata byte 128;
the int64 count follows those descriptors and the padded vector header. -/
def recordBatch (node : FieldNode) (buffers : List Buffer) (dataCount bodyLength : Nat) :
    KBytes :=
  let vtable := words [halfwords 14 32, halfwords 8 16, halfwords 20 0, halfwords 24 0]
  let table := words [16, 0] ++
    (longs [node.length] ++ words [20, 40, 44 + 16 * buffers.length, 0])
  let nodes := words [0, 1] ++ longs [node.length, node.nullCount]
  let descriptors := words [0, buffers.length] ++
    longs (buffers.flatMap fun buffer => [buffer.offset, buffer.length])
  let counts := words [0, 1] ++ longs [dataCount]
  messagePrefix 3 64 bodyLength ++ (vtable ++ (table ++ (nodes ++ (descriptors ++ counts))))

def recordBatchSize (bufferCount : Nat) : Nat := 144 + 16 * bufferCount

end Wire

inductive RecordError where
  | column (cause : Column.Writer.Error)
  | ipc (cause : Arrow.Error)
  deriving DecidableEq, Repr

inductive Error where
  | ipc (cause : Arrow.Error)
  | record (index : Nat) (cause : RecordError)
  | readback (cause : Stream.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

def checkMetadataSize (ipc : Arrow.Limits) (size : Nat) : Except Arrow.Error Unit := do
  if size ≥ 2^31 then throw (.malformed .metadataLength)
  if size > ipc.metadataBytes then throw (.limit .metadataBytes)

def emitColumn (limits : Column.Limits) (field : Schema.Field)
    (values : Schema.Values field.kind) : Except Column.Writer.Error Column.Writer.Emitted :=
  match field, values with
  | ⟨_, nullable, .binary⟩, values => Column.Writer.emitBinary limits nullable values
  | ⟨_, nullable, .utf8⟩, values => Column.Writer.emitUtf8 limits nullable values

def rowCount (kind : Schema.Kind) (values : Schema.Values kind) : Nat :=
  match kind, values with
  | .binary, values => values.length
  | .utf8, values => values.length

def emitRecord (ipc : Arrow.Limits) (limits : Column.Limits) (field : Schema.Field)
    (values : Schema.Values field.kind) : Except RecordError KBytes := do
  if rowCount field.kind values > ipc.rows then throw (.ipc (.limit .rows))
  let column ← (emitColumn limits field values).mapError .column
  let parts := column.buffers.validity :: column.buffers.payload.views :: column.buffers.payload.data.toList
  let (descriptors, body) := Arrow.Writer.packBuffers 0 parts
  if column.node.length ≥ 2^63 || body.len ≥ 2^63 then throw (.ipc (.malformed .batchLayout))
  if body.len > ipc.bodyBytes then throw (.ipc (.limit .bodyBytes))
  let size := Wire.recordBatchSize descriptors.length
  (checkMetadataSize ipc size).mapError .ipc
  let metadata := Wire.recordBatch column.node descriptors column.buffers.payload.data.size body.len
  return Arrow.StreamWriter.envelopeBytes size ++ (metadata ++ body)

def serialize (ipc : Arrow.Limits) (limits : Column.Limits) (field : Schema.Field)
    (batches : List (Schema.Values field.kind)) : Except Error KBytes := do
  if ipc.fields = 0 then throw (.ipc (.limit .fields))
  if batches.length > ipc.batches then throw (.ipc (.limit .batches))
  let size := Wire.schemaSize field
  (checkMetadataSize ipc size).mapError .ipc
  let records ← batches.zipIdx.mapM fun (values, index) =>
    (emitRecord ipc limits field values).mapError (.record index)
  let schema := Arrow.StreamWriter.envelopeBytes size ++ Wire.schema field
  return schema ++ records.foldr (· ++ ·) Arrow.StreamWriter.eos

/-- Readback observes binary octets independent of byte-tree segmentation. -/
def BatchObservation : Schema.Kind → Type
  | .binary => List (Option (List UInt8))
  | .utf8 => List (Option String)

instance (kind : Schema.Kind) : DecidableEq (BatchObservation kind) := by
  cases kind <;> unfold BatchObservation <;> infer_instance

def observe : (kind : Schema.Kind) → Schema.Values kind → BatchObservation kind
  | .binary, values => values.map (Option.map KBytes.toList)
  | .utf8, values => values

/-- Exact descriptor equality transports the decoded batches to the input
field. The outer list retains all batch boundaries, including empty batches. -/
def Agrees (field : Schema.Field) (batches : List (Schema.Values field.kind))
    (decoded : Stream.Observed) : Prop :=
  ∃ same : decoded.field = field,
    (cast (congrArg (fun f : Schema.Field => List (Schema.Values f.kind)) same)
      decoded.batches).map (observe field.kind) = batches.map (observe field.kind)

instance (field : Schema.Field) (batches : List (Schema.Values field.kind))
    (decoded : Stream.Observed) : Decidable (Agrees field batches decoded) :=
  if same : decoded.field = field then
    decidable_of_iff _ ⟨fun h => ⟨same, h⟩, fun ⟨_, h⟩ => h⟩
  else
    isFalse fun ⟨h, _⟩ => same h

/-- Emit modern V5 schema and records the existing view reader accepts.
Certify the complete wire against the supplied field and ordered values. -/
def emit (ipc : Arrow.Limits) (limits : Column.Limits) (field : Schema.Field)
    (batches : List (Schema.Values field.kind)) : Except Error KBytes := do
  let wire ← serialize ipc limits field batches
  let decoded ← (Stream.read ipc limits wire).mapError .readback
  if Agrees field batches decoded then return wire else throw .readbackMismatch

end Silmaril.Formats.Arrow.BinaryView.StreamWriter
