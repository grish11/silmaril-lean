module

public import Silmaril.Formats.Arrow.MixedFlat.Writer.Defs
public import Silmaril.Formats.Arrow.MixedFlat.Stream.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Defs

/-! Checked Arrow IPC V5 streams for one Int32 and one BinaryView field. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.StreamWriter

structure Schema where
  order : MixedFlat.Writer.Order
  intName : String
  intNullable : Bool
  viewName : String
  viewNullable : Bool
  deriving DecidableEq, Repr

structure BatchInput where
  rowCount : Nat
  intValues : List (Option Int32)
  viewValues : List (Option KBytes)

def Schema.recordInput (schema : Schema) (batch : BatchInput) : MixedFlat.Writer.Input :=
  ⟨schema.order, batch.rowCount, schema.intName, schema.intNullable, batch.intValues,
    schema.viewName, schema.viewNullable, batch.viewValues⟩

def Schema.fields (schema : Schema) : List Field :=
  (schema.recordInput ⟨0, [], []⟩).fields

abbrev BatchObservation := Nat × Option (List (Field × MixedFlat.Writer.ColumnObservation))

def BatchInput.observe (schema : Schema) (batch : BatchInput) : BatchObservation :=
  (batch.rowCount, some (schema.recordInput batch).observe)

def observeBatch (batch : Stream.Batch) : BatchObservation :=
  (batch.observed.rowCount, MixedFlat.Writer.observeColumns batch.observed.columns)

namespace Wire

open MetadataWriter.Wire

def viewFieldBytes (name : String) (nullable : Bool) (kind : BinaryView.Schema.Kind) : KBytes :=
  let emptyType := words [halfwords 4 4, 0, 8, 0, 0]
  fieldFragment name nullable kind.tag emptyType

def viewField (schema : Schema) : KBytes :=
  viewFieldBytes schema.viewName schema.viewNullable .binary

def schemaMetadata (schema : Schema) : KBytes :=
  let integer := fieldBytes ⟨schema.intName, schema.intNullable, .int32⟩
  messagePrefix 1 56 0 ++ schemaPayloadOf (schema.order.pair integer (viewField schema))

def fieldSize (name : String) : Nat :=
  let size := 53 + name.utf8ByteSize
  size + Arrow.Writer.padding size

/-- After the Message prefix, the two-entry Schema field vector and its
padding occupy 32 bytes. The two field fragments follow in declared order. -/
def schemaSize (schema : Schema) : Nat :=
  80 + fieldSize schema.intName + fieldSize schema.viewName

end Wire

inductive Error where
  | ipc (cause : Arrow.Error)
  | schema (cause : Arrow.Error)
  | budget (batchIndex : Nat) (cause : Arrow.Error)
  | batch (batchIndex : Nat) (cause : MixedFlat.Writer.Error)
  | readback (cause : Stream.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

def emitSchema (ipc : Arrow.Limits) (schema : Schema) : Except Arrow.Error KBytes := do
  if ipc.fields < 2 then throw (.limit .fields)
  let size := Wire.schemaSize schema
  if size ≥ 2^31 then throw (.malformed .metadataLength)
  if size > ipc.metadataBytes then throw (.limit .metadataBytes)
  return Arrow.StreamWriter.envelopeBytes size ++ Wire.schemaMetadata schema

/-- Apply the mixed reader's running row and cell budgets before encoding
any record. A limit failure identifies the first batch exceeding the budget. -/
def checkTotals (limits : ObservationLimits) : Nat → Nat → List BatchInput → Except Error Unit
  | _, _, [] => .ok ()
  | index, before, batch :: rest => do
    let rows := before + batch.rowCount
    (Body.checkBudget limits 2 rows).mapError (.budget index)
    checkTotals limits (index + 1) rows rest

def emitRecord (limits : MixedFlat.Limits) (schema : Schema) (batch : BatchInput) (index : Nat) :
    Except Error KBytes := do
  let record ← (MixedFlat.Writer.emit limits (schema.recordInput batch)).mapError (.batch index)
  return Arrow.StreamWriter.envelopeBytes record.metadataBytes.len ++ (record.metadataBytes ++ record.body)

def serialize (limits : MixedFlat.Limits) (schema : Schema) (batches : List BatchInput) :
    Except Error KBytes := do
  let ipc := limits.observation.ipc
  if batches.length > ipc.batches then throw (.ipc (.limit .batches))
  checkTotals limits.observation 0 0 batches
  let header ← (emitSchema ipc schema).mapError .schema
  let records ← batches.zipIdx.mapM fun (batch, index) => emitRecord limits schema batch index
  return header ++ records.foldr (· ++ ·) Arrow.StreamWriter.eos

/-- Emit a complete modern stream and certify it with the exact-EOS mixed
reader. An empty batch list still writes the exact declared Schema. -/
def emit (limits : MixedFlat.Limits) (schema : Schema) (batches : List BatchInput) :
    Except Error KBytes := do
  let bytes ← serialize limits schema batches
  let decoded ← (Stream.read limits bytes).mapError .readback
  if decoded.fields = schema.fields ∧
      decoded.batches.map observeBatch = batches.map (BatchInput.observe schema) then
    return bytes
  else throw .readbackMismatch

end Silmaril.Formats.Arrow.MixedFlat.StreamWriter
