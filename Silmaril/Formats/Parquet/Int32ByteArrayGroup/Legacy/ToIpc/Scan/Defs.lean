module

public import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Defs
public import Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Defs
public import Silmaril.Formats.Arrow.MixedFlat.TwoBinaryViews.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.Defs

/-! Export the completed checked legacy scan through the existing native writers. -/

public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan

open Silmaril.Relational
open Arrow.MixedFlat

abbrev Schema := Relational.Scan.Schema String Legacy.Kind
abbrev Batch (schema : Schema) := Relational.Scan.Columns schema Legacy.Value
abbrev Projection := (selected : Schema) → Relational.Scan.Projection selected
abbrev Predicate := (selected : Schema) → Relational.Scan.Predicate selected Legacy.Value

inductive Error where
  | source (cause : Legacy.Error)
  | closed
  | unsupportedProjection (fields : List (String × Legacy.Kind))
  | budget (cause : Arrow.Error)
  | primitiveWriter (cause : Arrow.Error)
  | binaryWriter (cause : Arrow.BinaryView.StreamWriter.Error)
  | mixedWriter (cause : StreamWriter.Error)
  | twoViewWriter (cause : TwoBinaryViews.Error)
  | orderedWriter (cause : OrderedWriter.Error)
  | readback (cause : Stream.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

@[expose] def field : String × Legacy.Kind → Arrow.MixedFlat.Field
  | (name, .int32 layout) => ⟨name, layout == .optional, .primitive .int32⟩
  | (name, .byteArray layout) => ⟨name, layout == .optional, .view .binary⟩

@[expose] def fields (selected : Schema) : List Arrow.MixedFlat.Field :=
  (List.ofFn selected.kind).map field

inductive Column where
  | int32 (values : List (Option Int32))
  | binary (values : List (Option Bytes))

@[expose] def Column.ofValues : (kind : Legacy.Kind) → List (Option (Legacy.Value kind)) → Column
  | .int32 _, values => .int32 values
  | .byteArray _, values => .binary values

@[expose] def column {selected : Schema} (batch : Batch selected) (i : Fin selected.width) : Column :=
  Column.ofValues (selected.kind i).2 (batch.values i)

@[expose] def Column.observe : Column → Writer.ColumnObservation
  | .int32 values => .int32 (values.map (Option.map Arrow.Value.int32))
  | .binary values => .binaryView (values.map (Option.map Bytes.toList))

/-- Row count plus nullable, ordered columns. Row count is independent of schema width. -/
@[expose] def observe {selected : Schema} (batch : Batch selected) : StreamWriter.BatchObservation :=
  (batch.rowCount, some (List.ofFn fun i => (field (selected.kind i), (column batch i).observe)))

@[expose] def binaryValues (values : List (Option Bytes)) : List (Option KBytes) :=
  values.map (Option.map fun bytes => Arrow.Writer.emitWords 1 (bytes.toList.map UInt8.toNat))

private def emitMixed (ipc : Arrow.MixedFlat.Limits) (schema : StreamWriter.Schema)
    (batches : List (Nat × List Column)) (bad : Error) : Except Error KBytes := do
  let inputs ← batches.mapM fun (count, columns) =>
    match schema.order, columns with
    | .intFirst, [.int32 integers, .binary bytes] | .viewFirst, [.binary bytes, .int32 integers] =>
      .ok (⟨count, integers, binaryValues bytes⟩ : StreamWriter.BatchInput)
    | _, _ => .error bad
  (StreamWriter.serialize ipc schema inputs).mapError .mixedWriter

private def emitBinary (ipc : Arrow.MixedFlat.Limits) (name : String) (nullable : Bool)
    (batches : List (Nat × List Column)) (bad : Error) : Except Error KBytes := do
  let inputs ← batches.mapM fun
    | (_, [.binary bytes]) => .ok (binaryValues bytes)
    | _ => .error bad
  let view := { ipc.view with dataBuffers := min ipc.view.dataBuffers ipc.totalDataBuffers }
  (Arrow.BinaryView.StreamWriter.serialize ipc.observation.ipc view ⟨name, nullable, .binary⟩
    inputs).mapError .binaryWriter

private def emitPrimitive (ipc : Arrow.MixedFlat.Limits) (selected : Schema)
    (batches : List (Batch selected)) (bad : Error) : Except Error KBytes := do
  let primitiveField : String × Legacy.Kind → Except Error Arrow.Field := fun
    | (name, .int32 layout) => .ok (⟨name, layout == .optional, .int32⟩ : Arrow.Field)
    | _ => .error bad
  let fields ← (List.ofFn selected.kind).mapM primitiveField
  let inputs ← batches.mapM fun batch => do
    let named ← (List.ofFn (fun i : Fin selected.width => i)).mapM fun i => do
      let field ← primitiveField (selected.kind i)
      let .int32 values := column batch i | throw bad
      return (⟨field.name, field.nullable, .int32 values⟩ : Arrow.Writer.NamedColumn)
    return (⟨batch.rowCount, named⟩ : Arrow.Writer.BatchInput)
  (Arrow.StreamWriter.emit ipc.observation fields inputs).mapError .primitiveWriter

@[expose] def Column.toOrdered (label : Arrow.MixedFlat.Field) : Column → OrderedWriter.Column
  | .int32 values => .int32 label.name label.nullable values
  | .binary values => .binary label.name label.nullable (binaryValues values)

/-- Prepare fields positionally, retaining repeated selections and explicit row counts. -/
@[expose] def orderedBatch {selected : Schema} (batch : Batch selected) : OrderedWriter.BatchInput :=
  ⟨batch.rowCount, List.ofFn fun index => (column batch index).toOrdered (field (selected.kind index))⟩

def serialize (ipc : Arrow.MixedFlat.Limits) (selected : Schema)
    (batches : List (Batch selected)) : Except Error KBytes := do
  if selected.width > ipc.observation.ipc.fields then throw (.budget (.limit .fields))
  if batches.length > ipc.observation.ipc.batches then throw (.budget (.limit .batches))
  (Arrow.Body.checkBudget ipc.observation selected.width (batches.map (·.rowCount)).sum).mapError .budget
  let schema := List.ofFn selected.kind
  let bad := Error.unsupportedProjection schema
  let inputs := fun () => batches.map fun batch => (batch.rowCount, List.ofFn (column batch))
  match schema with
  | [(name, .byteArray layout)] => emitBinary ipc name (layout == .optional) (inputs ()) bad
  | [(int, .int32 i), (view, .byteArray b)] =>
    emitMixed ipc ⟨.intFirst, int, i == .optional, view, b == .optional⟩ (inputs ()) bad
  | [(view, .byteArray b), (int, .int32 i)] =>
    emitMixed ipc ⟨.viewFirst, int, i == .optional, view, b == .optional⟩ (inputs ()) bad
  | _ =>
    let nativeFields := fields selected
    if nativeFields.any (·.kind.isView) then
      let writerError := if TwoBinaryViews.supported nativeFields then Error.twoViewWriter else Error.orderedWriter
      (OrderedWriter.serialize ipc nativeFields (batches.map orderedBatch)).mapError writerError
    else emitPrimitive ipc selected batches bad

/-- Certify every supported writer's output against the same ordered observation. -/
@[expose] def emit (ipc : Arrow.MixedFlat.Limits) (selected : Schema) (batches : List (Batch selected)) :
    Except Error KBytes := do
  let wire ← serialize ipc selected batches
  let decoded ← (Stream.read ipc wire).mapError .readback
  if decoded.fields = fields selected ∧ decoded.batches.map StreamWriter.observeBatch = batches.map observe then
    return wire
  else throw .readbackMismatch

/-- A carrier is available only after the checked scan has reached EOS.
The predicate sees both original cells before projection. -/
@[expose] def convert (parquet : Legacy.Limits) (ipc : Arrow.MixedFlat.Limits) (input : Bytes)
    (int32Name byteArrayName : String) (project : Projection) (keep : Predicate) : Except Error KBytes := do
  let ⟨selected, trace⟩ ← ((Legacy.readAll parquet input int32Name byteArrayName).scan project keep).mapError .source
  match trace.termination with
  | .eos => emit ipc selected trace.batches
  | .readError cause | .closeError cause => .error (.source cause)
  | .closed => .error .closed

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan
