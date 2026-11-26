module

public import Silmaril.Formats.Arrow.TimestampStream.ToCsv.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Defs

/-! Write one checked TIMESTAMP RecordBatch after a supplied V5 Schema frame. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.TimestampStream.FromCsv

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (ConversionError Ticks)
open ToCsv (Cell CsvLimits Kind codecs schemaOf)
open Silmaril.Formats.Relational.NamedTable (Packed ImportError importCollected schemaMatches)

inductive Error where
  | nameConflict
  | csvByteLimit
  | csvRowLimit
  | schema (reason : TimestampStream.Error)
  | schemaExtent (expected actual : Nat)
  | schemaMismatch
  | csv (reason : Csv.Typed.Error)
  | requiredNull
  | payload (reason : ConversionError)
  | writer (reason : Arrow.Error)
  | readback (reason : TimestampStream.Error)
  | readbackMismatch
  | destination (reason : ImportError Csv.Typed.Error)
  deriving DecidableEq

structure Result (Name : Type*) where
  db : Packed Name Csv.Field Cell
  wire : KBytes

/-- Accept exactly one complete Schema frame matching the declaration.
Schema matching preserves the timezone option itself. -/
def checkSchema (limits : Arrow.Limits) (declared : Csv.Typed.Schema Kind) (frame : KBytes) :
    Except Error TimestampBatch.Binding := do
  if !frame.wf then throw (.schema .source)
  let (binding, next) ← (TimestampStream.readSchema limits frame).mapError .schema
  if next ≠ frame.len then throw (.schemaExtent next frame.len)
  if !schemaMatches declared (schemaOf binding) then throw .schemaMismatch
  return binding

/-- Bound the CSV extent before decoding and the row count before frame emission. -/
def prepare (ipc : Arrow.Limits) (csv : CsvLimits) (declared : Csv.Typed.Schema Kind)
    (frame : KBytes) (wire : Csv.Bytes) :
    Except Error (Σ binding : TimestampBatch.Binding, Csv.Typed.Table (schemaOf binding) Cell) := do
  if csv.maxBytes < wire.length then throw .csvByteLimit
  let binding ← checkSchema ipc declared frame
  let rows ← (Csv.Typed.Utf8.decode (schemaOf binding) codecs wire).mapError .csv
  if csv.maxRows < rows.length then throw .csvRowLimit
  return ⟨binding, rows⟩

def slotsOf (binding : TimestampBatch.Binding) (rows : Csv.Typed.Table (schemaOf binding) Cell) :
    TimestampBatch.Column binding :=
  rows.map fun row => row ⟨0, by simp [schemaOf]⟩

def tickCounts {binding : TimestampBatch.Binding} (column : TimestampBatch.Column binding) :
    List (Option Int) :=
  column.map (Option.map Ticks.ticks)

/-- Pack validity and same-unit Int64 values as a single aligned record.
A null slot has a zero physical word and a clear validity bit. -/
def emitRecord (limits : Arrow.Limits) (binding : TimestampBatch.Binding)
    (slots : TimestampBatch.Column binding) : Except Error KBytes := do
  if limits.batches = 0 then throw (.writer (.limit .batches))
  if limits.rows < slots.length then throw (.writer (.limit .rows))
  if !binding.nullable && slots.any Option.isNone then throw .requiredNull
  let validitySize := (slots.length + 7) / 8
  if limits.bodyBytes < validitySize + Writer.padding validitySize + 8 * slots.length then
    throw (.writer (.limit .bodyBytes))
  let values ← (binding.metadata.encodeBufferLE (slots.map (·.getD ⟨0⟩))).mapError .payload
  let payload := Writer.emitWords 1 (values.data.toList.map UInt8.toNat)
  let (buffers, body) := Writer.packBuffers 0 [Writer.emitBitmap slots, payload]
  let node : FieldNode := ⟨slots.length, slots.countP Option.isNone⟩
  let message : Message := ⟨.recordBatch ⟨slots.length, [node], buffers⟩, body.len⟩
  (StreamWriter.emitFrame limits message body).mapError .writer

/-- Certify the complete byte stream with the existing TIMESTAMP reader. -/
def certify (limits : Arrow.Limits) (binding : TimestampBatch.Binding)
    (slots : TimestampBatch.Column binding) (wire : KBytes) : Except Error Unit := do
  let stream ← (TimestampStream.read limits wire).mapError .readback
  if schemaMatches (schemaOf binding) (schemaOf stream.binding) &&
      decide (stream.batches.map tickCounts = [tickCounts slots]) then return ()
  else throw .readbackMismatch

def emit (limits : Arrow.Limits) (binding : TimestampBatch.Binding) (frame : KBytes)
    (slots : TimestampBatch.Column binding) : Except Error KBytes := do
  let record ← emitRecord limits binding slots
  let wire := frame ++ record ++ StreamWriter.eos
  certify limits binding slots wire
  return wire

/-- Return the exact named update and complete IPC bytes after checked emission. -/
def convert {Name : Type*} [DecidableEq Name] (db : Packed Name Csv.Field Cell) (name : Name)
    (ipc : Arrow.Limits) (csv : CsvLimits) (declared : Csv.Typed.Schema Kind)
    (frame : KBytes) (wire : Csv.Bytes) : Except Error (Result Name) :=
  if (db name).isSome then .error .nameConflict
  else
    match prepare ipc csv declared frame wire with
    | .error reason => .error reason
    | .ok ⟨binding, rows⟩ =>
      match emit ipc binding frame (slotsOf binding rows) with
      | .error reason => .error reason
      | .ok emitted =>
        let schema := schemaOf binding
        match importCollected (Error := Csv.Typed.Error) db name schema
            (.ok ⟨⟨schema, rows⟩, .eos⟩) with
        | .error reason => .error (.destination reason)
        | .ok inserted => .ok ⟨inserted, emitted⟩

end Silmaril.Formats.Arrow.TimestampStream.FromCsv
