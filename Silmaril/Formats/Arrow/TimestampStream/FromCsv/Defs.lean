module

public import Silmaril.Formats.Arrow.TimestampStream.ToCsv.Defs
public import Silmaril.Formats.Arrow.TimestampBatch.Writer.Defs

/-! Write one checked TIMESTAMP RecordBatch after a supplied V5 Schema frame. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.TimestampStream.FromCsv

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (ConversionError)
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
  TimestampBatch.Writer.tickCounts column

/-- Use the shared TIMESTAMP record emitter while retaining the CSV adapter's
existing error payloads. -/
def emitRecord (limits : Arrow.Limits) (binding : TimestampBatch.Binding)
    (slots : TimestampBatch.Column binding) : Except Error KBytes :=
  (TimestampBatch.Writer.emitRecord limits binding slots).mapError fun
    | .writer reason => .writer reason
    | .requiredNull => .requiredNull
    | .payload reason => .payload reason

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
