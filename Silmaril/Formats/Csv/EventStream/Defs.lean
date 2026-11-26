module

public import Silmaril.Formats.Csv.NamedTable.Utf8.Defs

/-! # Typed batch events through a named table to UTF-8 CSV -/

@[expose] public section

namespace Silmaril.Formats.Csv.EventStream

open Silmaril.Formats.Arrow
open Silmaril.Formats.Parquet
open Silmaril.Formats.Relational.NamedTable (Packed ImportError importCollected)

inductive Error (SourceError : Type*) where
  | input (error : ImportError SourceError)
  | output (error : NamedTable.ExportError)
  deriving DecidableEq

/-- The inserted database and exported schema and bytes are returned together. -/
structure Result (Name : Type*) {Kind : Type*} (Value : Kind → Type*) where
  db : Packed Name Field Value
  schema : Typed.Schema Kind
  wire : Bytes

variable {Name Kind SourceError Group : Type*} {Value : Kind → Type*}

/-- Insert only at the exact schema after EOS. Export succeeds before the
updated database and CSV bytes are returned to the caller. -/
def convertCollected [DecidableEq Name] [DecidableEq Kind] (db : Packed Name Field Value)
    (name : Name) (expected : Typed.Schema Kind) (codecs : (kind : Kind) → Typed.CellCodec (Value kind))
    (collected : Except SourceError (Events.Observation Field Value SourceError)) :
    Except (Error SourceError) (Result Name Value) :=
  match importCollected db name expected collected with
  | .error error => .error (.input error)
  | .ok loaded =>
    match NamedTable.Utf8.exportCsv loaded name codecs with
    | .error error => .error (.output error)
    | .ok (schema, wire) => .ok ⟨loaded, schema, wire⟩

/-- Collect typed events in batch order before attempting named insertion and export. -/
def convert [DecidableEq Name] [DecidableEq Kind] (db : Packed Name Field Value)
    (name : Name) (expected : Typed.Schema Kind) (codecs : (kind : Kind) → Typed.CellCodec (Value kind))
    (stream : Events.EventStream Field Value SourceError) :
    Except (Error SourceError) (Result Name Value) :=
  convertCollected db name expected codecs stream.collect

/-- Consume the existing typed Parquet row-group source to completion. -/
def convertParquet [DecidableEq Name] [DecidableEq Kind] (db : Packed Name Field Value)
    (name : Name) (expected : Typed.Schema Kind) (codecs : (kind : Kind) → Typed.CellCodec (Value kind))
    (opened : Reader.OpenResult Group Field Value SourceError) :
    Except (Error SourceError) (Result Name Value) :=
  convert db name expected codecs (Reader.readAll opened)

end Silmaril.Formats.Csv.EventStream
