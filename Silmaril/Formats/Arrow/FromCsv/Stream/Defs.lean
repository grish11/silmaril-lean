module

public import Silmaril.Formats.Arrow.FromCsv.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Defs
public import Silmaril.Formats.Csv.Typed.Utf8.Defs

/-! Emit complete, single-batch IPC streams from checked typed CSV or named rows. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.FromCsv.Stream

open Silmaril.Formats.Relational.NamedTable (Packed)
open ToCsv (Kind Cell schemaOf)

inductive EmitError where
  | adapter (error : AdapterError)
  | writer (error : Error)
  deriving DecidableEq

/-- Serialize one successfully adapted batch, retaining its explicit row count. -/
def emitAdapted (limits : ObservationLimits) (fields : List Field) :
    Except AdapterError Writer.BatchInput → Except EmitError KBytes
  | .error error => .error (.adapter error)
  | .ok input => (StreamWriter.emit limits fields [input]).mapError EmitError.writer

def emitCsv (limits : ObservationLimits) (fields : List Field) (wire : Csv.Bytes) :
    Except EmitError KBytes :=
  emitAdapted limits fields (ofCsv fields wire)

/-- Use the existing typed UTF-8 CSV decoder and feed the same row adapter. -/
def utf8Codecs : (kind : Kind) → Csv.Typed.CellCodec (Cell kind)
  | (.int32, _) => Csv.Typed.Codecs.int32
  | (.utf8, _) => Csv.Typed.Utf8.string

def ofCsvUtf8 (fields : List Field) (wire : Csv.Bytes) : Except AdapterError Writer.BatchInput := do
  let rows ← (Csv.Typed.Utf8.decode (schemaOf fields) utf8Codecs wire).mapError AdapterError.csv
  ofRows fields rows

def emitCsvUtf8 (limits : ObservationLimits) (fields : List Field) (wire : Csv.Bytes) :
    Except EmitError KBytes :=
  emitAdapted limits fields (ofCsvUtf8 fields wire)

/-- Use the existing packed observation independently of how the table was loaded. -/
def emitNamed {Name : Type} (limits : ObservationLimits) (db : Packed Name Csv.Field Cell)
    (name : Name) (fields : List Field) : Except EmitError KBytes :=
  emitAdapted limits fields (ofNamed db name fields)

end Silmaril.Formats.Arrow.FromCsv.Stream
