module

public import Silmaril.Formats.Parquet.FlatInt32Writer.Defs
public import Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv.Defs

/-! Checked typed UTF-8 CSV to a named INT32 table and a complete Parquet file. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Relational.NamedTable (Packed ImportError importCollected)
open Silmaril.Formats.Parquet.Snapshot.FlatInt32 (Cell)
open Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv (csvSchema codecs)

structure CsvLimits where
  maxBytes : Nat
  maxRows : Nat
  maxColumns : Nat

inductive Error where
  | csvByteLimit
  | csvRowLimit
  | csvColumnLimit
  | csv (reason : Csv.Typed.Error)
  | destination (reason : ImportError Csv.Typed.Error)
  | parquet (reason : FlatInt32Writer.Error)
  deriving DecidableEq

structure Result (Name : Type*) where
  db : Packed Name Csv.Field Cell
  bytes : Bytes

/-- Bound the wire extent and declared width before decoding. Then check the
number of decoded data rows. The schema and nullable tags are explicit. -/
def readCsv (limits : CsvLimits) (schema : Scan.Schema String Unit) (wire : Csv.Bytes) :
    Except Error (Csv.Typed.Table (csvSchema schema) Cell) :=
  if limits.maxBytes < wire.length then .error .csvByteLimit
  else if limits.maxColumns < schema.width then .error .csvColumnLimit
  else
    match Csv.Typed.Utf8.decode (csvSchema schema) codecs wire with
    | .error reason => .error (.csv reason)
    | .ok rows =>
      if limits.maxRows < rows.length then .error .csvRowLimit else .ok rows

/-- Transpose the typed row observation into writer columns in schema order.
Every field is OPTIONAL, so present and null slots retain their positions. -/
def writerInput (schema : Scan.Schema String Unit) (rows : Csv.Typed.Table (csvSchema schema) Cell) :
    FlatInt32Writer.Input :=
  ⟨rows.length, List.ofFn fun i => ⟨(schema.kind i).1, .optional (rows.map (· i))⟩⟩

/-- Return the exact named insertion and complete Parquet bytes together.
An occupied name takes precedence; other failures return only their error. -/
def convert {Name : Type*} [DecidableEq Name] (db : Packed Name Csv.Field Cell) (name : Name)
    (schema : Scan.Schema String Unit) (csvLimits : CsvLimits) (parquetLimits : FlatInt32Writer.Limits)
    (wire : Csv.Bytes) : Except Error (Result Name) :=
  if (db name).isSome then .error (.destination .nameConflict)
  else
    match readCsv csvLimits schema wire with
    | .error reason => .error reason
    | .ok rows =>
      match importCollected (Error := Csv.Typed.Error) db name (csvSchema schema)
          (.ok ⟨⟨csvSchema schema, rows⟩, .eos⟩) with
      | .error reason => .error (.destination reason)
      | .ok inserted =>
        match FlatInt32Writer.emit parquetLimits (writerInput schema rows) with
        | .error reason => .error (.parquet reason)
        | .ok encoded => .ok ⟨inserted, encoded.bytes⟩

end Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv
