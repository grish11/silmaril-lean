module

public import Silmaril.Formats.Arrow.ToCsv.Defs
public import Silmaril.Formats.Arrow.Writer.Defs

/-! Checked adaptation of typed CSV and named nullable rows to one physical Arrow batch. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.FromCsv

open Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable (Packed schemaMatches)
open ToCsv (Kind Cell schemaOf codecs)

inductive AdapterError where
  | csv (error : Csv.Typed.Error)
  | missingName
  | schemaMismatch
  | requiredNull
  deriving DecidableEq

def columnValues : (kind : Kind) → List (Option (Cell kind)) → Writer.ColumnValues
  | (.int32, _), cells => .int32 cells
  | (.utf8, _), cells => .utf8 cells

/-- Use the existing aligned transpose. The schema check makes the declared field
list and the typed positions the same size and order before they are zipped. -/
def ofObservation (fields : List Field) (table : Scan.Observation Csv.Field Cell) :
    Except AdapterError Writer.BatchInput :=
  if schemaMatches (schemaOf fields) table.schema then
    let aligned : Scan.Columns table.schema Cell := AlignedColumns.ofRows table.rows
    let values := List.ofFn fun i => columnValues (table.schema.kind i).2 (aligned.values i)
    let columns := List.zipWith
      (fun (field : Field) values => (⟨field.name, field.nullable, values⟩ : Writer.NamedColumn))
      fields values
    if columns.any (fun column => !column.nullable && column.values.nullCount != 0) then
      .error .requiredNull
    else .ok ⟨aligned.rowCount, columns⟩
  else .error .schemaMismatch

/-- Adapt a table already indexed by the schema of the declared Arrow fields. -/
def ofRows (fields : List Field) (rows : Scan.Table (schemaOf fields) Cell) :
    Except AdapterError Writer.BatchInput :=
  ofObservation fields ⟨schemaOf fields, rows⟩

/-- Decode the ordered header and tagged cells using the declared Arrow fields. -/
def ofCsv (fields : List Field) (wire : Csv.Bytes) : Except AdapterError Writer.BatchInput := do
  let rows ← (Csv.Typed.decode (schemaOf fields) codecs wire).mapError AdapterError.csv
  ofRows fields rows

/-- Observe the exact database key and check the stored schema against the declaration. -/
def ofNamed {Name : Type} (db : Packed Name Csv.Field Cell) (name : Name) (fields : List Field) :
    Except AdapterError Writer.BatchInput :=
  match Scan.observePacked db name with
  | none => .error .missingName
  | some table => ofObservation fields table

end Silmaril.Formats.Arrow.FromCsv
