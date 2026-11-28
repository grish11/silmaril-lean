module

public import Silmaril.Formats.Relational.NamedTable.Date32.Defs
public import Silmaril.Formats.Parquet.Date.FromIpc.Defs

/-! # Export one selected column of a named Date32 table to native Parquet DATE -/

@[expose] public section

namespace Silmaril.Formats.Relational.NamedTable.Date32.Export

open Silmaril.Relational Silmaril.Formats.Parquet

structure Column where
  index : Nat
  field : String
  nullable : Bool

structure Limits where
  maxRows : Nat
  writer : FlatInt32Writer.Limits
  readback : Date.Limits

inductive Error where
  | missingName
  | columnIndex (index width : Nat)
  | fieldMismatch (actual : String)
  | kindMismatch (actual : Date.Events.Kind)
  | rowLimit (actual limit : Nat)
  | write (cause : Date.FromIpc.Error)
  deriving DecidableEq, Repr

/-- Check the exact named entry and selected positional descriptor, then
bound its row count before projecting that column in stored row order. -/
def select {Name : Type*} (db : Database Name) (name : Name)
    (column : Column) (maxRows : Nat) : Except Error (List Slot) :=
  match Scan.observePacked db name with
  | none => .error .missingName
  | some table =>
    if within : column.index < table.schema.width then
      let index : Fin table.schema.width := ⟨column.index, within⟩
      let actual := table.schema.kind index
      if actual.1 ≠ column.field then .error (.fieldMismatch actual.1)
      else if actual.2 ≠ .date32 column.nullable then .error (.kindMismatch actual.2)
      else if table.rowCount > maxRows then .error (.rowLimit table.rowCount maxRows)
      else .ok (table.rows.map (· index))
    else .error (.columnIndex column.index table.schema.width)

/-- Emit one checked DATE group from the selected ordered slots, including
an explicit zero-row group for an empty named table. -/
def convert {Name : Type*} (db : Database Name) (name : Name) (column : Column)
    (limits : Limits) : Except Error Bytes := do
  let slots ← select db name column limits.maxRows
  (Date.FromIpc.emitGroup limits.writer limits.readback column.field column.nullable
    (slots.map (Option.map DateInterop.Date32.toCivil))).mapError .write

end Silmaril.Formats.Relational.NamedTable.Date32.Export
