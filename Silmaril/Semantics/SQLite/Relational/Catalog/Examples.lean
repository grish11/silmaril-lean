module

public import Silmaril.Semantics.SQLite.Relational.Catalog.Thms

/-! Generic witnesses for row-only erasure. No value implementation is assumed. -/

namespace Silmaril.SQLite.Relational

variable {Value Affinity Expr : Type}
variable (model : ValueModel Value Affinity) (sem : TableSemantics Value Affinity Expr)

private def anyColumn : (mode : TypingMode) → Column Affinity mode
  | .dynamic => {name := "data", type := .dynamicAny}
  | .strict => {name := "data", type := .strict .any}

private def anySchema (mode : TypingMode) : TableSchema Affinity Expr where
  mode := mode
  width := 1
  column _ := anyColumn mode
  uniqueNames := by intro first second _; exact Subsingleton.elim first second
  organization := .rowid none
  generation _ := none
  suppliedExists := ⟨0, rfl⟩
  inputsSupplied := by simp
  primaryKeySupplied := by simp
  organizationKey := trivial

private def singleton {mode : TypingMode} (table : CheckedTable model sem (anySchema (Expr := Expr) mode)) :
    PackedDatabase model sem :=
  fun name => if name = "example" then some ⟨anySchema mode, table⟩ else none

-- The dynamic and STRICT catalogs differ even when the table name and row list agree.
example :
    singleton model sem (mode := .dynamic) CheckedTable.empty ≠
      singleton model sem (mode := .strict) CheckedTable.empty := by
  intro dbEq
  have found := congrFun dbEq "example"
  have modeEq := congrArg (Option.map fun (entry : Sigma (CheckedTable model sem)) => entry.fst.mode) found
  cases modeEq

example :
    eraseDatabase (singleton model sem (mode := .dynamic) CheckedTable.empty) =
      eraseDatabase (singleton model sem (mode := .strict) CheckedTable.empty) := by
  funext name
  by_cases named : name = "example" <;>
    simp [eraseDatabase, Silmaril.Relational.Database.Packed.erase,
      Silmaril.Relational.Database.Partial.map, singleton, named, CheckedTable.values,
      CheckedTable.eraseRows, CheckedTable.rows, CheckedTable.empty]

-- Absence and presence with an empty row list have different observations.
example :
    (eraseDatabase (singleton model sem (mode := .dynamic) CheckedTable.empty) "missing",
      eraseDatabase (singleton model sem (mode := .dynamic) CheckedTable.empty) "example") =
      (none, some []) := rfl

private def anyRow (id : Int64) (value : Value) :
    TableRow model (anySchema (Affinity := Affinity) (Expr := Expr) .dynamic) :=
  TableRow.ofCells id (fun _ => ⟨value, rfl⟩)

private def oneRow (id : Int64) (value : Value) :
    CheckedTable model sem (anySchema (Expr := Expr) .dynamic) :=
  ⟨[anyRow (Expr := Expr) model id value], by
    simp [TableSchema.TableValid, TableSchema.GenerationValid, TableSchema.fill, TableSchema.rowChecks,
      TableSchema.requiresPrimaryKeyNotNull, anyRow, anySchema, anyColumn]⟩

-- Even with the schema fixed and a useful row present, dropping the ROWID is lossy.
example (value : Value) :
    oneRow model sem 1 value ≠ oneRow model sem 2 value ∧
      (oneRow model sem 1 value).values = (oneRow model sem 2 value).values := by
  refine ⟨fun eq => ?_, rfl⟩
  have ids := congrArg (fun table => table.rows.map TableRow.rowId) eq
  have impossible : ([1] : List Int64) = [2] := ids
  exact (by decide : ([1] : List Int64) ≠ [2]) impossible

end Silmaril.SQLite.Relational
