module

public import Silmaril.Semantics.SQLite.Relational.Schema.Thms
public import Silmaril.Semantics.SQLite.Relational.Table.Defs
import Silmaril.Proofs.Semantics.SQLite.Relational.Table.Checks
import Silmaril.Proofs.Semantics.SQLite.Relational.Table.Alignment

/-! Generation and checked row/column diagrams. -/

@[expose] public section

namespace Silmaril.SQLite.Relational

open Silmaril.Relational (AlignedColumns)

variable {Value Affinity Expr : Type}
variable {schema : TableSchema Affinity Expr} {model : ValueModel Value Affinity}
variable {sem : TableSemantics Value Affinity Expr}

namespace TableSchema

theorem materialize_eq_some_iff (supplied : schema.SuppliedCells model) (cells : schema.Cells model) :
    schema.materialize model sem supplied = some cells ↔
      ∀ i, schema.fill model sem supplied i = some (cells i) :=
  Proofs.SQLite.Relational.materialize_eq_some_iff supplied cells

theorem generationValid_iff (cells : schema.Cells model) :
    schema.GenerationValid model sem cells ↔
      (schema.generatedColumns model sem).Valid (fun j => some (cells j.val),
        fun j => some (cells j.val.1)) :=
  Proofs.SQLite.Relational.generationValid_iff cells

theorem materialize_supplied (supplied : schema.SuppliedCells model) (cells : schema.Cells model)
    (materialized : schema.materialize model sem supplied = some cells) :
    (fun j : schema.Supplied => cells j.val) = supplied :=
  Proofs.SQLite.Relational.materialize_supplied supplied cells materialized

@[simp] theorem materialize_restrict_iff (cells : schema.Cells model) :
    schema.materialize model sem (fun j => cells j.val) = some cells ↔
      schema.GenerationValid model sem cells :=
  materialize_eq_some_iff _ _

theorem generationValid_of_materialize {supplied : schema.SuppliedCells model} {cells : schema.Cells model}
    (h : schema.materialize model sem supplied = some cells) : schema.GenerationValid model sem cells :=
  (materialize_restrict_iff cells).mp ((materialize_supplied supplied cells h).symm ▸ h)

end TableSchema

namespace CheckedTable

/-- Transport table checks through Track C alignment, retaining row identities. -/
def rowsEquivColumns : CheckedTable model sem schema ≃ CheckedColumns model sem schema where
  toFun table := ⟨AlignedColumns.ofRows table.rows, by simpa [rows] using table.property⟩
  invFun columns := ⟨columns.val.toRows, columns.property⟩
  left_inv table := Subtype.ext (AlignedColumns.toRows_ofRows table.rows)
  right_inv columns := Subtype.ext (AlignedColumns.ofRows_toRows columns.val)

@[simp] theorem rowsEquivColumns_val (table : CheckedTable model sem schema) :
    (rowsEquivColumns table).val = AlignedColumns.rowsEquiv table.rows := rfl

@[simp] theorem rowsEquivColumns_column (table : CheckedTable model sem schema) (i : schema.Index) :
    (rowsEquivColumns table).val.values (some i) = table.column i := rfl

@[simp] theorem rowsEquivColumns_rowIds (table : CheckedTable model sem schema) :
    (rowsEquivColumns table).val.values none = table.rows.map TableRow.rowId := rfl

theorem rowsEquivColumns_check (table : CheckedTable model sem schema) :
    schema.TableValid model sem (rowsEquivColumns table).val.toRows :=
  (rowsEquivColumns table).property

theorem row_reconstruct (table : CheckedTable model sem schema) (row : TableRow model schema)
    (mem : row ∈ table.rows) :
    schema.materialize model sem (fun j => row.cell j.val) = some row.cell :=
  (schema.materialize_restrict_iff row.cell).mpr (table.property.1 row mem).1

theorem check_transpose (rows : List (TableRow model schema))
    [Decidable (schema.TableValid model sem rows)]
    [Decidable (schema.TableValid model sem (AlignedColumns.ofRows rows).toRows)] :
    (check (sem := sem) rows).map rowsEquivColumns =
      CheckedColumns.check (sem := sem) (AlignedColumns.ofRows rows) :=
  Proofs.SQLite.Relational.check_transpose rows rowsEquivColumns (fun _ => rfl)

@[simp] theorem check_eq_none_iff (rows : List (TableRow model schema))
    [Decidable (schema.TableValid model sem rows)] :
    check (sem := sem) rows = none ↔ ¬ schema.TableValid model sem rows := by
  by_cases valid : schema.TableValid model sem rows <;> simp [check, valid]

@[simp] theorem check_eq_some_iff (rows : List (TableRow model schema))
    [Decidable (schema.TableValid model sem rows)] (table : CheckedTable model sem schema) :
    check rows = some table ↔ rows = table.rows := by
  by_cases valid : schema.TableValid model sem rows
  · simp [check, CheckedTable.rows, valid, Subtype.ext_iff]
  · simp [check, valid]
    intro eq
    exact valid (eq ▸ table.property)

end CheckedTable

end Silmaril.SQLite.Relational
