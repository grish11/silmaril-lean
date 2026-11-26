module

public import Silmaril.Semantics.SQLite.Relational.Table.Defs

public section

namespace Silmaril.Proofs.SQLite.Relational

open Silmaril.Relational (AlignedColumns)
open Silmaril.SQLite.Relational

variable {Value Affinity Expr : Type}
variable {schema : TableSchema Affinity Expr} {model : ValueModel Value Affinity}
variable {sem : TableSemantics Value Affinity Expr}

theorem check_transpose (rows : List (TableRow model schema))
    [Decidable (schema.TableValid model sem rows)]
    [Decidable (schema.TableValid model sem (AlignedColumns.ofRows rows).toRows)]
    (transpose : CheckedTable model sem schema → CheckedColumns model sem schema)
    (aligned : ∀ table, (transpose table).val = AlignedColumns.ofRows table.rows) :
    (CheckedTable.check (sem := sem) rows).map transpose =
      CheckedColumns.check (sem := sem) (AlignedColumns.ofRows rows) := by
  have valid : schema.TableValid model sem (AlignedColumns.ofRows rows).toRows ↔
      schema.TableValid model sem rows := by rw [AlignedColumns.toRows_ofRows]
  by_cases h : schema.TableValid model sem rows
  · simp only [CheckedTable.check, CheckedColumns.check, dite_eq_left h, dite_eq_left (valid.mpr h),
      Option.map_some, Option.some.injEq]
    exact Subtype.ext (aligned ⟨rows, h⟩)
  · simp only [CheckedTable.check, CheckedColumns.check, dite_eq_right h,
      dite_eq_right (fun hc => h (valid.mp hc)), Option.map_none]

end Silmaril.Proofs.SQLite.Relational
