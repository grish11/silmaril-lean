module

public import Mathlib.Data.List.OfFn
public import Silmaril.Semantics.SQLite.Relational.Catalog.Defs
public import Silmaril.Semantics.SQLite.Relational.Table.Thms

public section

namespace Silmaril.Proofs.SQLite.Relational

open Silmaril.SQLite.Relational
open Silmaril.Relational.Database (Partial)

variable {Value Affinity Expr : Type}
variable {model : ValueModel Value Affinity} {sem : TableSemantics Value Affinity Expr}

private theorem rowWithValues_injective {schema : TableSchema Affinity Expr} :
    Function.Injective (TableRow.withValues (model := model) (schema := schema)) := by
  intro first second eq
  have ids := congrArg Prod.fst eq
  have cells : first.get = second.get := List.ofFn_injective (congrArg Prod.snd eq)
  funext i
  cases i with
  | none => exact ids
  | some i => exact Subtype.ext (congrFun cells i)

theorem encodeTable_injective :
    Function.Injective (fun entry : Sigma (CheckedTable model sem) => encodeTable entry.fst entry.snd) := by
  rintro ⟨firstSchema, first⟩ ⟨secondSchema, second⟩ eq
  have schemas := congrArg Sigma.fst eq
  change firstSchema = secondSchema at schemas
  subst secondSchema
  have rows := (Sigma.mk.inj eq).2
  have eqTable : first = second :=
    Subtype.ext (List.map_injective_iff.mpr rowWithValues_injective (eq_of_heq rows))
  exact congrArg (Sigma.mk firstSchema) eqTable

theorem erase_columns (db : PackedDatabase model sem) :
    Silmaril.Relational.Database.Packed.erase (fun _ columns => CheckedTable.eraseRows columns.val.toRows)
      (packedRowsEquivColumns db) = eraseDatabase db := by
  funext name
  change ((db name).map (fun entry => (⟨entry.fst, CheckedTable.rowsEquivColumns entry.snd⟩ :
    Sigma (CheckedColumns model sem)))).map (fun entry => CheckedTable.eraseRows entry.snd.val.toRows) =
      (db name).map (fun entry => entry.snd.values)
  rw [Option.map_map]
  exact congrArg (fun encode => (db name).map encode) (funext fun entry => by
    change CheckedTable.eraseRows (Silmaril.Relational.AlignedColumns.ofRows entry.snd.rows).toRows =
      entry.snd.values
    rw [Silmaril.Relational.AlignedColumns.toRows_ofRows]
    rfl)

end Silmaril.Proofs.SQLite.Relational
