module

public import Silmaril.Semantics.SQLite.Relational.Catalog.Defs
import Silmaril.Proofs.Semantics.SQLite.Relational.Catalog.Recovery

/-! Database representation, information erasure and exact read-back. -/

@[expose] public section

namespace Silmaril.SQLite.Relational

open Silmaril.Relational.Database (Packed dependentEquivPacked)

variable {Value Affinity Expr : Type}
variable {model : ValueModel Value Affinity} {sem : TableSemantics Value Affinity Expr}

def databaseEquiv : DependentDatabase model sem ≃ PackedDatabase model sem := dependentEquivPacked

@[simp] theorem catalog_databaseEquiv (db : DependentDatabase model sem) :
    Packed.catalog (databaseEquiv db) = db.fst :=
  Silmaril.Relational.Database.catalog_pack db

@[simp] theorem catalog_packedRowsEquivColumns (db : PackedDatabase model sem) :
    Packed.catalog (packedRowsEquivColumns db) = Packed.catalog db := by
  funext name
  change ((db name).map (fun entry => (⟨entry.fst, CheckedTable.rowsEquivColumns entry.snd⟩ :
    Sigma (CheckedColumns model sem)))).map Sigma.fst = (db name).map Sigma.fst
  exact Option.map_map _ _ _

theorem erase_columns (db : PackedDatabase model sem) :
    Packed.erase (fun _ columns => CheckedTable.eraseRows columns.val.toRows)
      (packedRowsEquivColumns db) = eraseDatabase db :=
  Proofs.SQLite.Relational.erase_columns db

theorem erase_constraints (db : PackedDatabase model sem) :
    Packed.erase (fun _ rows => CheckedTable.eraseRows rows)
      (Silmaril.Relational.Database.eraseConstraints (fun (schema : TableSchema Affinity Expr) => schema.TableValid model sem) db) =
      eraseDatabase db :=
  Silmaril.Relational.Database.erase_eraseConstraints _ db _

@[simp] theorem eraseDatabase_eq_none_iff (db : PackedDatabase model sem) (name : String) :
    eraseDatabase db name = none ↔ db name = none :=
  Silmaril.Relational.Database.erase_eq_none_iff _ _ _

theorem eraseDatabase_of_present (db : PackedDatabase model sem) (name : String)
    {schema : TableSchema Affinity Expr} {table : CheckedTable model sem schema}
    (present : db name = some ⟨schema, table⟩) :
    eraseDatabase db name = some table.values :=
  congrArg (Option.map (fun (entry : Sigma (CheckedTable model sem)) => entry.snd.values)) present

theorem encodeTable_injective :
    Function.Injective (fun entry : Sigma (CheckedTable model sem) => encodeTable entry.fst entry.snd) :=
  Proofs.SQLite.Relational.encodeTable_injective

theorem recoverableKeepingIdentity (db : PackedDatabase model sem) :
    Silmaril.Relational.Database.Recoverable (encodeTable (model := model) (sem := sem)) (eraseKeepingIdentity db) :=
  Silmaril.Relational.Database.recoverable_of_injective _ db encodeTable_injective

@[simp] theorem recover_eraseKeepingIdentity (db : PackedDatabase model sem) :
    Silmaril.Relational.Database.recover encodeTable (eraseKeepingIdentity db)
      (recoverableKeepingIdentity db) = db :=
  Silmaril.Relational.Database.recover_erase _ _ _

end Silmaril.SQLite.Relational
