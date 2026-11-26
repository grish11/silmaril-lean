module

import Silmaril.Machine.SQLite.Relational.All

/-! Consumer checks for the public entry point that includes the storage bridge. -/

open Silmaril.SQLite.Relational
open Silmaril.Machine.SqliteVfs (FileState Trace readOnly)

#check Value.toSql_ofSql
#check CatalogExecutor.execute_eq
#check Bridge.execute
#check Bridge.Bound
#check Bridge.ColdLeaf
#check Bridge.Projected
#check Bridge.Corresponds
#check Bridge.execute_corresponds

-- The projected D3 equality and the full poststates come from the same admitted read pair.
example {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}
    (capacity : Nat) (locate : Bridge.Locate sem)
    (db : Connection (Bridge.profile sem FileState)) (call : Invocation CatalogExecutor.Names)
    (plan : Plan (CatalogExecutor.Target sem)) (key : Int64) (table : Silmaril.Formats.Sqlite.Vdbe.Table)
    (bound : Bridge.Bound db call plan key) (leaf : Bridge.ColdLeaf db (locate plan.target) table)
    (agrees : Bridge.Projected plan.target table key) :
    ∃ bytes cell,
      let request := locate plan.target
      let result : SelectResult SqlValue := ⟨plan.label, cell⟩
      let suffix : Trace := [⟨request.page.request, .ok bytes⟩]
      let after := { db with
        cache := db.cache.install request.target request.page bytes
        exchanges := db.exchanges ++ suffix }
      CatalogExecutor.execute sem (Bridge.forgetStorage db) call =
        (.statement (.ok result), Bridge.forgetStorage after) ∧
      (Bridge.executor (readOnly capacity) locate).executeBatch db [call, call] =
        (⟨[(result, after), (result, after)], none⟩, after) ∧
      Trace.Valid (readOnly capacity) db.backing suffix after.backing := by
  obtain ⟨bytes, cell, _, projected, batch, _, valid⟩ :=
    Bridge.execute_cold_warm capacity locate db call plan key table bound leaf agrees
  exact ⟨bytes, cell, projected, batch, valid⟩
