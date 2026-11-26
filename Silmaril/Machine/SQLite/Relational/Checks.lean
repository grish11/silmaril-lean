module

import Silmaril.Machine.SQLite.Relational.All

/-! Consumer checks for the public entry point that includes the storage bridge. -/

open Silmaril.SQLite.Relational
open Silmaril.Machine.SQLite.TrackA
open Silmaril.Machine.SqliteVfs (FileState Handler Trace readOnly)

#check Value.toSql_ofSql
#check CatalogExecutor.execute_eq
#check Bridge.execute
#check Bridge.Bound
#check Bridge.ColdLeaf
#check Bridge.Projected
#check Read.Adapter.Observes

-- Selected open-tree membership and the file transition are distinct observations.
example {Expr Backing : Type} {sem : TableSemantics SqlValue Affinity Expr}
    (backing : Handler Backing) (locate : Bridge.Locate sem)
    (db : Connection (Bridge.profile sem Backing)) (call : Invocation CatalogExecutor.Names)
    (plan : Plan (CatalogExecutor.Target sem)) (key : Int64) (bound : Bridge.Bound db call plan key) :
    let request := locate plan.target
    let observed := Read.runStaged backing db.backing db.cache request.target request.page key
    let tree := Read.Interaction.vfsTree db.cache request.target request.page key
    Read.Adapter.Observes tree observed ∧
      Bridge.Corresponds db plan observed ((Bridge.executor backing locate).execute db call) ∧
      Trace.Valid backing db.backing observed.exchanges observed.file := by
  obtain ⟨_, _, corresponds, _, _, valid, observes⟩ :=
    Bridge.execute_corresponds backing locate db call plan key bound
  exact ⟨observes, corresponds, valid⟩

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
