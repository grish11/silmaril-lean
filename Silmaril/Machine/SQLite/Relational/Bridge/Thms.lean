module

public import Silmaril.Machine.SQLite.Relational.Bridge.Defs
import Silmaril.Proofs.Machine.SQLite.Relational.Bridge.Correspondence

public section

namespace Silmaril.SQLite.Relational.Bridge

open Silmaril.Machine.SQLite.TrackA
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SQLite.TrackA.Read.Adapter (Returns pagerTree stagedCall handlePager
  handleVfs Observes pagerTwice)
open Silmaril.Machine.SQLite.TrackA.Read.Interaction (vfsTree)
open CatalogExecutor (Names Target)

variable {Expr Backing : Type} {sem : TableSemantics SqlValue Affinity Expr}

/-- A bound D invocation agrees with both handled Track A interpretations on
its result and complete poststate, including on a defined read failure. -/
theorem execute_corresponds (backing : Handler Backing) (locate : Locate sem)
    (db : Connection (profile sem Backing)) (call : Invocation Names)
    (plan : Plan (Target sem)) (key : Int64) (bound : Bound db call plan key) :
    let request := locate plan.target
    let observed := Read.runStaged backing db.backing db.cache request.target request.page key
    let tree := vfsTree db.cache request.target request.page key
    let out := (executor backing locate).execute db call
    (executor backing locate).prepare db call.statement = .ok ⟨plan, none⟩ ∧
    execute backing locate db call = CheckedOutcome.ofStatement out ∧
    Corresponds db plan observed out ∧
    Returns (pagerTree (stagedCall request key)) (handlePager backing)
      (db.backing, db.cache, []) (observed.file, observed.cache, observed.exchanges)
      (observed.result, observed.cache) ∧
    Returns tree (handleVfs backing) (db.backing, [])
      (observed.file, observed.exchanges) (observed.result, observed.cache) ∧
    Trace.Valid backing db.backing observed.exchanges observed.file ∧ Observes tree observed :=
  Proofs.Machine.SQLite.Relational.Bridge.execute_corresponds backing locate db call plan key bound

/-- The same admitted point read twice uses one VFS exchange and retains the
installed slot in both statement poststates. The point result also satisfies
D3's catalog-only reference after erasing the storage observations. -/
theorem execute_cold_warm (capacity : Nat) (locate : Locate sem)
    (db : Connection (profile sem FileState)) (call : Invocation Names)
    (plan : Plan (Target sem)) (key : Int64) (table : Formats.Sqlite.Vdbe.Table)
    (bound : Bound db call plan key) (leaf : ColdLeaf db (locate plan.target) table)
    (agrees : Projected plan.target table key) :
    let request := locate plan.target
    let backing := readOnly capacity
    ∃ bytes cell,
      let result : SelectResult SqlValue := ⟨plan.label, cell⟩
      let suffix : Trace := [⟨request.page.request, .ok bytes⟩]
      let resident := db.cache.install request.target request.page bytes
      let after := { db with cache := resident, exchanges := db.exchanges ++ suffix }
      plan.target.Matches key cell ∧
      (CatalogExecutor.reference sem).Executes (forgetStorage db) call (.ok result)
        (forgetStorage after) ∧
      (executor backing locate).executeBatch db [call, call] =
        (⟨[(result, after), (result, after)], none⟩, after) ∧
      Returns (pagerTwice (stagedCall request key)) (handlePager backing)
        (db.backing, db.cache, db.exchanges) (after.backing, after.cache, after.exchanges)
        ((.ok (Read.lookupValue table key), resident), (.ok (Read.lookupValue table key), resident)) ∧
      Trace.Valid backing db.backing suffix after.backing :=
  Proofs.Machine.SQLite.Relational.Bridge.execute_cold_warm capacity locate db call plan key table bound leaf agrees

end Silmaril.SQLite.Relational.Bridge
