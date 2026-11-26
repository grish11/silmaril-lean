module

public import Silmaril.Machine.SQLite.Relational.Bridge.Defs
import Silmaril.Machine.SQLite.TrackA.Read.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.Relational.Bridge

open Silmaril.SQLite.Relational
open Silmaril.SQLite.Relational.Bridge
open Silmaril.SQLite.Relational.CatalogExecutor (Names Target)
open Silmaril.Machine.SQLite.TrackA
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SQLite.TrackA.Read.Adapter (Returns pagerTree stagedCall handlePager
  handleVfs Observes pagerTwice)
open Silmaril.Machine.SQLite.TrackA.Read.Interaction (vfsTree)

variable {Expr Backing : Type} {sem : TableSemantics SqlValue Affinity Expr}

private theorem prepare_eq (backing : Handler Backing) (locate : Locate sem)
    {db : Connection (profile sem Backing)} {call : Invocation Names}
    {plan : Plan (Target sem)} {key : Int64} (bound : Bound db call plan key) :
    (executor backing locate).prepare db call.statement = .ok ⟨plan, none⟩ := by
  simp [Executor.prepare, executor, bound.resolved]

private theorem execute_staged (backing : Handler Backing) (locate : Locate sem)
    {db : Connection (profile sem Backing)} {call : Invocation Names}
    {plan : Plan (Target sem)} {key : Int64} (bound : Bound db call plan key) :
    let request := locate plan.target
    let observed := Read.runStaged backing db.backing db.cache request.target request.page key
    (executor backing locate).execute db call = (transfer observed).finish db plan.label := by
  dsimp only
  rw [Executor.execute, prepare_eq backing locate bound, bound.binding]
  simp [Prepared.bindInt64, Executor.run, executor, Read.staged_eq_composed]

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
    Trace.Valid backing db.backing observed.exchanges observed.file ∧ Observes tree observed := by
  dsimp only
  refine ⟨prepare_eq backing locate bound, ?_, ?_, ?_⟩
  · simp [execute, bound.admitted, Executor.check]
  · rw [execute_staged backing locate bound]
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
    simp only [ReadOutcome.finish, transfer]
    split <;> rename_i equation <;> rw [equation]
  · exact Read.Adapter.interpretations_agree backing db.backing db.cache (locate plan.target) key

private theorem projected_lookup (target : Target sem) (table : Formats.Sqlite.Vdbe.Table)
    (key : Int64) (agrees : Projected target table key) :
    ∃ cell, transferResult (.ok (Read.lookupValue table key)) = .ok cell ∧
      target.Matches key cell := by
  obtain ⟨_, lookup⟩ := agrees
  unfold Read.lookupValue
  split at lookup
  · rename_i hit
    rw [hit]
    exact ⟨none, rfl, lookup⟩
  · rename_i hit
    rw [hit]
    obtain ⟨cell, decode, matching⟩ := lookup
    exact ⟨some cell, by simp [transferResult, decode, Except.map], matching⟩

private theorem cold_warm_reads (capacity : Nat) (db : Connection (profile sem FileState))
    (request : Read.Adapter.Acquire) (key : Int64) (table : Formats.Sqlite.Vdbe.Table)
    (leaf : ColdLeaf db request table) :
    let cold := Read.runStaged (readOnly capacity) db.backing db.cache request.target request.page key
    let warm := Read.runStaged (readOnly capacity) cold.file cold.cache request.target request.page key
    ∃ bytes,
      cold = ⟨.ok (Read.lookupValue table key), db.backing,
        db.cache.install request.target request.page bytes, [⟨request.page.request, .ok bytes⟩]⟩ ∧
      warm = ⟨cold.result, cold.file, cold.cache, []⟩ ∧
      Trace.Valid (readOnly capacity) db.backing (cold.exchanges ++ warm.exchanges) warm.file := by
  rcases request with ⟨target, ⟨handle, number, size⟩⟩
  rcases leaf with ⟨image, view, pageSize, snapshot, found, live, range, owned, decoded⟩
  change size = image.header.pageSize at pageSize
  subst size
  simpa only [Read.staged_eq_composed] using
    Read.readOnly_cold_warm_lookup capacity db.backing image number view handle db.cache target key
      table snapshot found live range owned decoded

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
      Trace.Valid backing db.backing suffix after.backing := by
  let request := locate plan.target
  let backing := readOnly capacity
  let cold := Read.runStaged backing db.backing db.cache request.target request.page key
  let warm := Read.runStaged backing cold.file cold.cache request.target request.page key
  obtain ⟨bytes, coldEq, warmEq, valid⟩ := cold_warm_reads capacity db request key table leaf
  change cold = _ at coldEq
  change warm = ⟨cold.result, cold.file, cold.cache, []⟩ at warmEq
  obtain ⟨cell, resultEq, matching⟩ := projected_lookup plan.target table key agrees
  let result : SelectResult SqlValue := ⟨plan.label, cell⟩
  let suffix : Trace := [⟨request.page.request, .ok bytes⟩]
  let after := { db with
    cache := db.cache.install request.target request.page bytes
    exchanges := db.exchanges ++ suffix }
  have first : (executor backing locate).execute db call = (.ok result, after) := by
    have eq := execute_staged backing locate bound
    change _ = (transfer cold).finish db plan.label at eq
    rw [coldEq] at eq
    simpa [transfer, ReadOutcome.finish, resultEq, result, after, suffix] using eq
  have nextBound : Bound after call plan key := ⟨bound.admitted, bound.resolved, bound.binding⟩
  have second : (executor backing locate).execute after call = (.ok result, after) := by
    have eq := execute_staged backing locate nextBound
    have readEq : Read.runStaged backing after.backing after.cache request.target request.page key =
        warm := by simp [warm, coldEq, after]
    change _ = (transfer (Read.runStaged backing after.backing after.cache request.target
      request.page key)).finish after plan.label at eq
    rw [readEq, warmEq, coldEq] at eq
    simpa [transfer, ReadOutcome.finish, resultEq, result, after] using eq
  refine ⟨bytes, cell, matching, ?_, ?_, ?_, ?_⟩
  · exact Reference.Executes.seek (ref := CatalogExecutor.reference sem) (plan := plan)
      (read := CatalogExecutor.readOutcome cell) bound.resolved bound.binding ⟨cell, matching, rfl⟩
  · change (executor backing locate).executeBatch db [call, call] =
      (⟨[(result, after), (result, after)], none⟩, after)
    simp only [Executor.executeBatch, first, second, BatchOutcome.prepend]
  · obtain ⟨returns, _⟩ := Read.Adapter.pagerTwice_agrees backing db.backing db.cache
      db.exchanges request key
    change Returns _ _ _ (warm.file, warm.cache, db.exchanges ++ cold.exchanges ++ warm.exchanges)
      ((cold.result, cold.cache), (warm.result, warm.cache)) at returns
    rw [warmEq, coldEq] at returns
    simpa [after, suffix] using returns
  · change Trace.Valid backing db.backing (cold.exchanges ++ warm.exchanges) warm.file at valid
    rw [warmEq, coldEq] at valid
    simpa [after, suffix] using valid

end Silmaril.Proofs.Machine.SQLite.Relational.Bridge
