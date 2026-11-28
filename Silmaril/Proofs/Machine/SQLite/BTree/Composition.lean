module

public import Silmaril.Machine.SQLite.BTree.Defs
import Silmaril.Machine.SQLite.VFS.Thms
import Silmaril.Machine.SQLite.TrackB.Read.Interaction.Thms
import Silmaril.Machine.SQLite.Relational.Bridge.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.BTree

open Silmaril.Formats.Sqlite
open Silmaril.Machine
open Silmaril.Machine.SQLite
open Silmaril.Machine.SQLite.TrackA
open Silmaril.Machine.SqliteVfs
open Silmaril.Semantics
open Silmaril.SQLite.Relational
open Read.Adapter (Acquire Observes Returns handlePager handleVfs pagerTree pagerTwice stagedCall)
open Read.Interaction (vfsTree)
open FileView.Admission.VdbeLeaf (btreeHeaderOffset)


theorem opened_read {maximum requested : Mode} {capacity : Nat} {uri : Bool} {name : String}
    {files openedFiles : VFS.FileMap} {opened : VFS.Opened}
    (success : VFS.openExisting maximum capacity uri requested name files = (.ok opened, openedFiles))
    (grant : Pager.LockGrant) (allowed : grant.Allows opened .readOnly)
    (cache : PageRead.Cache) (slot : PageRead.SlotId) (number size : Nat) (key : Int64) :
    let page : PageRead.Page := ⟨opened.handle, number, size⟩
    let request : Acquire := ⟨slot, page⟩
    let backing := SqliteVfs.backing maximum capacity
    ∃ file,
      Pager.ReadAccess openedFiles opened grant file page ∧
      let out := TrackB.Read.run backing file cache slot page key
      let tree := vfsTree cache slot page key
      Returns (pagerTree (stagedCall request key)) (handlePager backing)
        (file, cache, []) (out.file, out.cache, out.exchanges) (out.result, out.cache) ∧
      Returns tree (handleVfs backing) (file, []) (out.file, out.exchanges) (out.result, out.cache) ∧
      Trace.Valid backing file out.exchanges out.file ∧ Observes tree out := by
  dsimp only
  obtain ⟨target, before, _, _, _, _, _, live, _⟩ := VFS.open_success success
  let file := { before with openMode := some target.mode }
  let page : PageRead.Page := ⟨opened.handle, number, size⟩
  refine ⟨file, ⟨allowed, ⟨target.mode, live⟩, rfl⟩, ?_⟩
  rw [TrackB.Read.run_eq_staged]
  exact Read.Adapter.interpretations_agree (SqliteVfs.backing maximum capacity) file cache
    ⟨slot, page⟩ key

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}

theorem catalog_cold_warm (capacity : Nat) (locate : Bridge.Locate sem)
    (db : Connection (Bridge.profile sem FileState)) (call : Invocation CatalogExecutor.Names)
    (plan : Plan (CatalogExecutor.Target sem)) (key : Int64) (table : Vdbe.Table)
    (bound : Bridge.Bound db call plan key) (leaf : Bridge.ColdLeaf db (locate plan.target) table)
    (projected : Bridge.Projected plan.target table key) :
    let request := locate plan.target
    let backing := readOnly capacity
    let memory := TrackB.Read.leafMemory request.page.number table
    ∃ bytes row cell,
      let result : SelectResult SqlValue := ⟨plan.label, cell⟩
      let suffix : Trace := [⟨request.page.request, .ok bytes⟩]
      let resident := db.cache.install request.target request.page bytes
      let after := { db with cache := resident, exchanges := db.exchanges ++ suffix }
      let cold : Read.Outcome FileState := ⟨.ok (TrackB.Read.project row), db.backing, resident, suffix⟩
      let warm : Read.Outcome FileState := ⟨cold.result, cold.file, cold.cache, []⟩
      FileView.VdbeLeaf.table? (TrackB.Read.acquiredView bytes) (btreeHeaderOffset request.page.number) =
        some table ∧
      Page.Run TrackB.Read.leafModel (TrackB.Read.pageLookup request.page.number key) memory [] (.returned row memory) ∧
      Observes (vfsTree db.cache request.target request.page key) cold ∧
      Observes (vfsTree resident request.target request.page key) warm ∧
      Returns (pagerTwice (stagedCall request key)) (handlePager backing)
        (db.backing, db.cache, db.exchanges) (after.backing, after.cache, after.exchanges)
        ((cold.result, resident), (warm.result, resident)) ∧
      Trace.Valid backing db.backing suffix after.backing ∧
      Bridge.transferResult cold.result = .ok cell ∧
      CatalogExecutor.execute sem (Bridge.forgetStorage db) call =
        (.statement (.ok result), Bridge.forgetStorage after) ∧
      (Bridge.executor backing locate).executeBatch db [call, call] =
        (⟨[(result, after), (result, after)], none⟩, after) := by
  let request := locate plan.target
  have range := leaf.range
  change ReadRange ((request.page.number - 1) * request.page.size : Nat) request.page.size at range
  rw [leaf.pageSize] at range
  obtain ⟨actual, row, decoded, run, trace, _, _, cold, warm⟩ :=
    TrackB.Read.Interaction.readOnly_cold_warm_observations capacity db.backing leaf.image request.page.number
      leaf.view request.page.handle db.cache request.target key table leaf.snapshot leaf.found
      leaf.live range leaf.owned leaf.decoded
  rw [← leaf.pageSize] at trace cold warm
  simp only [List.append_nil] at trace
  obtain ⟨bytes, cell, matching, catalog, batch, twice, valid⟩ :=
    Bridge.execute_cold_warm capacity locate db call plan key table bound leaf projected
  change Trace.Valid (readOnly capacity) db.backing [⟨request.page.request, .ok bytes⟩] db.backing at valid
  have response (payload : SqliteVfs.Bytes)
      (h : Trace.Valid (readOnly capacity) db.backing [⟨request.page.request, .ok payload⟩]
        db.backing) : (readOnly capacity db.backing request.page.request).1 = .ok payload := by
    cases h with
    | cons step _ => exact congrArg Prod.fst step
  have same : bytes = actual := ReadReply.ok.inj ((response bytes valid).symm.trans (response actual trace))
  subst bytes
  have rowEq := Page.Exit.returned.inj ((TrackB.Read.page_lookup_run_iff leaf.decoded key).mp run).2
  have resultEq : TrackB.Read.project row = Read.lookupValue table key :=
    congrArg TrackB.Read.project rowEq.1 |>.trans (TrackB.Read.leaf_lookup table key)
  have transfer : Bridge.transferResult (.ok (TrackB.Read.project row)) = .ok cell := by
    rw [resultEq]
    have unique {other : Option SqlValue} (atKey : plan.target.Matches key other) : cell = other :=
      ((CatalogExecutor.Target.lookup_iff _ _ _).mpr matching).symm.trans
        ((CatalogExecutor.Target.lookup_iff _ _ _).mpr atKey)
    have atKey := projected.2
    unfold Read.lookupValue
    cases get : table.get key.toInt with
    | none =>
      rw [get] at atKey
      have sameCell := unique atKey
      subst cell
      rfl
    | some fields =>
      rw [get] at atKey
      obtain ⟨value, converted, atKey⟩ := atKey
      have sameCell := unique atKey
      subst cell
      simp [Bridge.transferResult, converted, Except.map]
  refine ⟨actual, row, cell, decoded, run, cold, warm, ?_, valid, transfer, catalog, batch⟩
  simpa only [resultEq] using twice

end Silmaril.Proofs.Machine.SQLite.BTree
