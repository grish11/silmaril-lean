module

public import Silmaril.Machine.SQLite.BTree.Defs
public import Silmaril.Machine.SQLite.TrackB.Read.Interaction.Thms
public import Silmaril.Machine.SQLite.Relational.Bridge.Thms
public import Silmaril.Semantics.BTreePages.Trace.Thms
import Silmaril.Proofs.Machine.SQLite.BTree.Composition

public section

namespace Silmaril.Machine.SQLite.BTree

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite
open Silmaril.Machine.SQLite.TrackA
open Silmaril.Machine.SqliteVfs
open Silmaril.Semantics
open Silmaril.SQLite.Relational
open Read.Adapter (Acquire Observes Returns handlePager handleVfs pagerTree pagerTwice stagedCall)
open Read.Interaction (vfsTree)
open FileView.Admission.VdbeLeaf (btreeHeaderOffset)


/-- A named open selects the same live backing used by the typed Pager and
VFS interpreters. The entire Track B outcome survives, including any ordinary
acquisition or decoder error and the actual backing and cache poststates. -/
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
      Trace.Valid backing file out.exchanges out.file ∧ Observes tree out :=
  Proofs.Machine.SQLite.BTree.opened_read success grant allowed cache slot number size key

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}

/-- Both cold/warm point calls project one generic run on the actual acquired
bytes. It supplies the cell used by the repeated Pager call and the D4 batch.
Storage erasure gives the D3 result and connection. The open VFS observations
select the complete cold exchange and the empty warm trace. -/
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
        (⟨[(result, after), (result, after)], none⟩, after) :=
  Proofs.Machine.SQLite.BTree.catalog_cold_warm capacity locate db call plan key table
    bound leaf projected

end Silmaril.Machine.SQLite.BTree
