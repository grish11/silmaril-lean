module
import Batteries.Data.Except

import Silmaril.Machine.SQLite.BTree.Thms
import Silmaril.Machine.SQLite.Pager.Thms
import Silmaril.Machine.SQLite.VFS.Thms
import Silmaril.Formats.Sqlite.Record.Write.Defs
meta import Silmaril.Machine.SQLite.TrackB.Read.Defs
meta import Silmaril.Machine.SQLite.Pager.Defs
meta import Silmaril.Machine.SQLite.VFS.Defs
meta import Silmaril.Formats.Sqlite.Record.Write.Defs

namespace Silmaril.Machine.SQLite

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.TrackA
open Silmaril.Semantics

private def sampleFile : FileState := ⟨[4], none, 17⟩
private def otherFile : FileState := ⟨[9], none, 17⟩

private def paths : VFS.FileMap := fun path =>
  if path = "sample.db" then some sampleFile
  else if path = "other.db" then some otherFile
  else none

#guard decide (VFS.parseOpen true .readWrite "file:sample.db?mode=ro" =
  .ok ⟨"sample.db", .readOnly⟩)
#guard decide (VFS.parseOpen true .readOnly "file:sample.db?mode=rw" = .error .modeEscalation)
#guard decide (VFS.parseOpen false .readOnly "file:sample.db" = .error .unsupportedName)
#guard decide (VFS.parseOpen true .readWrite "file://localhost/sample.db" = .error .unsupportedName)
#guard decide (VFS.parseOpen true .readWrite "file:sample.db?nolock=1" = .error .unsupportedName)
#guard decide (VFS.parseOpen true .readWrite "file:sample%2edb" = .error .unsupportedName)

#guard
  let (reply, after) := VFS.openExisting .readWrite 1024 true .readWrite "file:sample.db?mode=ro" paths
  decide (reply = .ok ⟨"sample.db", ⟨17⟩⟩) &&
    after "sample.db" == some { sampleFile with openMode := some .readOnly } &&
    after "other.db" == some otherFile

-- A well-typed VFS handler can violate the byte contract.
example : ¬ ReadOnlyProfile (badShortRead 1024) id := bad_not_readOnlyProfile 1024

-- An undefined generic slot produces Page UB before any leaf projection.
example : Page.Run TrackB.Read.leafModel (TrackB.Read.pageLookup 2 42)
    (fun _ => .undef) [] (.stopped (.ub (.readUndef 2))) :=
  .ub (.readUndef rfl)

private def snapshot : WriteProfile.Snapshot := ⟨[⟨42, 7⟩], by decide⟩
private def namedRead (short : Bool) (expected : TrackA.Read.Result) : Bool :=
  (do
    let image ← (WriteProfile.Image.encode snapshot).toOption
    let bytes := if short then image.toList.take 600 else image.toList
    let files : VFS.FileMap := fun name =>
      if name = "sample.db" then some ⟨bytes, none, 17⟩ else none
    let (reply, after) := VFS.openExisting .readOnly 1024 true .readOnly "file:sample.db" files
    let opened ← reply.toOption
    let file ← after opened.path
    let page : PageRead.Page := ⟨opened.handle, 2, 512⟩
    let cache : PageRead.Cache := fun slot => if slot = 0 then some .vacant else none
    let cold := TrackB.Read.run (readOnly 1024) file cache 0 page 42
    let again := TrackB.Read.run (readOnly 1024) cold.file cold.cache 0 page 42
    pure (decide (cold.result = expected) && decide (again.result = expected) && again.file == file &&
      cold.exchanges.length == 1 && again.exchanges.length == (if short then 1 else 0) &&
      cold.cache 0 == (if short then some .vacant else some (.resident page (readBytes bytes 512 512))))
    : Option Bool).getD false

#guard namedRead false (.ok (some (.integer 7)))
#guard namedRead true (.error (.acquire .shortRead))

private def op : Write.Insert := ⟨0, 1, 2⟩
private def vm : Vdbe.State :=
  (Vdbe.State.initial.write 1 (.blob (Silmaril.Formats.Bytes.ofList (Record.Write.amount 11)))).write
    2 (.integer (-3))

private def opened : VFS.Opened := ⟨"sample.db", ⟨17⟩⟩

example : ¬ (Pager.LockGrant.mk opened .shared).Allows opened .readWrite := by
  simp [Pager.LockGrant.Allows]

-- A follow-up Track B read acquires the committed leaf or the intact old leaf.
-- The sync fault still has its own typed error and journal poststate.
private def insertThenRead (fault : Option Error) : Bool :=
  (do
    let catalogue ← WriteProfile.Image.cataloguePage.toOption
    let preimage ← (WriteProfile.Image.tablePage snapshot).toOption
    let ctx : Write.Context := ⟨0, snapshot, preimage, opened.handle, ⟨17⟩⟩
    let files := Write.initialFiles ctx catalogue
    let cache : PageRead.Cache := fun slot => if slot = 0 then some (.resident ctx.page preimage) else none
    let (run, retired) ← (Pager.observeInsert (Write.dispatch ⟨1024, 512⟩ fault)
      files cache 0 op vm ctx).toOption
    let read := TrackB.Read.run (readOnly 1024) run.files.database retired 0 ctx.page (-3)
    let writeOk := match fault, run.result with
      | none, .ok result =>
        result.snapshot.rows.map (fun row => (row.id, row.amount)) == [(-3, 11), (42, 7)] && result.changed == 1 &&
          run.events.length == 5 && run.files.journal.isNone
      | some reason, .error (.vfs .syncJournal actual) =>
        actual == reason && run.events.length == 2 &&
          run.files.database == files.database &&
          run.files.journal == some (Write.openWritable ctx.journalHandle preimage)
      | _, _ => false
    let expected := if fault.isNone then some (.integer 11) else none
    pure (writeOk && retired 0 == some .vacant && decide (read.result = .ok expected) &&
      read.exchanges.length == 1 && read.file == run.files.database) : Option Bool).getD false

#guard insertThenRead none
#guard insertThenRead (some .ioWrite)

#print axioms VFS.open_success
#print axioms VFS.open_error_preserves
#print axioms Pager.observeInsert_ofAccess
#print axioms Pager.commit_reopens
#print axioms Pager.sync_failure_preserves_database
#print axioms BTree.opened_read
#print axioms BTree.catalog_cold_warm

end Silmaril.Machine.SQLite
