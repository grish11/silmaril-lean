module

public import Silmaril.Machine.SQLite.Pager.Defs
import Silmaril.Machine.SqliteVfs.PageRead.Release.Thms
import Silmaril.Machine.SqliteVfs.TrackA.Write.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.Pager

open Silmaril.Machine
open SqliteVfs
open Silmaril.Machine.SqliteVfs.TrackA
open Silmaril.Machine.SQLite
open Silmaril.Formats.Sqlite
open Silmaril.Semantics.TrackA.Interaction (Coalgebra)

variable {named : VFS.FileMap} {opened : VFS.Opened} {grant : Pager.LockGrant}
variable {ctx : Write.Context} {cache : PageRead.Cache} {slot : PageRead.SlotId}
variable {op : Write.Insert} {vm : Vdbe.State} {limits : Write.Limits}
variable {id amount : Int64} {edited : WriteProfile.Edited} {catalogue newPage : Bytes}

theorem observeInsert_ofAccess (handler : Coalgebra.Handler Write.vfs Write.Files)
    {files : Write.Files} (access : Pager.WriteAccess named opened grant ctx files cache slot) :
    Pager.observeInsert handler files cache slot op vm ctx =
      .ok ((Write.insertAndCommit op vm ctx).run handler files,
        fun other => if other = slot then some .vacant else cache other) := by
  simp [Pager.observeInsert, PageRead.Release.release_resident access.resident, Except.map]

theorem commit_reopens
    (access : Pager.WriteAccess named opened grant ctx (Write.initialFiles ctx catalogue) cache slot)
    (operands : op.operands vm ctx = .ok (id, amount))
    (inserted : ctx.snapshot.apply (.insert (.integer id) (.integer amount)) = .ok edited)
    (resident : WriteProfile.Image.tablePage ctx.snapshot = .ok ctx.oldPage)
    (catalogueOk : WriteProfile.Image.cataloguePage = .ok catalogue)
    (packed : WriteProfile.Image.tablePage edited.snapshot = .ok newPage)
    (journalCapacity : 512 ≤ limits.journal) (databaseCapacity : 1024 ≤ limits.database) :
    ∃ run after,
      Pager.observeInsert (Write.dispatch limits) (Write.initialFiles ctx catalogue) cache slot op vm ctx =
        .ok (run, after) ∧
      run.events = Write.completed ctx newPage ∧
      run.result = .ok ⟨{ vm.advance with halted := some 0 }, edited.snapshot, 1⟩ ∧
      run.files = ⟨Write.openWritable ctx.databaseHandle (catalogue ++ newPage), none⟩ ∧
      TableLeaf.open? (Formats.Bytes.ofList run.files.database.bytes) = some edited.snapshot.readTable ∧
      edited.snapshot.rows = ⟨id, amount⟩ :: ctx.snapshot.rows ∧
      after slot = some .vacant ∧ ∀ other, other ≠ slot → after other = cache other := by
  obtain ⟨events, result, files, reopened, rows⟩ :=
    Write.commit_success operands inserted resident catalogueOk packed journalCapacity databaseCapacity
  refine ⟨_, _, observeInsert_ofAccess (Write.dispatch limits) access,
    events, result, files, reopened, rows, ?_, ?_⟩
  · simp
  · intro other different
    simp [different]

theorem sync_failure_preserves_database {reason : Error}
    (access : Pager.WriteAccess named opened grant ctx (Write.initialFiles ctx catalogue) cache slot)
    (operands : op.operands vm ctx = .ok (id, amount))
    (prepared : Write.prepareLeaf ctx id amount = .ok (edited, newPage))
    (resident : WriteProfile.Image.tablePage ctx.snapshot = .ok ctx.oldPage)
    (journalCapacity : 512 ≤ limits.journal) :
    ∃ run after,
      Pager.observeInsert (Write.dispatch limits (some reason))
        (Write.initialFiles ctx catalogue) cache slot op vm ctx = .ok (run, after) ∧
      run.events =
        [⟨Write.Call.write .journal ctx.journalHandle 0 ctx.oldPage, .ok ()⟩,
         ⟨Write.Call.sync .journal ctx.journalHandle, .error reason⟩] ∧
      run.result = .error (.vfs .syncJournal reason) ∧
      run.files.database = (Write.initialFiles ctx catalogue).database ∧
      run.files.journal = some (Write.openWritable ctx.journalHandle ctx.oldPage) ∧
      after slot = some .vacant ∧ ∀ other, other ≠ slot → after other = cache other := by
  obtain ⟨events, result, database, journal⟩ :=
    Write.journal_sync_failure (limits := limits) (reason := reason) (catalogue := catalogue)
      operands prepared resident journalCapacity
  refine ⟨_, _, observeInsert_ofAccess (Write.dispatch limits (some reason)) access,
    events, result, database, journal, ?_, ?_⟩
  · simp
  · intro other different
    simp [different]

end Silmaril.Proofs.Machine.SQLite.Pager
