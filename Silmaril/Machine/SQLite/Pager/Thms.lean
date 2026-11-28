module

public import Silmaril.Machine.SQLite.Pager.Defs
public import Silmaril.Machine.SQLite.TrackA.Read.Adapter.Thms
public import Silmaril.Machine.SqliteVfs.TrackA.Write.Thms
public import Silmaril.Machine.SqliteVfs.PageRead.Release.Thms
import Silmaril.Proofs.Machine.SQLite.Pager.Transaction

public section

namespace Silmaril.Machine.SQLite.Pager

open SqliteVfs
open Silmaril.Machine.SqliteVfs.TrackA
open Silmaril.Formats.Sqlite
open Silmaril.Semantics.TrackA.Interaction (Coalgebra)

variable {named : VFS.FileMap} {opened : VFS.Opened} {grant : LockGrant}
variable {ctx : Write.Context} {cache : PageRead.Cache} {slot : PageRead.SlotId}
variable {op : Write.Insert} {vm : Vdbe.State} {limits : Write.Limits}
variable {id amount : Int64} {edited : WriteProfile.Edited} {catalogue newPage : Bytes}

/-- The checked resident preimage allows the actual write run and retires
precisely the matching slot, for any handler in the write signature. -/
theorem observeInsert_ofAccess (handler : Coalgebra.Handler Write.vfs Write.Files)
    {files : Write.Files} (access : WriteAccess named opened grant ctx files cache slot) :
    observeInsert handler files cache slot op vm ctx =
      .ok ((Write.insertAndCommit op vm ctx).run handler files,
        fun other => if other = slot then some .vacant else cache other) :=
  Proofs.Machine.SQLite.Pager.observeInsert_ofAccess handler access

/-- After the selected rollback-mode commit, reopen the actual written file
and observe the inserted logical row and a vacant read-cache slot. -/
theorem commit_reopens
    (access : WriteAccess named opened grant ctx (Write.initialFiles ctx catalogue) cache slot)
    (operands : op.operands vm ctx = .ok (id, amount))
    (inserted : ctx.snapshot.apply (.insert (.integer id) (.integer amount)) = .ok edited)
    (resident : WriteProfile.Image.tablePage ctx.snapshot = .ok ctx.oldPage)
    (catalogueOk : WriteProfile.Image.cataloguePage = .ok catalogue)
    (packed : WriteProfile.Image.tablePage edited.snapshot = .ok newPage)
    (journalCapacity : 512 ≤ limits.journal) (databaseCapacity : 1024 ≤ limits.database) :
    ∃ run after,
      observeInsert (Write.dispatch limits) (Write.initialFiles ctx catalogue) cache slot op vm ctx =
        .ok (run, after) ∧
      run.events = Write.completed ctx newPage ∧
      run.result = .ok ⟨{ vm.advance with halted := some 0 }, edited.snapshot, 1⟩ ∧
      run.files = ⟨Write.openWritable ctx.databaseHandle (catalogue ++ newPage), none⟩ ∧
      TableLeaf.open? (Formats.Bytes.ofList run.files.database.bytes) = some edited.snapshot.readTable ∧
      edited.snapshot.rows = ⟨id, amount⟩ :: ctx.snapshot.rows ∧
      after slot = some .vacant ∧ ∀ other, other ≠ slot → after other = cache other :=
  Proofs.Machine.SQLite.Pager.commit_reopens access operands inserted resident catalogueOk
    packed journalCapacity databaseCapacity

/-- A failed journal sync returns the typed stage error with the preimage in
the journal, the old database backing and a retired read-cache slot. -/
theorem sync_failure_preserves_database {reason : Error}
    (access : WriteAccess named opened grant ctx (Write.initialFiles ctx catalogue) cache slot)
    (operands : op.operands vm ctx = .ok (id, amount))
    (prepared : Write.prepareLeaf ctx id amount = .ok (edited, newPage))
    (resident : WriteProfile.Image.tablePage ctx.snapshot = .ok ctx.oldPage)
    (journalCapacity : 512 ≤ limits.journal) :
    ∃ run after,
      observeInsert (Write.dispatch limits (some reason))
        (Write.initialFiles ctx catalogue) cache slot op vm ctx = .ok (run, after) ∧
      run.events =
        [⟨Write.Call.write .journal ctx.journalHandle 0 ctx.oldPage, .ok ()⟩,
         ⟨Write.Call.sync .journal ctx.journalHandle, .error reason⟩] ∧
      run.result = .error (.vfs .syncJournal reason) ∧
      run.files.database = (Write.initialFiles ctx catalogue).database ∧
      run.files.journal = some (Write.openWritable ctx.journalHandle ctx.oldPage) ∧
      after slot = some .vacant ∧ ∀ other, other ≠ slot → after other = cache other :=
  Proofs.Machine.SQLite.Pager.sync_failure_preserves_database access operands prepared resident
    journalCapacity

end Silmaril.Machine.SQLite.Pager
