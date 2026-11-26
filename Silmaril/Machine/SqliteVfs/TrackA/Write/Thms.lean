module

public import Silmaril.Machine.SqliteVfs.TrackA.Write.Defs
import Silmaril.Proofs.Machine.SqliteVfs.TrackA.Write.Backing
import Silmaril.Proofs.Machine.SqliteVfs.TrackA.Write.Correspondence

public section

namespace Silmaril.Machine.SqliteVfs.TrackA.Write

open Silmaril.Semantics.TrackA.Interaction
open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile (Edited)

variable {op : Insert} {vm : Vdbe.State} {ctx : Context} {id amount : Int64}
variable {edited : Edited} {catalogue newPage : Bytes} {limits : Limits}

/-- The selected P2 and P3 inputs carry a packed two-field record and a signed
rowid. The cursor and running VM must already be admitted. -/
theorem operands_of_registers {record : Silmaril.Formats.Bytes}
    (running : vm.halted = none) (cursor : op.cursor = ctx.cursor)
    (rowid : vm.registers op.rowidRegister = .integer id)
    (payload : vm.registers op.recordRegister = .blob record)
    (decoded : Record.decode? .utf8 record = some #[.null, .integer amount]) :
    op.operands vm ctx = .ok (id, amount) := by
  simp [Insert.operands, running, cursor, rowid, payload, decoded]
  rfl

/-- A successful logical insert and packed leaf encode admit the no-split edit. -/
theorem prepareLeaf_ok
    (inserted : ctx.snapshot.apply (.insert (.integer id) (.integer amount)) = .ok edited)
    (packed : WriteProfile.Image.tablePage edited.snapshot = .ok newPage) :
    prepareLeaf ctx id amount = .ok (edited, newPage) :=
  Proofs.Machine.SqliteVfs.TrackA.Write.prepareLeaf_ok inserted packed

/-- The handler-selected run supplies a complete Track A observation with
both its actual replies and its ordinary return. -/
theorem run_observes (handler : Coalgebra.Handler vfs Files) (program : Program) (files : Files) :
    let run := program.run handler files
    Silmaril.Semantics.TrackA.Interaction.Trace.finite run.events (.returned (some run.result)) ∈
      unfoldProgram.observes program :=
  Proofs.Machine.SqliteVfs.TrackA.Write.run_observes handler program files

/-- The model has no explicit UB observation, including on VFS error paths. -/
theorem no_ub (program : Program) :
    none ∉ UB.atBoundary (unfoldProgram.observes program) :=
  Proofs.Machine.SqliteVfs.TrackA.Write.no_ub program

/-- After VM operand admission and a successful pure leaf preflight, a run
of `insertAndCommit` implements the flat schedule. It reflects the handler's
actual replies and poststate, stopping at the first failed request. -/
theorem run_follows_schedule (handler : Coalgebra.Handler vfs Files) (files : Files)
    (vmOperands : op.operands vm ctx = .ok (id, amount))
    (prepared : prepareLeaf ctx id amount = .ok (edited, newPage)) :
    let run := (insertAndCommit op vm ctx).run handler files
    ∃ status, run.result.vfsStatus = some status ∧
      FollowsSchedule handler (schedule ctx newPage) files run.events status run.files :=
  Proofs.Machine.SqliteVfs.TrackA.Write.run_follows_schedule handler files vmOperands prepared

/-- In a run of `insertAndCommit` after operand admission and leaf preflight,
even a failed database write attempt follows a successful preimage write
and successful sync on the journal handle. -/
theorem database_write_requires_journal (handler : Coalgebra.Handler vfs Files) (files : Files)
    (vmOperands : op.operands vm ctx = .ok (id, amount))
    (prepared : prepareLeaf ctx id amount = .ok (edited, newPage))
    (attempt : Call.write .database ctx.databaseHandle 512 newPage ∈
      ((insertAndCommit op vm ctx).run handler files).events.map Sigma.fst) :
    ∃ response rest, ((insertAndCommit op vm ctx).run handler files).events =
      ⟨Call.write .journal ctx.journalHandle 0 ctx.oldPage, .ok ()⟩ ::
      ⟨Call.sync .journal ctx.journalHandle, .ok ()⟩ ::
      ⟨Call.write .database ctx.databaseHandle 512 newPage, response⟩ :: rest :=
  Proofs.Machine.SqliteVfs.TrackA.Write.database_write_requires_journal
    handler files vmOperands prepared attempt

/-- With the canonical catalogue and resident preimage, sufficient capacity
and the fault-free bounded backing, the selected run completes both phases.
The catalogue bytes are preserved, the journal is removed, and reopening
the database finds the logical insert with every prior row preserved. -/
theorem commit_success
    (vmOperands : op.operands vm ctx = .ok (id, amount))
    (inserted : ctx.snapshot.apply (.insert (.integer id) (.integer amount)) = .ok edited)
    (resident : WriteProfile.Image.tablePage ctx.snapshot = .ok ctx.oldPage)
    (catalogueOk : WriteProfile.Image.cataloguePage = .ok catalogue)
    (packed : WriteProfile.Image.tablePage edited.snapshot = .ok newPage)
    (journalCapacity : 512 ≤ limits.journal) (databaseCapacity : 1024 ≤ limits.database) :
    let run := (insertAndCommit op vm ctx).run (dispatch limits) (initialFiles ctx catalogue)
    run.events = completed ctx newPage ∧
      run.result = .ok ⟨{ vm.advance with halted := some 0 }, edited.snapshot, 1⟩ ∧
      run.files = ⟨openWritable ctx.databaseHandle (catalogue ++ newPage), none⟩ ∧
      TableLeaf.open? (Silmaril.Formats.Bytes.ofList run.files.database.bytes) =
        some edited.snapshot.readTable ∧
      edited.snapshot.rows = ⟨id, amount⟩ :: ctx.snapshot.rows :=
  Proofs.Machine.SqliteVfs.TrackA.Write.commit_success
    vmOperands inserted resident catalogueOk packed journalCapacity databaseCapacity

/-- An injected journal sync error returns the ordinary VFS error, retains
the written preimage, and leaves the database backing untouched. -/
theorem journal_sync_failure {reason : SqliteVfs.Error}
    (vmOperands : op.operands vm ctx = .ok (id, amount))
    (prepared : prepareLeaf ctx id amount = .ok (edited, newPage))
    (resident : WriteProfile.Image.tablePage ctx.snapshot = .ok ctx.oldPage)
    (journalCapacity : 512 ≤ limits.journal) :
    let run := (insertAndCommit op vm ctx).run (dispatch limits (some reason))
      (initialFiles ctx catalogue)
    run.events =
      [⟨Call.write .journal ctx.journalHandle 0 ctx.oldPage, .ok ()⟩,
       ⟨Call.sync .journal ctx.journalHandle, .error reason⟩] ∧
    run.result = .error (.vfs .syncJournal reason) ∧
    run.files.database = (initialFiles ctx catalogue).database ∧
    run.files.journal = some (openWritable ctx.journalHandle ctx.oldPage) :=
  Proofs.Machine.SqliteVfs.TrackA.Write.journal_sync_failure
    vmOperands prepared resident journalCapacity

end Silmaril.Machine.SqliteVfs.TrackA.Write
