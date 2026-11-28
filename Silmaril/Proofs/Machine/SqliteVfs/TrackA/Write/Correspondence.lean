module

public import Silmaril.Machine.SqliteVfs.TrackA.Write.Defs
import Silmaril.Semantics.TrackA.Interaction.Thms

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.TrackA.Write

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.TrackA.Write
open Silmaril.Semantics.TrackA.Interaction
open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile (Edited Row Snapshot)

variable {op : Insert} {vm : Vdbe.State} {ctx : Context} {id amount : Int64}
variable {edited : Edited} {catalogue newPage : Silmaril.Machine.SqliteVfs.Bytes} {limits : Limits}

theorem run_observes (handler : Coalgebra.Handler vfs Files) (program : Program) (files : Files) :
    let run := program.run handler files
    Trace.finite run.events (.returned (some run.result)) ∈ unfoldProgram.observes program := by
  induction program generalizing files with
  | done result =>
    exact ⟨.done result, .done result, .nil _, .refl, rfl⟩
  | silent next ih =>
    rw [Coalgebra.observes_tau (c := unfoldProgram) (start := .silent next) (next := next) rfl]
    exact ih files
  | call request next ih =>
    obtain ⟨reply, after, h⟩ : ∃ r f, handler files request = (r, f) :=
      ⟨_, _, (Prod.eta _).symm⟩
    simp only [Program.run.eq_3, h]
    have step : unfoldProgram.WeakStep (.call request next) ⟨request, reply⟩ (next reply) :=
      ⟨.call request next, .refl, .vis rfl reply⟩
    obtain ⟨y, z, follows, silent, ends⟩ := ih reply after
    exact ⟨y, z, .cons step follows, silent, ends⟩

theorem no_ub (program : Program) : none ∉ UB.atBoundary (unfoldProgram.observes program) := by
  rintro ⟨trace, observed, classified⟩
  cases trace with
  | infinite events => simp [UB.classify] at classified
  | finite events ending =>
    cases ending with
    | returned value =>
      cases value with
      | some result => simp [UB.classify] at classified
      | none =>
        obtain ⟨_, finish, _, _, ends⟩ := observed
        cases finish <;> cases ends
    | stuck request => simp [UB.classify] at classified
    | deadlock kind => simp [UB.classify] at classified
    | diverge => simp [UB.classify] at classified

theorem prepareLeaf_ok
    (inserted : ctx.snapshot.apply (.insert (.integer id) (.integer amount)) = .ok edited)
    (packed : WriteProfile.Image.tablePage edited.snapshot = .ok newPage) :
    prepareLeaf ctx id amount = .ok (edited, newPage) := by
  simp [prepareLeaf, inserted, packed, Except.mapError, bind, Except.bind]
  rfl

private theorem issue_follows (handler : Coalgebra.Handler vfs Files) (files : Files)
    (stage : Stage) (call : Call) (calls : List Call) (next : Program)
    (continuation : ∀ f, let run := next.run handler f
      ∃ status, run.result.vfsStatus = some status ∧
        FollowsSchedule handler calls f run.events status run.files) :
    let run := (issue stage call next).run handler files
    ∃ status, run.result.vfsStatus = some status ∧
      FollowsSchedule handler (call :: calls) files run.events status run.files := by
  cases h : handler files call with
  | mk reply after =>
    cases reply with
    | ok ack =>
      cases ack
      obtain ⟨status, result, trace⟩ := continuation after
      refine ⟨status, ?_, ?_⟩
      · simpa [issue, Program.run, h] using result
      · simpa [issue, Program.run, h] using FollowsSchedule.next h trace
    | error reason =>
      exact ⟨.error reason, by simp [issue, Program.run, h, Result.vfsStatus],
        by simpa [issue, Program.run, h] using
          (FollowsSchedule.failed (calls := calls) h)⟩

theorem run_follows_schedule (handler : Coalgebra.Handler vfs Files) (files : Files)
    (vmOperands : op.operands vm ctx = .ok (id, amount))
    (prepared : prepareLeaf ctx id amount = .ok (edited, newPage)) :
    let run := (insertAndCommit op vm ctx).run handler files
    ∃ status, run.result.vfsStatus = some status ∧
      FollowsSchedule handler (schedule ctx newPage) files run.events status run.files := by
  simp only [insertAndCommit, vmOperands, Program.run.eq_2, btreeInsert, prepared, Pager.admit,
    schedule]
  apply issue_follows
  intro afterJournalWrite
  simp only [Program.run.eq_2, Pager.phaseOne, Context.page, PageRead.Page.offset,
    File.Write.pageSize, Nat.reduceSub, Nat.reduceMul]
  apply issue_follows
  intro afterJournalSync
  apply issue_follows
  intro afterDbWrite
  apply issue_follows
  intro afterDbSync
  simp only [Pager.phaseTwo]
  apply issue_follows
  intro afterDelete
  exact ⟨.ok (), rfl, .done afterDelete⟩

private theorem schedule_journal_prefix {handler : Coalgebra.Handler vfs Files}
    {start finish : Files} {events : List Event} {status : Except Silmaril.Machine.SqliteVfs.Error Unit}
    (trace : FollowsSchedule handler (schedule ctx newPage) start events status finish)
    (attempt : Call.write .database ctx.databaseHandle 512 newPage ∈ events.map Sigma.fst) :
    ∃ response rest, events =
      ⟨Call.write .journal ctx.journalHandle 0 ctx.oldPage, .ok ()⟩ ::
      ⟨Call.sync .journal ctx.journalHandle, .ok ()⟩ ::
      ⟨Call.write .database ctx.databaseHandle 512 newPage, response⟩ :: rest := by
  unfold schedule at trace
  cases trace with
  | failed =>
    change Call.write .database ctx.databaseHandle 512 newPage ∈
      ([Call.write .journal ctx.journalHandle 0 ctx.oldPage] : List Call) at attempt
    simp at attempt
  | next _ journalSync =>
    cases journalSync with
    | failed =>
      change Call.write .database ctx.databaseHandle 512 newPage ∈
        ([Call.write .journal ctx.journalHandle 0 ctx.oldPage,
          Call.sync .journal ctx.journalHandle] : List Call) at attempt
      simp at attempt
    | next _ databaseWrite =>
      cases databaseWrite with
      | next => exact ⟨.ok (), _, rfl⟩
      | failed => exact ⟨.error _, [], rfl⟩

theorem database_write_requires_journal (handler : Coalgebra.Handler vfs Files) (files : Files)
    (vmOperands : op.operands vm ctx = .ok (id, amount))
    (prepared : prepareLeaf ctx id amount = .ok (edited, newPage))
    (attempt : Call.write .database ctx.databaseHandle 512 newPage ∈
      ((insertAndCommit op vm ctx).run handler files).events.map Sigma.fst) :
    ∃ response rest, ((insertAndCommit op vm ctx).run handler files).events =
      ⟨Call.write .journal ctx.journalHandle 0 ctx.oldPage, .ok ()⟩ ::
      ⟨Call.sync .journal ctx.journalHandle, .ok ()⟩ ::
      ⟨Call.write .database ctx.databaseHandle 512 newPage, response⟩ :: rest := by
  obtain ⟨_, _, trace⟩ := run_follows_schedule handler files vmOperands prepared
  exact schedule_journal_prefix trace attempt

end Silmaril.Proofs.Machine.SqliteVfs.TrackA.Write
