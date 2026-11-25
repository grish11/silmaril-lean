module

public import Silmaril.Containers.SqliteVfs.ReadEntry.Defs
public import Silmaril.Containers.SqliteVfs.Completed.Defs
import Silmaril.Containers.SqliteVfs.Completed.Thms
import Silmaril.Containers.SqliteVfs.Thms
import Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary.Thms
import Silmaril.Machine.SqliteRead.Thms

@[expose] public section

namespace Silmaril.Proofs.Containers.SqliteVfs.ReadEntry

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.Completed
open Silmaril.Containers.SqliteVfs.ReadEntry
open Silmaril.Machine
open Silmaril.Machine.Behaviour.Observable
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary

theorem dispatch_pending {State : Type} (handler : Handler State) (state : State)
    {binding : FileBinding} {page : Page} {request : SqliteRead.Request} {env : SqliteRead.Context}
    {observation : SqliteRead.Obs} (safe : Safe ((SqliteRead.contract env).spec request))
    (seen : observation ∈ (SqliteRead.contract env).spec request)
    (aligned : MatchesPage binding request page) (positive : 0 < page.number) :
    page.Admitted ∧ projectEntry binding observation = some (.recv page.request) ∧
      (machine handler).Exec Mach.seqPolicy (.idle state) [.recv page.request]
        (.pending state page.request) ∧ completed [.recv page.request] = [] := by
  refine ⟨page_admitted request page env ((SqliteRead.safe_iff_admitted env request).mp safe)
      aligned positive, ?_, ?_, rfl⟩
  · rw [SqliteRead.dispatch_only safe seen]
    simp [projectEntry, SqliteRead.dispatch, aligned.handle, aligned.offset, aligned.amount, Page.request]
  · exact exec_iff.mpr ⟨[], state, .nil _, .inr ⟨page.request, rfl, rfl⟩⟩

theorem single_receive_not_blocked {State : Type} (handler : Handler State)
    (state : State) (request : Request) :
    ¬ (runtime handler).beh state (.blocked [.recv request]) := by
  intro blocked
  have shape := (completed_blocked_iff.mp blocked).1
  change [Event.recv request] = [] at shape
  cases shape

end Silmaril.Proofs.Containers.SqliteVfs.ReadEntry
