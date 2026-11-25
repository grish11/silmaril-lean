module

public import Silmaril.Containers.SqliteVfs.ReadEntry.Defs
public import Silmaril.Containers.SqliteVfs.Completed.Defs
import Silmaril.Proofs.Containers.SqliteVfs.ReadEntry.Projection

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.ReadEntry

open Silmaril.Machine
open Silmaril.Machine.Behaviour.Observable
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary
open Completed (completed)

/-- A safe and page-aligned ABI entry yields an admitted page and an
unanswered receive. The backing stays in its initial state and there are
zero completed exchanges. -/
theorem dispatch_pending {State : Type} (handler : Handler State) (state : State)
    {binding : FileBinding} {page : Page} {request : SqliteRead.Request} {env : SqliteRead.Context}
    {observation : SqliteRead.Obs} (safe : Safe ((SqliteRead.contract env).spec request))
    (seen : observation ∈ (SqliteRead.contract env).spec request)
    (aligned : MatchesPage binding request page) (positive : 0 < page.number) :
    page.Admitted ∧ projectEntry binding observation = some (.recv page.request) ∧
      (machine handler).Exec Mach.seqPolicy (.idle state) [.recv page.request]
        (.pending state page.request) ∧ completed [.recv page.request] = [] :=
  Proofs.Containers.SqliteVfs.ReadEntry.dispatch_pending handler state safe seen aligned positive

/-- The runtime can report blocking only at an idle boundary. A receive on
its own therefore cannot be a blocked runtime observation. -/
theorem single_receive_not_blocked {State : Type} (handler : Handler State)
    (state : State) (request : Request) :
    ¬ (runtime handler).beh state (.blocked [.recv request]) :=
  Proofs.Containers.SqliteVfs.ReadEntry.single_receive_not_blocked handler state request

end Silmaril.Containers.SqliteVfs.ReadEntry
