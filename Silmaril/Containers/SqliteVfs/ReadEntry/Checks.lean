module

import Silmaril.Containers.SqliteVfs.ReadEntry.Thms
import Silmaril.Machine.SqliteRead.Thms

namespace Silmaril.Containers.SqliteVfs.ReadEntry

open Silmaril.Machine
open Silmaril.Machine.Behaviour.Observable
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary (FileBinding MatchesPage)
open Completed (completed)

private def request : SqliteRead.Request := ⟨1, 32, 2, 0⟩
private def page : Page := ⟨⟨0⟩, 1, 2⟩
private def bindings : FileBinding := fun ptr => if ptr = 1 then some ⟨0⟩ else none
private def context : SqliteRead.Context := ⟨fun _ => True, fun _ _ => True⟩
private def file : FileState := ⟨[10, 20], some .readOnly, 0⟩

private theorem admitted : context.Admits request :=
  ⟨by decide, trivial, by decide, by decide, by decide, by decide, by decide, trivial⟩

example : (machine (readOnly 8)).Exec Mach.seqPolicy (.idle file) [.recv page.request]
    (.pending file page.request) ∧ completed [.recv page.request] = [] := by
  have safe := (SqliteRead.safe_iff_admitted context request).mpr admitted
  have inSpec : SqliteRead.dispatch request ∈ (SqliteRead.contract context).spec request := by
    rw [Contract.spec_of_pre (show (SqliteRead.contract context).pre request from admitted)]
    rfl
  have aligned : MatchesPage bindings request page := ⟨rfl, rfl, rfl⟩
  exact (dispatch_pending (readOnly 8) file safe inSpec aligned (by decide)).2.2

example : projectEntry bindings ⟨[request], .faulted .data⟩ = none := rfl
example : projectEntry (fun _ => none) (SqliteRead.dispatch request) = none := rfl

example : ¬ (runtime (readOnly 8)).beh file (.blocked [.recv page.request]) :=
  single_receive_not_blocked (readOnly 8) file page.request

#print axioms dispatch_pending
#print axioms single_receive_not_blocked

end Silmaril.Containers.SqliteVfs.ReadEntry
