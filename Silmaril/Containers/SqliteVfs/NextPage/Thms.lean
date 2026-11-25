module

public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.NextPage.Defs
import Silmaril.Proofs.Containers.SqliteVfs.NextPage.Trace

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.NextPage

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs (machine runtime encode)
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.NextPage (fillFollowing)

/-- The actual exchanges of a fill and any selected follow-up form a
completed serial machine execution and its input-blocked observation. -/
theorem fill_following_observation {State : Type} (handler : Handler State) (file : State)
    (cache : Cache) (firstSlot : SlotId) (firstPage : Page) (nextSlot : SlotId)
    (select : Bytes → Option Page) :
    let first := fill handler file cache firstSlot firstPage
    let next := fillFollowing handler first nextSlot select
    let trace := first.trace ++ (next.map Outcome.trace).getD []
    let final := (next.map Outcome.file).getD first.file
    Trace.Valid handler file trace final ∧
      (machine handler).Exec Mach.seqPolicy (.idle file) (encode trace) (.idle final) ∧
      (runtime handler).beh file (.blocked (encode trace)) ∧
      completed (encode trace) = trace :=
  Proofs.Containers.SqliteVfs.NextPage.fill_following_observation
    handler file cache firstSlot firstPage nextSlot select

end Silmaril.Containers.SqliteVfs.NextPage
