module

public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.NextPage.Defs
import Silmaril.Containers.SqliteVfs.Thms
import Silmaril.Containers.SqliteVfs.Completed.Thms
import Silmaril.Machine.SqliteVfs.PageRead.Thms
import Silmaril.Machine.SqliteVfs.PageRead.NextPage.Thms

@[expose] public section

namespace Silmaril.Proofs.Containers.SqliteVfs.NextPage

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs (machine runtime encode)
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.NextPage (fillFollowing)
open Silmaril.Containers.SqliteVfs (exec_iff blocked_iff)
open Silmaril.Containers.SqliteVfs.Completed (completed_encode)
open Silmaril.Machine.SqliteVfs.PageRead.NextPage (fillFollowing_trace)

private theorem append_valid {State : Type} {handler : Handler State}
    {start middle final : State} {frontTrace backTrace : Trace}
    (first : Trace.Valid handler start frontTrace middle)
    (second : Trace.Valid handler middle backTrace final) :
    Trace.Valid handler start (frontTrace ++ backTrace) final := by
  induction first with
  | nil => exact second
  | cons step _ ih => exact .cons step (ih second)

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
      completed (encode trace) = trace := by
  let first := fill handler file cache firstSlot firstPage
  let trace := first.trace ++ ((fillFollowing handler first nextSlot select).map Outcome.trace).getD []
  let final := ((fillFollowing handler first nextSlot select).map Outcome.file).getD first.file
  have front : Trace.Valid handler file first.trace first.file :=
    fill_trace handler file cache firstSlot firstPage
  have valid : Trace.Valid handler file trace final := by
    cases chosen : fillFollowing handler first nextSlot select with
    | none => simpa [trace, final, chosen] using front
    | some next =>
      have suffix := fillFollowing_trace handler first next nextSlot select chosen
      simpa [trace, final, chosen] using append_valid front suffix
  exact ⟨valid, exec_iff.mpr ⟨trace, final, valid, .inl ⟨rfl, rfl⟩⟩,
    blocked_iff.mpr ⟨trace, final, valid, rfl⟩, completed_encode trace⟩

end Silmaril.Proofs.Containers.SqliteVfs.NextPage
