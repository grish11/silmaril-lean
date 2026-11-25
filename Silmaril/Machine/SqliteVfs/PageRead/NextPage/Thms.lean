module

public import Silmaril.Machine.SqliteVfs.PageRead.NextPage.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.NextPage.Select

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.NextPage

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

theorem fillFollowing_skips_rejected {State : Type} (handler : Handler State)
    (first : Outcome State) (target : SlotId) (select : Bytes → Option Page)
    (reason : FillError) (rejected : first.result = .error reason) :
    fillFollowing handler first target select = none := by
  simp [fillFollowing, rejected]

theorem fillFollowing_skips_unselected {State : Type} (handler : Handler State)
    (first : Outcome State) (target : SlotId) (select : Bytes → Option Page)
    (bytes : Bytes) (accepted : first.result = .ok bytes) (unselected : select bytes = none) :
    fillFollowing handler first target select = none := by
  simp [fillFollowing, accepted, unselected]

/-- The selected fill records a valid suffix from the first backing state. -/
theorem fillFollowing_trace {State : Type} (handler : Handler State)
    (first next : Outcome State) (target : SlotId) (select : Bytes → Option Page)
    (continued : fillFollowing handler first target select = some next) :
    Trace.Valid handler first.file next.trace next.file :=
  Proofs.Machine.SqliteVfs.PageRead.NextPage.fillFollowing_trace
    handler first next target select continued

/-- A choice made from the first full buffer glues two admitted reads
and yields exactly their two ordered exchanges. -/
theorem readOnly_selected_full_fills (capacity : Nat) (file : FileState) (cache : Cache)
    (firstSlot nextSlot : SlotId) (firstPage nextPage : Page) (select : Bytes → Option Page)
    (distinct : nextSlot ≠ firstSlot)
    (firstOwned : cache firstSlot = some .vacant) (nextOwned : cache nextSlot = some .vacant)
    (firstAdmitted : firstPage.Admitted) (nextAdmitted : nextPage.Admitted)
    (firstLive : (file.mode firstPage.handle).isNone = false)
    (nextLive : (file.mode nextPage.handle).isNone = false)
    (firstComplete : firstPage.offset + firstPage.size ≤ file.bytes.length)
    (nextComplete : nextPage.offset + nextPage.size ≤ file.bytes.length)
    (chosen : select (readBytes file.bytes firstPage.offset firstPage.size) = some nextPage) :
    let firstBytes := readBytes file.bytes firstPage.offset firstPage.size
    let nextBytes := readBytes file.bytes nextPage.offset nextPage.size
    let first := fill (readOnly capacity) file cache firstSlot firstPage
    let next := fill (readOnly capacity) first.file first.cache nextSlot nextPage
    fillFollowing (readOnly capacity) first nextSlot select = some next ∧
      first.result = .ok firstBytes ∧ next.result = .ok nextBytes ∧ next.file = file ∧
      next.cache = (cache.install firstSlot firstPage firstBytes).install nextSlot nextPage nextBytes ∧
      first.trace ++ next.trace = [⟨firstPage.request, .ok firstBytes⟩, ⟨nextPage.request, .ok nextBytes⟩] ∧
      Trace.Valid (readOnly capacity) file (first.trace ++ next.trace) next.file :=
  Proofs.Machine.SqliteVfs.PageRead.NextPage.readOnly_selected_full_fills
    capacity file cache firstSlot nextSlot firstPage nextPage select distinct firstOwned nextOwned
    firstAdmitted nextAdmitted firstLive nextLive firstComplete nextComplete chosen

end Silmaril.Machine.SqliteVfs.PageRead.NextPage
