module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.Pair.Composition

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.Pair

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- Two complete reads into distinct initially vacant slots preserve the
shared read-only backing, install both pages and record a valid ordered trace. -/
theorem readOnly_two_full_fills (capacity : Nat) (file : FileState) (cache : Cache)
    (firstSlot secondSlot : SlotId) (firstPage secondPage : Page)
    (different : secondSlot ≠ firstSlot)
    (firstOwned : cache firstSlot = some .vacant) (secondOwned : cache secondSlot = some .vacant)
    (firstAdmitted : firstPage.Admitted) (secondAdmitted : secondPage.Admitted)
    (firstLive : (file.mode firstPage.handle).isNone = false)
    (secondLive : (file.mode secondPage.handle).isNone = false)
    (firstComplete : firstPage.offset + firstPage.size ≤ file.bytes.length)
    (secondComplete : secondPage.offset + secondPage.size ≤ file.bytes.length) :
    let firstBytes := readBytes file.bytes firstPage.offset firstPage.size
    let secondBytes := readBytes file.bytes secondPage.offset secondPage.size
    let first := fill (readOnly capacity) file cache firstSlot firstPage
    let second := fill (readOnly capacity) first.file first.cache secondSlot secondPage
    first.result = .ok firstBytes ∧ second.result = .ok secondBytes ∧ second.file = file ∧
      second.cache = (cache.install firstSlot firstPage firstBytes).install secondSlot secondPage secondBytes ∧
      first.trace ++ second.trace =
        [⟨firstPage.request, .ok firstBytes⟩, ⟨secondPage.request, .ok secondBytes⟩] ∧
      Trace.Valid (readOnly capacity) file (first.trace ++ second.trace) second.file :=
  Proofs.Machine.SqliteVfs.PageRead.Pair.readOnly_two_full_fills capacity file cache firstSlot secondSlot
    firstPage secondPage different firstOwned secondOwned firstAdmitted secondAdmitted
    firstLive secondLive firstComplete secondComplete

end Silmaril.Machine.SqliteVfs.PageRead.Pair
