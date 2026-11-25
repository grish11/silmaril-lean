module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.Order.Serial

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.Order

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- For two full reads into distinct owned slots on one snapshot, either
serial order preserves the same backing, cache, and per-page results.
The exchange lists record the two opposite orders. -/
theorem readOnly_two_fill_orders (capacity : Nat) (file : FileState) (cache : Cache)
    (firstSlot secondSlot : SlotId) (firstPage secondPage : Page)
    (different : secondSlot ≠ firstSlot)
    (firstOwned : cache firstSlot = some .vacant) (secondOwned : cache secondSlot = some .vacant)
    (firstAdmitted : firstPage.Admitted) (secondAdmitted : secondPage.Admitted)
    (firstLive : (file.mode firstPage.handle).isNone = false)
    (secondLive : (file.mode secondPage.handle).isNone = false)
    (firstComplete : firstPage.offset + firstPage.size ≤ file.bytes.length)
    (secondComplete : secondPage.offset + secondPage.size ≤ file.bytes.length) :
    let first := fill (readOnly capacity) file cache firstSlot firstPage
    let firstThenSecond := fill (readOnly capacity) first.file first.cache secondSlot secondPage
    let second := fill (readOnly capacity) file cache secondSlot secondPage
    let secondThenFirst := fill (readOnly capacity) second.file second.cache firstSlot firstPage
    firstThenSecond.cache = secondThenFirst.cache ∧
      firstThenSecond.file = secondThenFirst.file ∧
      first.result = secondThenFirst.result ∧ firstThenSecond.result = second.result ∧
      (first.trace ++ firstThenSecond.trace).reverse = second.trace ++ secondThenFirst.trace :=
  Proofs.Machine.SqliteVfs.PageRead.Order.readOnly_two_fill_orders capacity file cache
    firstSlot secondSlot firstPage secondPage different firstOwned secondOwned
    firstAdmitted secondAdmitted firstLive secondLive firstComplete secondComplete

end Silmaril.Machine.SqliteVfs.PageRead.Order
