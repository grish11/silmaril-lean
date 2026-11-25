module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Machine.SqliteVfs.PageRead.Pair.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.Order

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.Pair

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
      (first.trace ++ firstThenSecond.trace).reverse = second.trace ++ secondThenFirst.trace := by
  obtain ⟨firstResult, thenSecondResult, firstFile, firstCache, firstTrace, _⟩ :=
    readOnly_two_full_fills capacity file cache firstSlot secondSlot firstPage secondPage
      different firstOwned secondOwned firstAdmitted secondAdmitted firstLive secondLive
      firstComplete secondComplete
  obtain ⟨secondResult, thenFirstResult, secondFile, secondCache, secondTrace, _⟩ :=
    readOnly_two_full_fills capacity file cache secondSlot firstSlot secondPage firstPage
      (Ne.symm different) secondOwned firstOwned secondAdmitted firstAdmitted secondLive firstLive
      secondComplete firstComplete
  dsimp only
  refine ⟨?_, firstFile.trans secondFile.symm, firstResult.trans thenFirstResult.symm,
    thenSecondResult.trans secondResult.symm, ?_⟩
  · rw [firstCache, secondCache]
    funext slot
    by_cases atFirst : slot = firstSlot
    · subst slot
      simp [Cache.install, Ne.symm different]
    · simp [Cache.install, atFirst]
  · rw [firstTrace, secondTrace]
    rfl

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.Order
