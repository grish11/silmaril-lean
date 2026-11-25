module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Machine.SqliteVfs.PageRead.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.Pair

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

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
      Trace.Valid (readOnly capacity) file (first.trace ++ second.trace) second.file := by
  let firstBytes := readBytes file.bytes firstPage.offset firstPage.size
  let secondBytes := readBytes file.bytes secondPage.offset secondPage.size
  let nextCache := cache.install firstSlot firstPage firstBytes
  have firstFill : fill (readOnly capacity) file cache firstSlot firstPage =
      ⟨.ok firstBytes, file, nextCache, [⟨firstPage.request, .ok firstBytes⟩]⟩ := by
    simpa only [firstComplete, ite_true] using
      readOnly_fill capacity file cache firstSlot firstPage firstOwned firstAdmitted firstLive
  have nextVacant : nextCache secondSlot = some .vacant := by
    simp [nextCache, Cache.install, different, secondOwned]
  have secondFill : fill (readOnly capacity) file nextCache secondSlot secondPage =
      ⟨.ok secondBytes, file, nextCache.install secondSlot secondPage secondBytes,
        [⟨secondPage.request, .ok secondBytes⟩]⟩ := by
    simpa only [secondComplete, ite_true] using
      readOnly_fill capacity file nextCache secondSlot secondPage nextVacant secondAdmitted secondLive
  have firstTrace := fill_trace (readOnly capacity) file cache firstSlot firstPage
  have secondTrace := fill_trace (readOnly capacity) file nextCache secondSlot secondPage
  dsimp only at firstTrace secondTrace ⊢
  rw [firstFill] at firstTrace
  rw [secondFill] at secondTrace
  rw [firstFill, secondFill]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  cases firstTrace with
  | cons step tail =>
    cases tail
    exact .cons step secondTrace

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.Pair
