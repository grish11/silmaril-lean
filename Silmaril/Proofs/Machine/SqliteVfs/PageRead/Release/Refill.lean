module

public import Silmaril.Machine.SqliteVfs.PageRead.Release.Defs
import Silmaril.Machine.SqliteVfs.PageRead.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.Release

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.Release

theorem release_resident {cache : Cache} {target : SlotId} {page : Page} {bytes : Bytes}
    (stored : cache target = some (.resident page bytes)) :
    release cache target page =
      .ok (fun slot => if slot = target then some .vacant else cache slot) := by
  simp [release, stored]

theorem release_mismatch {cache : Cache} {target : SlotId} {resident expected : Page}
    {bytes : Bytes} (stored : cache target = some (.resident resident bytes))
    (different : resident ≠ expected) :
    release cache target expected = .error .pageMismatch := by
  simp [release, stored, different]

theorem release_after_fill_success {State : Type} (handler : Handler State) (file : State)
    (cache : Cache) (target : SlotId) (page : Page) {bytes : Bytes}
    (success : (fill handler file cache target page).result = .ok bytes) :
    release (fill handler file cache target page).cache target page = .ok cache := by
  obtain ⟨owned, _, stored⟩ := fill_success handler file cache target page success
  rw [release_resident stored]
  apply congrArg Except.ok
  funext slot
  by_cases selected : slot = target
  · subst slot
    simp [owned]
  · exact (ite_eq_right selected).trans (fill_other handler file cache target page slot selected)

theorem readOnly_release_and_refill (capacity : Nat) (file : FileState) (cache : Cache)
    (target : SlotId) (firstPage nextPage : Page) (owned : cache target = some .vacant)
    (firstAdmitted : firstPage.Admitted) (nextAdmitted : nextPage.Admitted)
    (firstLive : (file.mode firstPage.handle).isNone = false)
    (nextLive : (file.mode nextPage.handle).isNone = false)
    (firstComplete : firstPage.offset + firstPage.size ≤ file.bytes.length)
    (nextComplete : nextPage.offset + nextPage.size ≤ file.bytes.length) :
    let firstBytes := readBytes file.bytes firstPage.offset firstPage.size
    let nextBytes := readBytes file.bytes nextPage.offset nextPage.size
    let first := fill (readOnly capacity) file cache target firstPage
    let next := fill (readOnly capacity) first.file cache target nextPage
    first = ⟨.ok firstBytes, file, cache.install target firstPage firstBytes,
        [⟨firstPage.request, .ok firstBytes⟩]⟩ ∧
      release first.cache target firstPage = .ok cache ∧
      next = ⟨.ok nextBytes, file, cache.install target nextPage nextBytes,
        [⟨nextPage.request, .ok nextBytes⟩]⟩ ∧
      Trace.Valid (readOnly capacity) file (first.trace ++ next.trace) next.file := by
  let firstBytes := readBytes file.bytes firstPage.offset firstPage.size
  let nextBytes := readBytes file.bytes nextPage.offset nextPage.size
  let first := fill (readOnly capacity) file cache target firstPage
  have firstEq : first = ⟨.ok firstBytes, file, cache.install target firstPage firstBytes,
      [⟨firstPage.request, .ok firstBytes⟩]⟩ := by
    simpa only [firstComplete, ite_true] using
      readOnly_fill capacity file cache target firstPage owned firstAdmitted firstLive
  have reused := release_after_fill_success (readOnly capacity) file cache target firstPage
    (congrArg Outcome.result firstEq)
  have nextEq : fill (readOnly capacity) file cache target nextPage =
      ⟨.ok nextBytes, file, cache.install target nextPage nextBytes,
        [⟨nextPage.request, .ok nextBytes⟩]⟩ := by
    simpa only [nextComplete, ite_true] using
      readOnly_fill capacity file cache target nextPage owned nextAdmitted nextLive
  have after : first.file = file := congrArg Outcome.file firstEq
  have nextValid := fill_trace (readOnly capacity) file cache target nextPage
  have firstValid : Trace.Valid (readOnly capacity) file first.trace first.file :=
    fill_trace (readOnly capacity) file cache target firstPage
  refine ⟨firstEq, reused, ?_, ?_⟩
  · rw [after]
    exact nextEq
  · change Trace.Valid (readOnly capacity) file
      (first.trace ++ (fill (readOnly capacity) first.file cache target nextPage).trace)
      (fill (readOnly capacity) first.file cache target nextPage).file
    rw [after, firstEq]
    rw [firstEq] at firstValid
    cases firstValid with
    | cons step tail =>
      cases tail
      exact .cons step nextValid

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.Release
