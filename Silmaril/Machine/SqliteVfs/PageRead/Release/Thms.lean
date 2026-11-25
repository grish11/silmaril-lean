module

public import Silmaril.Machine.SqliteVfs.PageRead.Release.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.Release.Refill

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.Release

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- Releasing the matching page changes exactly the target to a vacancy. -/
theorem release_resident {cache : Cache} {target : SlotId} {page : Page} {bytes : Bytes}
    (stored : cache target = some (.resident page bytes)) :
    release cache target page =
      .ok (fun slot => if slot = target then some .vacant else cache slot) :=
  Proofs.Machine.SqliteVfs.PageRead.Release.release_resident stored

/-- A different resident page yields the mismatch status. -/
theorem release_mismatch {cache : Cache} {target : SlotId} {resident expected : Page}
    {bytes : Bytes} (stored : cache target = some (.resident resident bytes))
    (different : resident ≠ expected) :
    release cache target expected = .error .pageMismatch :=
  Proofs.Machine.SqliteVfs.PageRead.Release.release_mismatch stored different

/-- Releasing a successfully filled slot recovers the exact input cache. -/
theorem release_after_fill_success {State : Type} (handler : Handler State) (file : State)
    (cache : Cache) (target : SlotId) (page : Page) {bytes : Bytes}
    (success : (fill handler file cache target page).result = .ok bytes) :
    release (fill handler file cache target page).cache target page = .ok cache :=
  Proofs.Machine.SqliteVfs.PageRead.Release.release_after_fill_success handler file cache target page success

/-- Two complete reads can reuse one owned slot through a serial release. -/
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
      Trace.Valid (readOnly capacity) file (first.trace ++ next.trace) next.file :=
  Proofs.Machine.SqliteVfs.PageRead.Release.readOnly_release_and_refill capacity file cache target firstPage nextPage owned
    firstAdmitted nextAdmitted firstLive nextLive firstComplete nextComplete

end Silmaril.Machine.SqliteVfs.PageRead.Release
