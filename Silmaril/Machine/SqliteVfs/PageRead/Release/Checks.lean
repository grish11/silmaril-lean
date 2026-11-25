module

import Silmaril.Machine.SqliteVfs.PageRead.Release.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.Release

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private def file : FileState := ⟨[10, 20, 30, 40], some .readOnly, 0⟩
private def firstPage : Page := ⟨⟨0⟩, 1, 2⟩
private def nextPage : Page := ⟨⟨0⟩, 2, 2⟩
private def cache : Cache := fun slot => if slot = 0 then some .vacant else none

example : release cache 0 firstPage = .error .unavailableSlot ∧
    release cache 1 firstPage = .error .unavailableSlot :=
  ⟨rfl, rfl⟩

example :
    let first := fill (readOnly 8) file cache 0 firstPage
    release first.cache 0 nextPage = .error .pageMismatch := rfl

example :
    let first := fill (readOnly 8) file cache 0 firstPage
    release first.cache 0 firstPage = .ok cache ∧
      (fill (readOnly 8) first.file cache 0 nextPage).cache 0 = some (.resident nextPage [30, 40]) := by
  have reused := readOnly_release_and_refill 8 file cache 0 firstPage nextPage rfl
    (by decide) (by decide) rfl rfl (by decide) (by decide)
  exact ⟨reused.2.1, rfl⟩

#print axioms release_resident
#print axioms release_mismatch
#print axioms release_after_fill_success
#print axioms readOnly_release_and_refill

end Silmaril.Machine.SqliteVfs.PageRead.Release
