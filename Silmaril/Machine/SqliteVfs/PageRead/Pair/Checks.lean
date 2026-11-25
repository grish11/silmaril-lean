module

import Silmaril.Machine.SqliteVfs.PageRead.Pair.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.Pair

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private def file : FileState := ⟨[10, 20, 30, 40], some .readOnly, 0⟩
private def firstPage : Page := ⟨⟨0⟩, 1, 2⟩
private def secondPage : Page := ⟨⟨0⟩, 2, 2⟩
private def cache : Cache := fun slot => if slot = 0 ∨ slot = 1 then some .vacant else none

example :
    let first := fill (readOnly 8) file cache 0 firstPage
    let second := fill (readOnly 8) first.file first.cache 1 secondPage
    second.cache 0 = some (.resident firstPage [10, 20]) ∧
      second.cache 1 = some (.resident secondPage [30, 40]) ∧
      (first.trace ++ second.trace).length = 2 := by
  have both := readOnly_two_full_fills 8 file cache 0 1 firstPage secondPage
    (by decide) rfl rfl (by decide) (by decide) rfl rfl (by decide) (by decide)
  dsimp only at both ⊢
  rw [both.2.2.2.1, both.2.2.2.2.1]
  exact ⟨rfl, rfl, rfl⟩

#print axioms readOnly_two_full_fills

end Silmaril.Machine.SqliteVfs.PageRead.Pair
