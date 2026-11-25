module

import Silmaril.Machine.SqliteVfs.PageRead.Order.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.Order

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private def file : FileState := ⟨[10, 20, 30, 40], some .readOnly, 0⟩
private def firstPage : Page := ⟨⟨0⟩, 1, 2⟩
private def secondPage : Page := ⟨⟨0⟩, 2, 2⟩
private def cache : Cache := fun slot => if slot = 0 ∨ slot = 1 then some .vacant else none

example :
    let first := fill (readOnly 8) file cache 0 firstPage
    let firstThenSecond := fill (readOnly 8) first.file first.cache 1 secondPage
    let second := fill (readOnly 8) file cache 1 secondPage
    let secondThenFirst := fill (readOnly 8) second.file second.cache 0 firstPage
    firstThenSecond.cache = secondThenFirst.cache ∧
      (first.trace ++ firstThenSecond.trace).map Exchange.request = [firstPage.request, secondPage.request] ∧
      (second.trace ++ secondThenFirst.trace).map Exchange.request = [secondPage.request, firstPage.request] := by
  have both := readOnly_two_fill_orders 8 file cache 0 1 firstPage secondPage
    (by decide) rfl rfl (by decide) (by decide) rfl rfl (by decide) (by decide)
  exact ⟨both.1, rfl, rfl⟩

#print axioms readOnly_two_fill_orders

end Silmaril.Machine.SqliteVfs.PageRead.Order
