module

import Silmaril.Machine.SqliteVfs.PageRead.NextPage.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.NextPage

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private def firstPage : Page := ⟨⟨0⟩, 1, 2⟩
private def nextPage : Page := ⟨⟨0⟩, 2, 2⟩
private def slots : Cache := fun slot => if slot = 0 ∨ slot = 1 then some .vacant else none
private def file : FileState := ⟨[2, 10, 30, 40], some .readOnly, 0⟩
private def shortFile : FileState := ⟨[2], some .readOnly, 0⟩
private def select (bytes : Bytes) : Option Page :=
  if bytes.head? = some 2 then some nextPage else none

example : let first := fill (readOnly 8) file slots 0 firstPage
    (fillFollowing (readOnly 8) first 1 select).map Outcome.result = some (.ok [30, 40]) := rfl

example : let first := fill (readOnly 8) shortFile slots 0 firstPage
    first.trace = [⟨firstPage.request, .shortRead [2, 0]⟩] ∧
      select [2, 0] = some nextPage ∧ fillFollowing (readOnly 8) first 1 select = none :=
  ⟨rfl, rfl, rfl⟩

#print axioms fillFollowing_skips_rejected
#print axioms fillFollowing_skips_unselected
#print axioms fillFollowing_trace
#print axioms readOnly_selected_full_fills

end Silmaril.Machine.SqliteVfs.PageRead.NextPage
