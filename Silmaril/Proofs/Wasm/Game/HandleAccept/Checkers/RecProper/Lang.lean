module

public import Silmaril.Wasm.Game.HandleAccept.Checkers.RecProper.Defs
public import Silmaril.Wasm.Game.HandleAccept.Checkers.Thms

/-!
# The language of `recProperCheck`

`nestL` lies strictly between the proper lists of words and the recursively proper lists:
`wordsL_subset_nestL`, `nestL_subset_recProperL`; `nested123` separates the first pair and
`deep1 = (((1)))` the second.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers

open Silmaril.Formats Silmaril.Wasm.Game.HandleAccept.Checkers

theorem ofAtoms_properList' (ws : List (BitVec 64)) : SExp2.ProperList (SExp2.ofAtoms ws) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih => exact .cons (.atom w) ih

theorem nestElem_isProper {x : SExp2 (BitVec 64)} (h : NestElem x) : SExp2.IsProper x := by
  rcases h with ⟨w, rfl⟩ | ⟨ws, rfl⟩
  · exact .inl (.atom w)
  · exact .inr (ofAtoms_properList' ws)

theorem nestList_properList {x : SExp2 (BitVec 64)} (h : NestList x) : SExp2.ProperList x := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih =>
    rcases nestElem_isProper hx with h | h
    · exact .cons h ih
    · exact .cons h ih

theorem ofAtoms_nestList (ws : List (BitVec 64)) : NestList (SExp2.ofAtoms ws) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih => exact .cons (.inl ⟨w, rfl⟩) ih

theorem nested123_nestList : NestList nested123 :=
  .cons (.inr ⟨[1, 2], rfl⟩) (.cons (.inl ⟨3, rfl⟩) .nil)

theorem nested123_not_mem_wordsL : nested123 ∉ wordsL := by
  rintro ⟨_ | ⟨w, ws⟩, h⟩
  · cases h
  · injection h with h
    cases h

/-- `(((1)))`: recursively proper, of nesting depth three. -/
theorem deep1_not_nestList :
    ¬ NestList (SExp2.ofList [SExp2.ofList [SExp2.ofAtoms [(1 : BitVec 64)]]]) := by
  intro h
  cases h with
  | cons hx _ =>
    rcases hx with ⟨w, h⟩ | ⟨_ | ⟨w, ws⟩, h⟩
    · cases h
    · cases h
    · injection h with h
      cases h

theorem dottedElem_not_nestList : ¬ NestList dottedElem := by
  intro h
  cases h with
  | cons hx _ =>
    rcases hx with ⟨w, h⟩ | ⟨_ | ⟨w, ws⟩, h⟩
    · cases h
    · cases h
    · injection h with h
      cases h

end Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
