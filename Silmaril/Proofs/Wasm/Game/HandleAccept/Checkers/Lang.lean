module

public import Silmaril.Wasm.Game.HandleAccept.Checkers.Defs

/-!
# Reader checkers: the languages

`SpineProperList` is `∃ xs, x = SExp2.ofList xs` (`spineProperList_iff`), and every recursively
proper list (`SExp2.ProperList`) is spine-proper (`spineProperList_of_properList`).

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers

open Silmaril.Formats Silmaril.Wasm.Game.HandleAccept.Checkers

variable {α : Type}

theorem spineProperList_iff {x : SExp2 α} : SpineProperList x ↔ ∃ xs, x = SExp2.ofList xs := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨[], rfl⟩
    | cons x _ ih =>
      obtain ⟨xs, rfl⟩ := ih
      exact ⟨x :: xs, rfl⟩
  · rintro ⟨xs, rfl⟩
    induction xs with
    | nil => exact .nil
    | cons x xs ih => exact .cons x ih

theorem spineProperList_of_proper {k : SExp2.ProperKind} {x : SExp2 α} (h : SExp2.Proper k x)
    (hk : k = .list) : SpineProperList x := by
  induction h with
  | atom => cases hk
  | nil => exact .nil
  | cons _ _ _ ihd => exact .cons _ (ihd rfl)

theorem spineProperList_of_properList {x : SExp2 α} (h : SExp2.ProperList x) :
    SpineProperList x :=
  spineProperList_of_proper h rfl

end Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
