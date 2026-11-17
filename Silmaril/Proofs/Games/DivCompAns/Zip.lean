module

public import Silmaril.Games.Zip.Defs

/-!
# The synchronised and the visible moves of an interaction

See `Silmaril.Games.DivCompAns.Defs`: a move of the upper trace on the shared alphabet is a move
of the lower trace there (they synchronise), and a move of the lower trace on its own alphabet is
visible.
-/

public section

namespace Silmaril.Proofs.Games.DivCompAns

open Silmaril.Games

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- A shared move of the upper trace is a shared move of the lower trace. -/
theorem zip_inl_mem_right {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) {x : β} (hx : Sum.inl x ∈ t) : Sum.inr x ∈ s := by
  induction h with
  | nil => simp at hx
  | left a _ ih => exact List.mem_cons_of_mem _ (ih hx)
  | right c _ ih =>
    rcases List.mem_cons.1 hx with hx | hx
    · cases hx
    · exact ih hx
  | sync b _ ih =>
    rcases List.mem_cons.1 hx with hx | hx
    · cases hx; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hx)

/-- A move of the lower trace on its own alphabet is visible. -/
theorem zip_inl_mem_left {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) {x : α} (hx : Sum.inl x ∈ s) : Sum.inl x ∈ p := by
  induction h with
  | nil => simp at hx
  | left a _ ih =>
    rcases List.mem_cons.1 hx with hx | hx
    · cases hx; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hx)
  | right c _ ih => exact List.mem_cons_of_mem _ (ih hx)
  | sync b _ ih =>
    rcases List.mem_cons.1 hx with hx | hx
    · cases hx
    · exact ih hx

end Silmaril.Proofs.Games.DivCompAns
