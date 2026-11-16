module

public import Mathlib.Algebra.Group.Nat.Even

/-!
# Incremental acceptors: proofs for the examples

Proofs for `Silmaril.Semantics.Acceptors.Examples`. Nothing imports this module except
that file.
-/

public section

namespace Silmaril.Proofs.Semantics.Acceptors

universe u

/-- Flipping a bit at every occurrence of `a` computes the parity of the count of `a`. -/
theorem foldl_flip_count {α : Type u} [DecidableEq α] (a : α) (w : List α) (s : Bool) :
    w.foldl (fun s b => if b = a then !s else s) s = (s ^^ !decide (Even (w.count a))) := by
  induction w generalizing s with
  | nil => cases s <;> simp
  | cons b w ih =>
    rw [List.foldl_cons, ih, List.count_cons]
    by_cases hb : b = a <;> cases s <;> simp [hb, Nat.even_add_one]

end Silmaril.Proofs.Semantics.Acceptors
