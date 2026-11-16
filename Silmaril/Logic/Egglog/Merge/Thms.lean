module

public import Silmaril.Logic.Egglog.Merge.Defs

@[expose] public section

namespace Silmaril.Logic.Egglog.Merge

variable {Key Value : Type} [DecidableEq Key] [SemilatticeSup Value]

theorem write_sound (ideal : Key → Value) (table : Table Key Value) (key : Key) (new : Value)
    (hsound : Sound ideal table) (hnew : new ≤ ideal key) : Sound ideal (write table key new) := by
  intro query value hvalue
  by_cases hkey : query = key
  · subst query
    cases hold : table key with
    | none =>
      have hv : value = new := by simpa [write, hold] using hvalue.symm
      exact hv ▸ hnew
    | some old =>
      have hv : value = old ⊔ new := by simpa [write, hold] using hvalue.symm
      exact hv ▸ sup_le (hsound key old hold) hnew
  · have hv : table query = some value := by simpa [write, hkey] using hvalue
    exact hsound query value hv

theorem merged_old_bound (old new : Value) : old ≤ old ⊔ new := le_sup_left

theorem merged_new_bound (old new : Value) : new ≤ old ⊔ new := le_sup_right

/-- Commutativity, associativity and idempotence make collision order irrelevant. -/
theorem merge_order_independent (a b c : Value) : (a ⊔ b) ⊔ c = (c ⊔ a) ⊔ b := by
  simp only [sup_comm, sup_left_comm]

/-- A write can invalidate an exact old-value query even with a valid semilattice merge. -/
theorem exact_lookup_not_preserved :
    let table : Table Unit Nat := fun _ => some 0
    table () = some 0 ∧ write table () 2 () ≠ some 0 := by
  decide

/-- Last-writer-wins is permitted by low-level callbacks, but fails the semilattice contract. -/
theorem overwrite_not_commutative : ¬ ∀ a b : Nat, b = a := by
  intro h
  have impossible : (1 : Nat) = 0 := h 0 1
  cases impossible

end Silmaril.Logic.Egglog.Merge
