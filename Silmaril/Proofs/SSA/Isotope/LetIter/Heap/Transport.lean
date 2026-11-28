module

public import Silmaril.SSA.Isotope.LetIter.Heap.Defs

public section

namespace Silmaril.Proofs.LetIter.Heap

open Silmaril.Isotope.LetIter.Heap Silmaril.Isotope.Semantics Silmaril.Elgot


variable {I J : Type}

theorem lookup (e : I ≃ J) (s : Store I) (i : I) :
    storeEquiv e s (e i) = Equiv.optionCongr (valueEquiv e) (s i) := by
  change Equiv.optionCongr (valueEquiv e) (s (e.symm (e i))) = _
  rw [Equiv.symm_apply_apply]

theorem write_transport (e : I ≃ J) (s : Store I) (i : I) (v : Option (Value I)) :
    storeEquiv e (write s i v) =
      write (storeEquiv e s) (e i) (Equiv.optionCongr (valueEquiv e) v) := by
  classical
  funext j
  obtain ⟨j, rfl⟩ := e.surjective j
  by_cases h : j = i
  · subst j
    simp only [lookup, write, Function.update_self]
  · have h' : e j ≠ e i := fun hij => h (e.injective hij)
    rw [lookup, write, Function.update_of_ne h, write, Function.update_of_ne h', lookup]

theorem step_transport (e : I ≃ J) (q : ITree.Request (Event I)) (s : Store I)
    (r : q.1) (t : Store I) :
    step ((signatureEquiv e).request q) (storeEquiv e s) ((signatureEquiv e).reply q r)
      (storeEquiv e t) ↔ step q s r t := by
  rcases q with ⟨_, ⟨f, x⟩⟩
  let map := Equiv.optionCongr (valueEquiv e)
  cases f
  · change Value I at x
    change I at r
    change (storeEquiv e s (e r) = map none ∧
        storeEquiv e t = write (storeEquiv e s) (e r) (map (some x))) ↔ _
    rw [lookup, ← write_transport]
    exact and_congr map.injective.eq_iff (storeEquiv e).injective.eq_iff
  · change I at x
    change Value I at r
    change (storeEquiv e s (e x) = map (some r) ∧ storeEquiv e t = storeEquiv e s) ↔ _
    rw [lookup]
    exact and_congr map.injective.eq_iff (storeEquiv e).injective.eq_iff
  · change I × Value I at x
    rcases x with ⟨i, v⟩
    change (storeEquiv e s (e i) ≠ map none ∧
        storeEquiv e t = write (storeEquiv e s) (e i) (map (some v))) ↔ _
    rw [lookup, ← write_transport]
    exact and_congr (not_congr map.injective.eq_iff) (storeEquiv e).injective.eq_iff
  · change I at x
    change (storeEquiv e s (e x) ≠ map none ∧
        storeEquiv e t = write (storeEquiv e s) (e x) (map none)) ↔ _
    rw [lookup, ← write_transport]
    exact and_congr (not_congr map.injective.eq_iff) (storeEquiv e).injective.eq_iff

end Silmaril.Proofs.LetIter.Heap
