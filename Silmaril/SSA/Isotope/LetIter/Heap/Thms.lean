module

public import Silmaril.SSA.Isotope.LetIter.Heap.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Heap.Transport

public section

namespace Silmaril.Isotope.LetIter.Heap

open Silmaril.Elgot

universe v

variable {I J : Type} {A B : Type v}

@[simp] theorem storeEquiv_lookup (e : I ≃ J) (s : Store I) (i : I) :
    storeEquiv e s (e i) = Equiv.optionCongr (valueEquiv e) (s i) :=
  Silmaril.Proofs.LetIter.Heap.lookup e s i

theorem fresh_iff (e : I ≃ J) (s : Store I) (i : I) :
    storeEquiv e s (e i) = none ↔ s i = none := by
  rw [storeEquiv_lookup]
  change Equiv.optionCongr (valueEquiv e) (s i) = Equiv.optionCongr (valueEquiv e) none ↔ _
  exact (Equiv.optionCongr (valueEquiv e)).injective.eq_iff

@[simp] theorem storeEquiv_empty (e : I ≃ J) :
    storeEquiv e (emptyStore I) = emptyStore J := rfl

theorem write_transport (e : I ≃ J) (s : Store I) (i : I) (v : Option (Value I)) :
    storeEquiv e (write s i v) =
      write (storeEquiv e s) (e i) (Equiv.optionCongr (valueEquiv e) v) :=
  Silmaril.Proofs.LetIter.Heap.write_transport e s i v

/-- Every fresh index is a legal allocation reply, and every legal reply is fresh. -/
theorem alloc_reply_iff (s : Store I) (v : Value I) (i : I) :
    (∃ t, step ⟨I, allocEvent v⟩ s i t) ↔ s i = none :=
  ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨write s i (some v), h, rfl⟩⟩

theorem alloc_preserves_other_cells {s t : Store I} {v : Value I} {i j : I}
    (h : step ⟨I, allocEvent v⟩ s i t) (hj : j ≠ i) : t j = s j := by
  classical
  rw [h.2, write]
  exact Function.update_of_ne hj _ _

theorem step_equivariant (e : I ≃ J) (q : ITree.Request (Event I))
    (s : Store I) (r : q.1) (t : Store I) :
    step ((signatureEquiv e).request q) (storeEquiv e s) ((signatureEquiv e).reply q r)
      (storeEquiv e t) ↔ step q s r t :=
  Silmaril.Proofs.LetIter.Heap.step_transport e q s r t

/-- The trace membership square for heap-handled native LetIter denotations
and other trees over the same typed instruction signature. -/
theorem trace_equivariant (e : I ≃ J) (a : A ≃ B) (s : Store I)
    (t : ITree.Tree (Event I) A) (p : ITree.Trace (Event I) A) :
    ITree.HandledTrace step (storeEquiv e s) ((signatureEquiv e).tree a t)
      ((signatureEquiv e).trace a p) ↔ ITree.HandledTrace step s t p :=
  (signatureEquiv e).handledTrace_iff a (storeEquiv e) (step_equivariant e) s t p

/-- Every admitted target observation is the renaming of an admitted
source observation, including prefixes with a pending request. -/
theorem trace_image (e : I ≃ J) (a : A ≃ B) (s : Store I)
    (t : ITree.Tree (Event I) A) (p' : ITree.Trace (Event J) B) :
    ITree.HandledTrace step (storeEquiv e s) ((signatureEquiv e).tree a t) p' ↔
      ∃ p, ITree.HandledTrace step s t p ∧ (signatureEquiv e).trace a p = p' :=
  (signatureEquiv e).handledTrace_image a (storeEquiv e) (step_equivariant e) s t p'

/-- A permutation preserving both the store and the program denotation
preserves that program's trace language. The empty store is fixed by all
permutations. -/
theorem trace_fixed_iff (e : Reindex.Aut I) (a : Reindex.Aut A) (s : Store I)
    (t : ITree.Tree (Event I) A) (hs : storeEquiv e s = s)
    (ht : (signatureEquiv e).tree a t = t) (p : ITree.Trace (Event I) A) :
    ITree.HandledTrace step s t ((signatureEquiv e).trace a p) ↔
      ITree.HandledTrace step s t p := by
  simpa only [hs, ht] using trace_equivariant e a s t p

end Silmaril.Isotope.LetIter.Heap
