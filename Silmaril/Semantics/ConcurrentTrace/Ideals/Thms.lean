module

public import Silmaril.Semantics.ConcurrentTrace.Ideals.Defs
import Silmaril.Proofs.Semantics.ConcurrentTrace.Ideals.Basic

public section

namespace Silmaril.Semantics.ConcurrentTrace.Ideals

open Order

variable {E R F S M N : Type*} [Preorder M] [Preorder N]

theorem mem_prefixIdeal (q : WordMap E M) (s : PartialSequence E R) (x : M) :
    x ∈ prefixIdeal q s ↔ ∃ n, x ≤ q (s.cut n) :=
  Iff.rfl

/-- The generating chain is cofinal in its ideal. This is a condition on the image
of the sequence construction, even when the ambient order has other ideals. -/
theorem prefixIdeal_has_cofinal_sequence (q : WordMap E M) (s : PartialSequence E R) :
    ∃ c : Nat →o M, (∀ n, c n ∈ prefixIdeal q s) ∧
      ∀ x ∈ prefixIdeal q s, ∃ n, x ≤ c n :=
  ⟨⟨fun n => q (s.cut n), fun _ _ h => q.preservesPrefix (s.prefix_mono h)⟩,
    fun n => ⟨n, le_rfl⟩, fun _ hx => hx⟩

/-- Inclusion is cofinal domination of the finite quotient prefixes. -/
theorem prefixIdeal_le_iff (q : WordMap E M) (s t : PartialSequence E R) :
    prefixIdeal q s ≤ prefixIdeal q t ↔ ∀ n, ∃ m, q (s.cut n) ≤ q (t.cut m) :=
  Proofs.Semantics.ConcurrentTrace.Ideals.prefixIdeal_le_iff q s t

/-- Agreement on arbitrarily large cuts suffices for equal ideals. -/
theorem prefixIdeal_eq_of_cofinal_eq (q : WordMap E M) (s t : PartialSequence E R)
    (h : ∀ n, ∃ m, n ≤ m ∧ q (s.cut m) = q (t.cut m)) :
    prefixIdeal q s = prefixIdeal q t :=
  Proofs.Semantics.ConcurrentTrace.Ideals.prefixIdeal_eq_of_cofinal_eq q s t h

@[simp] theorem prefixIdeal_finite (q : WordMap E M) (w : List E) (r : Option R) :
    prefixIdeal q (PartialSequence.finite w r) = Ideal.principal (q w) :=
  Proofs.Semantics.ConcurrentTrace.Ideals.prefixIdeal_finite q w r

/-- A length-preserving quotient keeps infinite sequences distinct from finite observations. -/
theorem prefixIdeal_infinite_ne_principal (q : WordMap E M) (rank : M →o Nat)
    (length_eq : ∀ w, rank (q w) = w.length) (f : Nat → E) (x : M) :
    prefixIdeal q (.infinite f : PartialSequence E R) ≠ Ideal.principal x :=
  Proofs.Semantics.ConcurrentTrace.Ideals.prefixIdeal_infinite_ne_principal q rank length_eq f x

/-- The ideal observation is natural for relabellings that preserve the finite interpretation. -/
theorem prefixIdeal_map (q : WordMap E M) (q' : WordMap F N)
    (f : E → F) (g : R → S) (h : M →o N) (comm : ∀ w, q' (w.map f) = h (q w))
    (s : PartialSequence E R) :
    prefixIdeal q' (s.map f g) = lowerImage h (prefixIdeal q s) :=
  Proofs.Semantics.ConcurrentTrace.Ideals.prefixIdeal_map q q' f g h comm s

namespace Trace

variable {q : WordMap E M}

/-- The quotient embeds into the ambient ideals equipped with completion information. -/
theorem observe_injective : Function.Injective (observe (q := q) (R := R)) :=
  Proofs.Semantics.ConcurrentTrace.Ideals.observe_injective q

/-- Quotient equality is mutual cofinal domination and equality of optional results.
Each cut may be matched by a different, possibly longer cut of the other sequence. -/
theorem ofSequence_eq_iff (q : WordMap E M) (s t : PartialSequence E R) :
    ofSequence q s = ofSequence q t ↔
      ((∀ n, ∃ m, q (s.cut n) ≤ q (t.cut m)) ∧
       (∀ n, ∃ m, q (t.cut n) ≤ q (s.cut m))) ∧ s.completion = t.completion := by
  rw [← observe_injective.eq_iff]
  change (_, _) = (_, _) ↔ _
  rw [Prod.mk.injEq, le_antisymm_iff, prefixIdeal_le_iff, prefixIdeal_le_iff]

/-- Relabel a quotient trace along a commuting square of finite interpretations. -/
@[expose] def map (q : WordMap E M) (q' : WordMap F N) (f : E → F) (g : R → S)
    (h : M →o N) (comm : ∀ w, q' (w.map f) = h (q w)) (t : Trace q R) : Trace q' S :=
  Quotient.liftOn t (fun s => ofSequence q' (s.map f g)) (by
    intro s t eq
    apply Quotient.sound
    change observation q s = observation q t at eq
    simpa [observation, prefixIdeal_map _ _ _ _ _ comm] using
      congrArg (fun p : Order.Ideal M × Option R => (lowerImage h p.1, p.2.map g)) eq)

@[simp] theorem observe_map (q : WordMap E M) (q' : WordMap F N) (f : E → F) (g : R → S)
    (h : M →o N) (comm : ∀ w, q' (w.map f) = h (q w)) (t : Trace q R) :
    (map q q' f g h comm t).observe = (lowerImage h t.observe.1, t.observe.2.map g) := by
  induction t using Quotient.inductionOn with
  | _ s => exact Prod.ext (prefixIdeal_map q q' f g h comm s) (s.completion_map f g)

/-- Include a finite quotient word, with the same optional result. -/
@[expose] def ofFinite (q : WordMap E M) (word : FiniteWord q) (result : Option R) : Trace q R :=
  Quotient.liftOn word (fun w => ofSequence q (PartialSequence.finite w result)) (by
    intro w v h
    apply Quotient.sound
    change q w = q v at h
    simp [observation, h])

variable {P : Type*} [PartialOrder P]

/-- Finite representatives have equal traces exactly when their classes and results agree. -/
theorem ofSequence_finite_eq_iff (q : WordMap E P) (w v : List E) (r s : Option R) :
    ofSequence q (PartialSequence.finite w r) = ofSequence q (PartialSequence.finite v s) ↔
      q w = q v ∧ r = s :=
  Proofs.Semantics.ConcurrentTrace.Ideals.finite_eq_iff q w v r s

/-- Finite inclusion preserves and reflects finite quotient equality and completion. -/
theorem ofFinite_injective (q : WordMap E P) :
    Function.Injective (fun p : FiniteWord q × Option R => ofFinite q p.1 p.2) :=
  fun ⟨w, r⟩ ⟨v, s⟩ => Quotient.inductionOn₂ w v fun w v h =>
    let ⟨hw, hr⟩ := (ofSequence_finite_eq_iff q w v r s).1 h
    Prod.ext (Quotient.sound hw) hr

end Trace
end Silmaril.Semantics.ConcurrentTrace.Ideals
