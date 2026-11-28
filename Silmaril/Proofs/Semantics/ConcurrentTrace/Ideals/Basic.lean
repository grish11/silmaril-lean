module

public import Silmaril.Semantics.ConcurrentTrace.Ideals.Defs

public section

namespace Silmaril.Proofs.Semantics.ConcurrentTrace.Ideals

open Silmaril.Semantics.ConcurrentTrace Silmaril.Semantics.ConcurrentTrace.Ideals
open Order

variable {E R F S M N : Type*} [Preorder M] [Preorder N]

theorem prefixIdeal_le_iff (q : WordMap E M) (s t : PartialSequence E R) :
    prefixIdeal q s ≤ prefixIdeal q t ↔ ∀ n, ∃ m, q (s.cut n) ≤ q (t.cut m) := by
  constructor
  · intro h n
    exact h (show q (s.cut n) ∈ prefixIdeal q s from ⟨n, le_rfl⟩)
  · rintro h x ⟨n, hx⟩
    obtain ⟨m, hm⟩ := h n
    exact ⟨m, hx.trans hm⟩

theorem prefixIdeal_finite (q : WordMap E M) (w : List E) (r : Option R) :
    prefixIdeal q (PartialSequence.finite w r) = Ideal.principal (q w) := by
  ext x
  change (∃ n, x ≤ q ((PartialSequence.finite w r).cut n)) ↔ x ≤ q w
  simp only [PartialSequence.prefix_finite]
  exact ⟨fun ⟨n, hn⟩ => hn.trans (q.preservesPrefix (List.take_prefix n w)),
    fun h => ⟨w.length, by simpa using h⟩⟩

theorem prefixIdeal_map (q : WordMap E M) (q' : WordMap F N)
    (f : E → F) (g : R → S) (h : M →o N) (comm : ∀ w, q' (w.map f) = h (q w))
    (s : PartialSequence E R) :
    prefixIdeal q' (s.map f g) = lowerImage h (prefixIdeal q s) := by
  ext y
  change (∃ n, y ≤ q' ((s.map f g).cut n)) ↔ ∃ x ∈ prefixIdeal q s, y ≤ h x
  simp only [PartialSequence.prefix_map, comm]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨q (s.cut n), ⟨n, le_rfl⟩, hn⟩
  · rintro ⟨x, ⟨n, hx⟩, hy⟩
    exact ⟨n, hy.trans (h.monotone hx)⟩

theorem prefixIdeal_eq_of_cofinal_eq (q : WordMap E M) (s t : PartialSequence E R)
    (h : ∀ n, ∃ m, n ≤ m ∧ q (s.cut m) = q (t.cut m)) :
    prefixIdeal q s = prefixIdeal q t := by
  apply le_antisymm
  · refine (prefixIdeal_le_iff q s t).2 fun n => ?_
    obtain ⟨m, hn, he⟩ := h n
    exact ⟨m, he ▸ q.preservesPrefix (s.prefix_mono hn)⟩
  · refine (prefixIdeal_le_iff q t s).2 fun n => ?_
    obtain ⟨m, hn, he⟩ := h n
    exact ⟨m, he.symm ▸ q.preservesPrefix (t.prefix_mono hn)⟩

theorem prefixIdeal_infinite_ne_principal (q : WordMap E M) (rank : M →o Nat)
    (length_eq : ∀ w, rank (q w) = w.length) (f : Nat → E) (x : M) :
    prefixIdeal q (.infinite f : PartialSequence E R) ≠ Ideal.principal x := by
  intro eq
  let n := rank x + 1
  have hm : q ((PartialSequence.infinite f : PartialSequence E R).cut n) ∈
      prefixIdeal q (.infinite f : PartialSequence E R) := ⟨n, le_rfl⟩
  rw [eq, Ideal.mem_principal] at hm
  have hle := rank.monotone hm
  rw [length_eq, PartialSequence.cut, List.length_ofFn] at hle
  exact Nat.not_succ_le_self _ hle

theorem observe_injective (q : WordMap E M) : Function.Injective (Trace.observe (q := q) (R := R)) := by
  intro a b
  induction a using Quotient.inductionOn with
  | _ s =>
    induction b using Quotient.inductionOn with
    | _ t => exact fun h => Quotient.sound h

private theorem principal_injective {P : Type*} [PartialOrder P] :
    Function.Injective (Ideal.principal : P → Ideal P) := by
  intro a b h
  exact le_antisymm (Ideal.mem_principal.1 (h ▸ Ideal.mem_principal_self (x := a)))
    (Ideal.mem_principal.1 (h.symm ▸ Ideal.mem_principal_self (x := b)))

theorem finite_eq_iff {P : Type*} [PartialOrder P] (q : WordMap E P) (w v : List E)
    (r s : Option R) :
    Trace.ofSequence q (PartialSequence.finite w r) =
      Trace.ofSequence q (PartialSequence.finite v s) ↔ q w = q v ∧ r = s := by
  rw [← (observe_injective q).eq_iff]
  change observation q _ = observation q _ ↔ _
  simp only [observation, prefixIdeal_finite, PartialSequence.completion_finite, Prod.mk.injEq,
    principal_injective.eq_iff]

end Silmaril.Proofs.Semantics.ConcurrentTrace.Ideals
