module

public import Silmaril.Logic.Matching.FirstOrder.Predicate.Defs

@[expose] public section
namespace Silmaril.Logic.Matching.FirstOrder
open Algebraic.ManySorted (Signature)
variable {S : Type} {A : Signature S} {k : Nat} {Γ : Fin k → S} {s : S}

theorem Model.denote_disj (M : Model A) (v : (i : Fin k) → M.carrier (Γ i))
    (p q : Pattern A Γ s) : M.denote v (p.disj q) = M.denote v p ∪ M.denote v q := by
  simp [Pattern.disj, Model.denote]

namespace IsPredicateIn
variable {M : Model A} {p q : Pattern A Γ s}

theorem top : IsPredicateIn M (Pattern.top (Γ := Γ) (s := s)) :=
  fun v => Or.inl (M.denote_top v)

theorem bottom : IsPredicateIn M (Pattern.bottom (Γ := Γ) (s := s)) :=
  fun v => Or.inr (M.denote_bottom v)

theorem neg (hp : IsPredicateIn M p) : IsPredicateIn M (.neg p) := by
  intro v
  rcases hp v with full | empty
  · exact Or.inr (by change (M.denote v p)ᶜ = ∅; rw [full, Set.compl_univ])
  · exact Or.inl (by change (M.denote v p)ᶜ = Set.univ; rw [empty, Set.compl_empty])

theorem conj (hp : IsPredicateIn M p) (hq : IsPredicateIn M q) :
    IsPredicateIn M (.conj p q) := by
  intro v
  change M.denote v p ∩ M.denote v q = Set.univ ∨ M.denote v p ∩ M.denote v q = ∅
  rcases hp v with full | empty
  · simpa only [full, Set.univ_inter] using hq v
  · exact Or.inr (by rw [empty, Set.empty_inter])

theorem disj (hp : IsPredicateIn M p) (hq : IsPredicateIn M q) :
    IsPredicateIn M (p.disj q) := (hp.neg.conj hq.neg).neg

/-- The result sort and the quantified-variable sort are independent. -/
theorem ex (bound : S) {body : Pattern A (Fin.cases bound Γ) s}
    (hbody : IsPredicateIn M body) : IsPredicateIn M (.ex bound body) := by
  classical
  intro v
  by_cases existsFull : ∃ x : M.carrier bound, M.denote (Fin.cases x v) body = Set.univ
  · obtain ⟨x, full⟩ := existsFull
    left
    ext result
    exact ⟨fun _ => trivial, fun _ => ⟨x, full ▸ Set.mem_univ result⟩⟩
  · have empty : ∀ x : M.carrier bound, M.denote (Fin.cases x v) body = ∅ := by
      intro x
      exact (hbody (Fin.cases x v)).resolve_left (fun full => existsFull ⟨x, full⟩)
    right
    ext result
    change (∃ x, result ∈ M.denote (Fin.cases x v) body) ↔ False
    constructor
    · rintro ⟨x, member⟩
      have impossible : result ∈ (∅ : Set (M.carrier s)) := (empty x) ▸ member
      exact impossible
    · exact False.elim

/-- With a singleton result carrier every pattern is a predicate in the model. -/
theorem of_subsingleton (M : Model A) [Subsingleton (M.carrier s)]
    (p : Pattern A Γ s) : IsPredicateIn M p := by
  classical
  intro v
  by_cases inhabited : ∃ x, x ∈ M.denote v p
  · obtain ⟨x, member⟩ := inhabited
    left
    ext result
    exact ⟨fun _ => trivial, fun _ => Subsingleton.elim x result ▸ member⟩
  · right
    ext x
    exact ⟨fun member => inhabited ⟨x, member⟩, False.elim⟩
end IsPredicateIn

namespace IsPredicate
variable {p q : Pattern A Γ s}
theorem top : IsPredicate (Pattern.top (A := A) (Γ := Γ) (s := s)) := fun _ => IsPredicateIn.top
theorem bottom : IsPredicate (Pattern.bottom (A := A) (Γ := Γ) (s := s)) := fun _ => IsPredicateIn.bottom
theorem neg (hp : IsPredicate p) : IsPredicate (.neg p) := fun M => (hp M).neg
theorem conj (hp : IsPredicate p) (hq : IsPredicate q) : IsPredicate (.conj p q) :=
  fun M => (hp M).conj (hq M)
theorem disj (hp : IsPredicate p) (hq : IsPredicate q) : IsPredicate (p.disj q) :=
  fun M => (hp M).disj (hq M)
theorem ex (bound : S) {body : Pattern A (Fin.cases bound Γ) s}
    (hbody : IsPredicate body) : IsPredicate (.ex bound body) := fun M => (hbody M).ex bound
end IsPredicate
end Silmaril.Logic.Matching.FirstOrder
