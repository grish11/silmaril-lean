module

public import Silmaril.Logic.Matching.FirstOrder.Thms

/-! Semantic predicates in Roșu (2017), Definition 2.4. A predicate may change
truth value with its valuation; its denotation at each valuation is all or none
of the result carrier. No new primitive patterns are introduced. -/

@[expose] public section
namespace Silmaril.Logic.Matching.FirstOrder
open Algebraic.ManySorted (Signature)
variable {S : Type} {A : Signature S} {k : Nat} {Γ : Fin k → S} {s : S}

/-- A predicate in a fixed model, quantified over all free-variable valuations. -/
def IsPredicateIn (M : Model A) (p : Pattern A Γ s) : Prop :=
  ∀ v : (i : Fin k) → M.carrier (Γ i),
    M.denote v p = Set.univ ∨ M.denote v p = ∅

/-- A semantic predicate in every set-valued matching model of the signature. -/
def IsPredicate (p : Pattern A Γ s) : Prop := ∀ M : Model A, IsPredicateIn M p

/-- Disjunction is derived from negation and conjunction. -/
def Pattern.disj (p q : Pattern A Γ s) : Pattern A Γ s := .neg (.conj (.neg p) (.neg q))
end Silmaril.Logic.Matching.FirstOrder
