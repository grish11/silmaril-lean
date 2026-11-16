module

public import Silmaril.Logic.Matching.FirstOrder.Predicate.Thms
public import Silmaril.Logic.Matching.FirstOrder.Examples

/-! Finite, inhabited models distinguish predicates from arbitrary atoms.
A singleton denotation in Bool is proper; in a singleton carrier it is full. -/

@[expose] public section
namespace Silmaril.Logic.Matching.FirstOrder.PredicateExamples
open Examples

/-- A set-valued atom can denote a nonempty proper subset of its result sort. -/
theorem initial_not_predicate : ¬ IsPredicateIn transitions initial := by
  intro predicate
  rcases predicate (fun i : Fin 0 => nomatch i) with full | empty
  · have full : ({false} : Set Bool) = Set.univ := initial_denotation.symm.trans full
    have member : true ∈ ({false} : Set Bool) := by rw [full]; trivial
    simp at member
  · have empty : ({false} : Set Bool) = ∅ := initial_denotation.symm.trans empty
    have member : false ∈ (∅ : Set Bool) := empty ▸ (show false ∈ ({false} : Set Bool) from rfl)
    exact member

/-- Consequently this syntactic atom is not a predicate in all models. -/
theorem initial_not_universal_predicate : ¬ IsPredicate initial :=
  fun predicate => initial_not_predicate (predicate transitions)

/-- Another pattern in the same two-state model covers the whole carrier. -/
theorem afterOneStep_predicate : IsPredicateIn transitions afterOneStep := by
  intro v
  have same : v = (fun i : Fin 0 => nomatch i) := by funext i; exact Fin.elim0 i
  exact Or.inl (same ▸ afterOneStep_denotation)

/-- Every sort is an actual one-element carrier; operations return its singleton. -/
def singletonModel : Model signature where
  carrier _ := Unit
  nonempty _ := ⟨()⟩
  operation _ _ := {()}

theorem singleton_atom_denotation :
    singletonModel.denote (fun i : Fin 0 => nomatch i) initial = {()} :=
  singletonModel.denote_nullary _ Symbol.initial

/-- A singleton-valued atom can be a predicate when that singleton is the carrier. -/
theorem singleton_atom_predicate : IsPredicateIn singletonModel initial := by
  let : Subsingleton (singletonModel.carrier PUnit.unit) :=
    ⟨fun a b => by cases a; cases b; rfl⟩
  exact IsPredicateIn.of_subsingleton singletonModel initial

/-- info: 'Silmaril.Logic.Matching.FirstOrder.IsPredicateIn.ex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IsPredicateIn.ex
end Silmaril.Logic.Matching.FirstOrder.PredicateExamples
