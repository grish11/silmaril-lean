module

public import Silmaril.Calculi.PERConstraints.Finite.Defs
public import Silmaril.Calculi.PERConstraints.Thms

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Proofs

open Silmaril.Formats

variable {α Item : Type}

theorem distinct_multiset_coe (model : PER α) (terms : List α) :
    DISTINCTMultiset model (terms : Multiset α) ↔ DISTINCTList model terms := by
  let : Std.Symm (fun left right => ¬model.rel left right) :=
    ⟨fun _ _ unrelated related => unrelated (model.laws.symm related)⟩
  exact and_congr (by simp) Multiset.pairwise_coe_iff_pairwise

theorem dnf_to_cnf (model : PER α) (sentence : DNF α) :
    CNF.Holds model (DNF.toCNF sentence) ↔ DNF.Holds model sentence := by
  classical
  constructor
  · intro satisfies
    by_contra unsatisfied
    have meets : ∀ term ∈ sentence, ∃ bound ∈ term, ¬bound.Holds model := by
      intro term member
      by_contra none
      exact unsatisfied ⟨term, member, fun bound inside => by
        by_contra fails
        exact none ⟨bound, inside, fails⟩⟩
    obtain ⟨bound, fails, holds⟩ := satisfies {bound | ¬bound.Holds model} meets
    exact fails holds
  · rintro ⟨term, member, holds⟩ clause meets
    obtain ⟨bound, inside, chosen⟩ := meets term member
    exact ⟨bound, chosen, holds bound inside⟩

theorem any_all_choices (holds : Item → Prop) (rows : List (List Item)) :
    AnyList (AllList holds) (choices rows) ↔ AllList (AnyList holds) rows := by
  induction rows with
  | nil => simp [choices, AnyList, AllList, Any, All, members]
  | cons row rest ih =>
    have split : AllList (AnyList holds) (row :: rest) ↔ AnyList holds row ∧ AllList (AnyList holds) rest :=
      List.forall_mem_cons
    rw [split, ← ih]
    simp only [choices, AnyList, Any, members, Set.mem_ofPred_eq, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨_, ⟨item, member, tail, chosen, rfl⟩, satisfied⟩
      exact ⟨⟨item, member, satisfied _ (List.mem_cons_self ..)⟩,
        ⟨tail, chosen, fun atom inside => satisfied atom (List.mem_cons_of_mem _ inside)⟩⟩
    · rintro ⟨⟨item, member, satisfied⟩, tail, chosen, all⟩
      refine ⟨item :: tail, ⟨item, member, tail, chosen, rfl⟩, ?_⟩
      intro atom inside
      rcases List.mem_cons.mp inside with rfl | tailMember
      · exact satisfied
      · exact all atom tailMember

theorem all_any_choices (holds : Item → Prop) (rows : List (List Item)) :
    AllList (AnyList holds) (choices rows) ↔ AnyList (AllList holds) rows := by
  classical
  have dual := not_congr (any_all_choices (fun item => ¬holds item) rows)
  simpa only [AnyList, AllList, Any, All, not_exists, not_and, Classical.not_forall, Classical.not_imp,
    exists_prop, not_not] using dual

theorem length_choices (rows : List (List Item)) : (choices rows).length = (rows.map List.length).prod := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [choices, List.length_flatMap, List.length_map, List.map_const', List.sum_replicate_nat,
      List.map_cons, List.prod_cons, ih]

end Silmaril.Calculi.PERConstraints.Proofs
