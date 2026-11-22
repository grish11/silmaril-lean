module

public import Silmaril.Calculi.PERConstraints.Finite.Defs
public import Silmaril.Calculi.PERConstraints.Thms
import Silmaril.Proofs.Calculi.PERConstraints.Finite

@[expose] public section
namespace Silmaril.Calculi.PERConstraints

open Silmaril.Formats

variable {α β Item : Type}

theorem eq_multiset_coe (model : PER α) (terms : List α) :
    EQMultiset model (terms : Multiset α) ↔ EQList model terms := Iff.rfl

@[simp] theorem eq_list_nil (model : PER α) : EQList model [] := by simp [EQList, EQ, members]
@[simp] theorem eq_list_singleton (model : PER α) (term : α) :
    EQList model [term] ↔ model.Dom term := by simp [EQList, EQ, members, PER.Dom]

theorem eq_list_iff_finset [DecidableEq α] (model : PER α) (terms : List α) :
    EQList model terms ↔ EQFinset model terms.toFinset := by
  rw [EQList, EQFinset, show members terms = (terms.toFinset : Set α) from Set.ext fun _ => List.mem_toFinset.symm]

theorem eq_multiset_iff_finset [DecidableEq α] (model : PER α) (terms : Multiset α) :
    EQMultiset model terms ↔ EQFinset model terms.toFinset := by
  rw [EQMultiset, EQFinset, show members terms = (terms.toFinset : Set α) from
    Set.ext fun _ => Multiset.mem_toFinset.symm]

theorem distinct_multiset_coe (model : PER α) (terms : List α) :
    DISTINCTMultiset model (terms : Multiset α) ↔ DISTINCTList model terms :=
  Proofs.distinct_multiset_coe model terms

theorem distinct_multiset_iff (model : PER α) (terms : Multiset α) :
    DISTINCTMultiset model terms ↔ terms.Nodup ∧ DISTINCT model (members terms) :=
  Quotient.inductionOn' terms fun list => (distinct_multiset_coe model list).trans (distinct_list_iff model list)

theorem distinct_multiset_iff_finset [DecidableEq α] (model : PER α) (terms : Multiset α) :
    DISTINCTMultiset model terms ↔ terms.Nodup ∧ DISTINCTFinset model terms.toFinset := by
  rw [distinct_multiset_iff, DISTINCTFinset, show members terms = (terms.toFinset : Set α) from
    Set.ext fun _ => Multiset.mem_toFinset.symm]

theorem distinct_multiset_map (model : PER β) (rename : α → β) (terms : Multiset α) :
    DISTINCTMultiset model (terms.map rename) ↔ DISTINCTMultiset (model.pull rename) terms :=
  Quotient.inductionOn' terms fun list => (distinct_multiset_coe model (list.map rename)).trans
    ((distinct_list_map model rename list).trans (distinct_multiset_coe (model.pull rename) list).symm)

theorem Bound.holds_ofMultisetDistinct (model : PER α) (terms : Multiset α) :
    (Bound.ofMultisetDistinct terms).Holds model ↔ DISTINCTMultiset model terms := by
  change DISTINCTList model terms.toList ↔ DISTINCTMultiset model terms
  simpa only [Multiset.coe_toList] using (distinct_multiset_coe model terms.toList).symm

theorem all_list_iff_finset [DecidableEq Item] (holds : Item → Prop) (items : List Item) :
    AllList holds items ↔ AllFinset holds items.toFinset := by
  simp only [AllList, AllFinset, All, members, Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset]

theorem any_list_iff_finset [DecidableEq Item] (holds : Item → Prop) (items : List Item) :
    AnyList holds items ↔ AnyFinset holds items.toFinset := by
  simp only [AnyList, AnyFinset, Any, members, Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset]

theorem all_multiset_iff_finset [DecidableEq Item] (holds : Item → Prop) (items : Multiset Item) :
    AllMultiset holds items ↔ AllFinset holds items.toFinset := by
  simp only [AllMultiset, AllFinset, All, members, Set.mem_ofPred_eq, Finset.mem_coe, Multiset.mem_toFinset]

theorem any_multiset_iff_finset [DecidableEq Item] (holds : Item → Prop) (items : Multiset Item) :
    AnyMultiset holds items ↔ AnyFinset holds items.toFinset := by
  simp only [AnyMultiset, AnyFinset, Any, members, Set.mem_ofPred_eq, Finset.mem_coe, Multiset.mem_toFinset]

theorem CNF.holds_ofAnd (model : PER α) (atoms : Set (Bound α)) :
    CNF.Holds model (CNF.ofAnd atoms) ↔ All (Bound.Holds model) atoms := by
  simp [CNF.Holds, CNF.ofAnd, All, Any]

theorem CNF.holds_ofOr (model : PER α) (atoms : Set (Bound α)) :
    CNF.Holds model (CNF.ofOr atoms) ↔ Any (Bound.Holds model) atoms := by
  simp [CNF.Holds, CNF.ofOr, All]

theorem CNF.map_ofAnd (rename : α → β) (atoms : Set (Bound α)) :
    CNF.map rename (CNF.ofAnd atoms) = CNF.ofAnd (Bound.map rename '' atoms) := by
  simp [CNF.map, CNF.ofAnd, Set.image_image]

theorem CNF.map_ofOr (rename : α → β) (atoms : Set (Bound α)) :
    CNF.map rename (CNF.ofOr atoms) = CNF.ofOr (Bound.map rename '' atoms) := by
  simp [CNF.map, CNF.ofOr]

theorem CNF.holds_ofLists (model : PER α) (clauses : List (List (Bound α))) :
    CNF.Holds model (CNF.ofLists clauses) ↔ AllList (AnyList (Bound.Holds model)) clauses := all_image

theorem DNF.holds_ofLists (model : PER α) (terms : List (List (Bound α))) :
    DNF.Holds model (DNF.ofLists terms) ↔ AnyList (AllList (Bound.Holds model)) terms := any_image

theorem CNF.holds_ofMultisets (model : PER α) (clauses : Multiset (Multiset (Bound α))) :
    CNF.Holds model (CNF.ofMultisets clauses) ↔ AllMultiset (AnyMultiset (Bound.Holds model)) clauses := all_image

theorem DNF.holds_ofMultisets (model : PER α) (terms : Multiset (Multiset (Bound α))) :
    DNF.Holds model (DNF.ofMultisets terms) ↔ AnyMultiset (AllMultiset (Bound.Holds model)) terms := any_image

theorem DNF.holds_toCNF (model : PER α) (sentence : DNF α) :
    CNF.Holds model (DNF.toCNF sentence) ↔ DNF.Holds model sentence := Proofs.dnf_to_cnf model sentence

/-- Size before any duplicate elimination. In particular, binary rows give `2^rows.length` choices. -/
theorem length_choices (rows : List (List Item)) : (choices rows).length = (rows.map List.length).prod :=
  Proofs.length_choices rows

theorem CNF.holds_finiteToDNF (model : PER α) (clauses : List (List (Bound α))) :
    DNF.Holds model (CNF.finiteToDNF clauses) ↔ CNF.Holds model (CNF.ofLists clauses) :=
  (DNF.holds_ofLists model _).trans ((Proofs.any_all_choices _ _).trans (CNF.holds_ofLists model _).symm)

theorem DNF.holds_finiteToCNF (model : PER α) (terms : List (List (Bound α))) :
    CNF.Holds model (DNF.finiteToCNF terms) ↔ DNF.Holds model (DNF.ofLists terms) :=
  (CNF.holds_ofLists model _).trans ((Proofs.all_any_choices _ _).trans (DNF.holds_ofLists model _).symm)

/-- Normalized finite DNF is a sentence of the original institution, including
under non-injective translations. This states equality of truth, not of syntax. -/
theorem DNF.finiteToCNF_satisfaction (model : PER β) (rename : α → β) (terms : List (List (Bound α))) :
    CNF.Holds model (CNF.map rename (DNF.finiteToCNF terms)) ↔
      DNF.Holds (model.pull rename) (DNF.ofLists terms) :=
  (CNF.holds_map model rename _).trans (DNF.holds_finiteToCNF (model.pull rename) terms)

end Silmaril.Calculi.PERConstraints
