module

public import Silmaril.Calculi.PERConstraints.Interval.Examples.Defs
import Silmaril.Calculi.PERConstraints.Examples.Thms

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.IntervalExamples.Proofs

open Silmaril.Formats
open Term

private theorem mem_full {α : Type} {admissible : PER α → Prop} {model : PER α}
    (ok : admissible model) : model ∈ (full α).completions admissible :=
  ⟨⟨fun _ _ h => h.elim, fun _ _ _ => trivial⟩, ok⟩

private theorem pair_only_le_iff (model : PER Term) (a b : Term) :
    pairOnly a b ≤ model ↔ model.rel a b := by
  constructor
  · intro h
    apply h
    exact ⟨by simp, by simp, trivial⟩
  · intro h x y hx
    obtain ⟨hx, hy, _⟩ := hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact model.dom_left h
    · exact h
    · exact model.laws.symm h
    · exact model.dom_right h

private theorem holds_either_pair (model : PER Term) :
    eitherPair.Holds model ↔ model.rel first middle ∨ model.rel middle last := by
  have pair (a b : Term) : EQ model {a, b} ↔ model.rel a b := by
    rw [← pair_only_le_iff model a b]
    exact ⟨fun h _ _ edge => h _ edge.1 _ edge.2.1, fun h _ hx _ hy => h ⟨hx, hy, trivial⟩⟩
  simp [eitherPair, CNF.holds_ofOr, Any, Bound.Holds, pair]

theorem either_pair_two_minimal :
    Minimal (· ∈ (full Term).completions (fun model => eitherPair.Holds model)) (pairOnly first middle) ∧
    Minimal (· ∈ (full Term).completions (fun model => eitherPair.Holds model)) (pairOnly middle last) ∧
    pairOnly first middle ≠ pairOnly middle last := by
  refine ⟨⟨mem_full ((holds_either_pair _).mpr (Or.inl ⟨by simp, by simp, trivial⟩)), ?_⟩,
    ⟨mem_full ((holds_either_pair _).mpr (Or.inr ⟨by simp, by simp, trivial⟩)), ?_⟩, ?_⟩
  · intro other hm below
    rcases (holds_either_pair other).mp hm.2 with same | opposite
    · exact (pair_only_le_iff other first middle).mpr same
    have impossible := (below opposite : (pairOnly first middle).rel middle last).2.1
    simp [reduceCtorEq] at impossible
  · intro other hm below
    rcases (holds_either_pair other).mp hm.2 with opposite | same
    · have impossible := (below opposite : (pairOnly middle last).rel first middle).1
      simp [reduceCtorEq] at impossible
    exact (pair_only_le_iff other middle last).mpr same
  · intro same
    have edge : (pairOnly first middle).rel first middle := ⟨by simp, by simp, trivial⟩
    rw [same] at edge
    have impossible := edge.1
    simp [reduceCtorEq] at impossible

theorem either_pair_no_least :
    ¬ ∃ model, IsLeast ((full Term).completions (fun candidate => eitherPair.Holds candidate)) model := by
  rintro ⟨model, hm⟩
  rcases (holds_either_pair model).mp hm.1.2 with left | right
  · have impossible := (hm.2 either_pair_two_minimal.2.1.1 left : (pairOnly middle last).rel first middle).1
    simp [reduceCtorEq] at impossible
  · have impossible := (hm.2 either_pair_two_minimal.1.1 right : (pairOnly first middle).rel middle last).2.1
    simp [reduceCtorEq] at impossible

private theorem distinct_pair_iff {α : Type} (model : PER α) (a b : α) :
    DISTINCTList model [a, b] ↔ model.Dom a ∧ model.Dom b ∧ ¬ model.rel a b := by
  simp [DISTINCTList, and_assoc]

private theorem holds_separate_ends (model : PER Term) :
    separateEnds.Holds model ↔ model.Dom first ∧ model.Dom last ∧ ¬ model.rel first last := by
  simpa [separateEnds, CNF.holds_ofOr, Any, Bound.Holds] using distinct_pair_iff model first last

theorem separate_ends_two_maximal :
    Maximal (· ∈ (full Term).completions (fun model => separateEnds.Holds model)) joinFirstMiddle ∧
    Maximal (· ∈ (full Term).completions (fun model => separateEnds.Holds model)) joinMiddleLast ∧
    joinFirstMiddle ≠ joinMiddleLast := by
  refine ⟨⟨mem_full ((holds_separate_ends _).mpr ⟨rfl, rfl, Bool.noConfusion⟩), ?_⟩,
    ⟨mem_full ((holds_separate_ends _).mpr ⟨rfl, rfl, Bool.noConfusion⟩), ?_⟩, ?_⟩
  · intro other hm above
    have apart := ((holds_separate_ends other).mp hm.2).2.2
    have left : other.rel first middle := above (show joinFirstMiddle.rel first middle from rfl)
    have right : ¬ other.rel middle last := fun edge => apart (other.laws.trans left edge)
    intro a b edge
    cases a <;> cases b <;>
      first
      | rfl
      | exact (apart edge).elim
      | exact (apart (other.laws.symm edge)).elim
      | exact (right edge).elim
      | exact (right (other.laws.symm edge)).elim
  · intro other hm above
    have apart := ((holds_separate_ends other).mp hm.2).2.2
    have right : other.rel middle last := above (show joinMiddleLast.rel middle last from rfl)
    have left : ¬ other.rel first middle := fun edge => apart (other.laws.trans edge right)
    intro a b edge
    cases a <;> cases b <;>
      first
      | rfl
      | exact (apart edge).elim
      | exact (apart (other.laws.symm edge)).elim
      | exact (left edge).elim
      | exact (left (other.laws.symm edge)).elim
  · intro same
    have edge : joinFirstMiddle.rel first middle := rfl
    rw [same] at edge
    exact Bool.noConfusion edge

theorem separate_ends_no_greatest :
    ¬ ∃ model, IsGreatest ((full Term).completions (fun candidate => separateEnds.Holds candidate)) model := by
  rintro ⟨model, hm⟩
  have left : model.rel first middle := hm.2 separate_ends_two_maximal.1.1 (show joinFirstMiddle.rel first middle from rfl)
  have right : model.rel middle last := hm.2 separate_ends_two_maximal.2.1.1 (show joinMiddleLast.rel middle last from rfl)
  exact ((holds_separate_ends model).mp hm.1.2).2.2 (model.laws.trans left right)

private theorem holds_separate_bools (model : PER Bool) :
    separateBools.Holds model ↔ model.Dom false ∧ model.Dom true ∧ ¬ model.rel false true := by
  rw [separateBools, Dictionary.holds_toCNF, ← distinct_pair_iff]
  simp [Examples.separation, Dictionary.Holds, Bound.Holds]

private theorem equality_separates_bools : separateBools.Holds (PER.equality Bool) :=
  (holds_separate_bools _).mpr ⟨rfl, rfl, Bool.noConfusion⟩

theorem distinct_interior_only :
    ¬ separateBools.Holds (full Bool).lower ∧ ¬ separateBools.Holds (full Bool).upper ∧
    (full Bool).Possible (fun _ => True) (fun model => separateBools.Holds model) :=
  ⟨fun h => ((holds_separate_bools _).mp h).1,
    fun h => ((holds_separate_bools _).mp h).2.2 trivial,
    ⟨PER.equality Bool, mem_full trivial, equality_separates_bools⟩⟩

theorem collapse_possible_strict :
    ((full Unit).pull collapse).Possible (fun _ => True) (fun model => separateBools.Holds model) ∧
    ¬ (full Unit).Possible (fun _ => True) (fun model => (separateBools.map collapse).Holds model) := by
  refine ⟨⟨PER.equality Bool, ⟨⟨fun _ _ h => h.elim, fun _ _ _ => trivial⟩, trivial⟩,
    equality_separates_bools⟩, ?_⟩
  rintro ⟨model, _, holds⟩
  exact Examples.collapsed_unsat model holds

private theorem holds_require_false (model : PER Bool) : requireFalse.Holds model ↔ model.Dom false := by
  simp [requireFalse, CNF.holds_ofOr, Any, Bound.Holds]

theorem collapse_reduct_not_least :
    IsLeast ((full Unit).completions (fun model => (requireFalse.map collapse).Holds model)) (PER.equality Unit) ∧
    ¬ IsLeast (((full Unit).pull collapse).completions (fun model => requireFalse.Holds model))
      ((PER.equality Unit).pull collapse) := by
  have translated (model : PER Unit) : (requireFalse.map collapse).Holds model ↔ model.Dom () :=
    (CNF.holds_map model collapse requireFalse).trans (holds_require_false _)
  constructor
  · refine ⟨mem_full ((translated _).mpr rfl), ?_⟩
    intro model hm x y _
    cases x
    cases y
    exact (translated model).mp hm.2
  · intro least
    let source := (PER.equality Bool).restrict (· = false)
    have hm : source ∈ ((full Unit).pull collapse).completions (fun model => requireFalse.Holds model) :=
      ⟨⟨fun _ _ h => h.elim, fun _ _ _ => trivial⟩, (holds_require_false _).mpr ⟨rfl, rfl, rfl⟩⟩
    have edge : source.rel false true := least.2 hm (show ((PER.equality Unit).pull collapse).rel false true from rfl)
    exact Bool.noConfusion edge.2.1

theorem conflict_fiber_empty :
    (full Bool).completions (fun model => (Dictionary.toCNF Examples.conflict).Holds model) = ∅ := by
  ext model
  exact ⟨fun hm => Examples.conflict_unsat model ((Dictionary.holds_toCNF model _).mp hm.2), False.elim⟩

end Silmaril.Calculi.PERConstraints.IntervalExamples.Proofs
