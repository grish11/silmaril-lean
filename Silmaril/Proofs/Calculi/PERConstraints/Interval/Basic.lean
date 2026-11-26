module

public import Silmaril.Calculi.PERConstraints.Interval.Defs
public import Silmaril.Calculi.PERConstraints.Finite.Thms

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.IntervalProofs

open Silmaril.Formats

variable {α β : Type}

theorem eq_only_monotone {sentence : CNF α} (positive : sentence.EqOnly) :
    Monotone (fun model => sentence.Holds model) := by
  intro lower upper included holds clause inSentence
  obtain ⟨atom, inClause, trueBelow⟩ := holds clause inSentence
  refine ⟨atom, inClause, ?_⟩
  obtain ⟨terms, rfl⟩ := positive clause inSentence atom inClause
  exact fun left hl right hr => included (trueBelow left hl right hr)

theorem distinct_antitone {lower upper : PER α} {terms : List α} (le : lower ≤ upper)
    (valid : ∀ term ∈ terms, lower.Dom term) (holds : DISTINCTList upper terms) :
    DISTINCTList lower terms :=
  ⟨valid, holds.2.imp (fun unrelated related => unrelated (le related))⟩

theorem refines_iff (more less : Bounds α) :
    more.Refines less ↔ more.completions (fun _ => True) ⊆ less.completions (fun _ => True) := by
  constructor
  · intro h model hm
    exact ⟨⟨h.1.trans hm.1.1, hm.1.2.trans h.2⟩, trivial⟩
  · intro h
    exact ⟨(h ⟨⟨le_rfl, more.ordered⟩, trivial⟩).1.1,
      (h ⟨⟨more.ordered, le_rfl⟩, trivial⟩).1.2⟩

theorem completions_exact (model : PER α) (admissible : PER α → Prop) :
    (Bounds.exact model).completions admissible = {candidate | candidate = model ∧ admissible model} := by
  ext candidate
  constructor
  · rintro ⟨⟨lo, hi⟩, ok⟩
    have same : candidate = model := le_antisymm hi lo
    exact ⟨same, same ▸ ok⟩
  · rintro ⟨rfl, ok⟩
    exact ⟨⟨le_rfl, le_rfl⟩, ok⟩

theorem certain_isLeast {bounds : Bounds α} {admissible query : PER α → Prop}
    {least : PER α} (h : IsLeast (bounds.completions admissible) least) (mono : Monotone query) :
    bounds.Certain admissible query ↔ query least :=
  ⟨fun all => all least h.1, fun holds _ hm => mono (h.2 hm) holds⟩

theorem possible_isGreatest {bounds : Bounds α} {admissible query : PER α → Prop}
    {greatest : PER α} (h : IsGreatest (bounds.completions admissible) greatest) (mono : Monotone query) :
    bounds.Possible admissible query ↔ query greatest :=
  ⟨fun ⟨_, hm, holds⟩ => mono (h.2 hm) holds, fun holds => ⟨greatest, h.1, holds⟩⟩

theorem distinct_endpoints (bounds : Bounds α) {admissible : PER α → Prop} {terms : List α}
    (lo : admissible bounds.lower) (hi : admissible bounds.upper)
    (valid : ∀ term ∈ terms, bounds.lower.Dom term) :
    (bounds.Certain admissible (fun model => DISTINCTList model terms) ↔ DISTINCTList bounds.upper terms) ∧
    (bounds.Possible admissible (fun model => DISTINCTList model terms) ↔ DISTINCTList bounds.lower terms) := by
  refine ⟨⟨fun all => all _ ⟨⟨bounds.ordered, le_rfl⟩, hi⟩, ?_⟩,
    ⟨?_, fun holds => ⟨_, ⟨⟨le_rfl, bounds.ordered⟩, lo⟩, holds⟩⟩⟩
  · intro holds model hm
    exact distinct_antitone hm.1.2 (fun term ht => hm.1.1 (valid term ht)) holds
  · rintro ⟨model, hm, holds⟩
    exact distinct_antitone hm.1.1 valid holds

theorem certain_map {bounds : Bounds β} {rename : α → β}
    {sourceAdmissible : PER α → Prop} {targetAdmissible : PER β → Prop}
    (maps : Set.MapsTo (fun model => model.pull rename) (bounds.completions targetAdmissible)
      ((bounds.pull rename).completions sourceAdmissible)) (sentence : CNF α) :
    (bounds.pull rename).Certain sourceAdmissible (fun model => sentence.Holds model) →
    bounds.Certain targetAdmissible (fun model => (sentence.map rename).Holds model) := by
  intro certain model hm
  exact (CNF.holds_map model rename sentence).mpr (certain _ (maps hm))

theorem possible_map {bounds : Bounds β} {rename : α → β}
    {sourceAdmissible : PER α → Prop} {targetAdmissible : PER β → Prop}
    (maps : Set.MapsTo (fun model => model.pull rename) (bounds.completions targetAdmissible)
      ((bounds.pull rename).completions sourceAdmissible)) (sentence : CNF α) :
    bounds.Possible targetAdmissible (fun model => (sentence.map rename).Holds model) →
    (bounds.pull rename).Possible sourceAdmissible (fun model => sentence.Holds model) := by
  rintro ⟨model, hm, holds⟩
  exact ⟨_, maps hm, (CNF.holds_map model rename sentence).mp holds⟩

theorem map_iff_of_coverage {bounds : Bounds β} {rename : α → β}
    {sourceAdmissible : PER α → Prop} {targetAdmissible : PER β → Prop}
    (maps : Set.MapsTo (fun model => model.pull rename) (bounds.completions targetAdmissible)
      ((bounds.pull rename).completions sourceAdmissible))
    (covers : Set.SurjOn (fun model => model.pull rename) (bounds.completions targetAdmissible)
      ((bounds.pull rename).completions sourceAdmissible)) (sentence : CNF α) :
    (bounds.Certain targetAdmissible (fun model => (sentence.map rename).Holds model) ↔
      (bounds.pull rename).Certain sourceAdmissible (fun model => sentence.Holds model)) ∧
    (bounds.Possible targetAdmissible (fun model => (sentence.map rename).Holds model) ↔
      (bounds.pull rename).Possible sourceAdmissible (fun model => sentence.Holds model)) := by
  refine ⟨⟨?_, certain_map maps sentence⟩, ⟨possible_map maps sentence, ?_⟩⟩
  · intro certain source hs
    obtain ⟨target, ht, rfl⟩ := covers hs
    exact (CNF.holds_map target rename sentence).mp (certain target ht)
  · rintro ⟨source, hs, holds⟩
    obtain ⟨target, ht, rfl⟩ := covers hs
    exact ⟨target, ht, (CNF.holds_map target rename sentence).mpr holds⟩

theorem eq_seed_le_iff (equations : Set (Set α)) (model : PER α) :
    eqSeed equations ≤ model ↔ (CNF.ofAnd (Bound.eq '' equations)).Holds model := by
  rw [CNF.holds_ofAnd, all_image]
  constructor
  · intro h terms ht left hl right hr
    exact h (fun extension => extension.property ⟨terms, ht, hl, hr⟩)
  · intro h
    apply sInf_le
    rintro left right ⟨terms, ht, hl, hr⟩
    exact h terms ht left hl right hr

theorem eq_conjunction_isLeast (bounds : Bounds α) (C : PER.Constructors α)
    (equations : Set (Set α)) (closed : C.Closed bounds.upper)
    (holds : (CNF.ofAnd (Bound.eq '' equations)).Holds bounds.upper) :
    IsLeast (bounds.completions (fun model => C.Closed model ∧
      (CNF.ofAnd (Bound.eq '' equations)).Holds model))
      (C.generated (bounds.lower ⊔ eqSeed equations)) := by
  have seedUpper := sup_le bounds.ordered ((eq_seed_le_iff equations bounds.upper).mpr holds)
  have seedGenerated := C.le_generated (bounds.lower ⊔ eqSeed equations)
  refine ⟨⟨⟨le_sup_left.trans seedGenerated, C.generated_le seedUpper closed⟩,
    C.generated_closed _, (eq_seed_le_iff equations _).mp (le_sup_right.trans seedGenerated)⟩, ?_⟩
  intro model hm
  exact C.generated_le (sup_le hm.1.1 ((eq_seed_le_iff equations _).mpr hm.2.2)) hm.2.1

end Silmaril.Calculi.PERConstraints.IntervalProofs
