module

public import Silmaril.Calculi.PERConstraints.Interval.Defs
public import Silmaril.Calculi.PERConstraints.Finite.Thms
import Silmaril.Proofs.Calculi.PERConstraints.Interval.Basic
import Silmaril.Proofs.Calculi.PERConstraints.Interval.Coverage

@[expose] public section
namespace Silmaril.Calculi.PERConstraints

open CategoryTheory Silmaril.Formats

variable {α β γ : Type}

theorem eq_monotone (terms : Set α) : Monotone (fun model => EQ model terms) :=
  fun _ _ le holds left hl right hr => le (holds left hl right hr)

theorem CNF.holds_mono_of_eqOnly {sentence : CNF α} (positive : sentence.EqOnly) :
    Monotone (fun model => sentence.Holds model) := IntervalProofs.eq_only_monotone positive

theorem CNF.EqOnly.map {sentence : CNF α} (positive : sentence.EqOnly) (rename : α → β) :
    (sentence.map rename).EqOnly := by
  rintro _ ⟨clause, hc, rfl⟩ _ ⟨atom, ha, rfl⟩
  obtain ⟨terms, rfl⟩ := positive clause hc atom ha
  exact ⟨rename '' terms, rfl⟩

/-- The nonrelation part is downward closed. The smaller model still needs
all the designated terms in its domain. -/
theorem distinctList_of_le {lower upper : PER α} {terms : List α} (le : lower ≤ upper)
    (valid : ∀ term ∈ terms, lower.Dom term) (holds : DISTINCTList upper terms) :
    DISTINCTList lower terms := IntervalProofs.distinct_antitone le valid holds

namespace Bounds

variable {bounds : Bounds α} {admissible query : PER α → Prop}

theorem refines_iff (more less : Bounds α) :
    more.Refines less ↔ more.completions (fun _ => True) ⊆ less.completions (fun _ => True) :=
  IntervalProofs.refines_iff more less

@[simp] theorem completions_exact (model : PER α) (admissible : PER α → Prop) :
    (exact model).completions admissible = {candidate | candidate = model ∧ admissible model} :=
  IntervalProofs.completions_exact model admissible

theorem certain_exact (model : PER α) :
    (exact model).Certain admissible query ↔ (admissible model → query model) := by
  simp [Certain]

theorem possible_exact (model : PER α) :
    (exact model).Possible admissible query ↔ admissible model ∧ query model := by
  simp [Possible]

/-- Both interval readings recover satisfaction in the ordinary CNF institution. -/
theorem satisfaction_exact {signature : Syntax} (model : Model signature) (sentence : CNF signature.Term) :
    ((exact model).Certain (fun _ => True) (fun candidate => sentence.Holds candidate) ↔
      (room signature).Sat (Discrete.mk model) sentence) ∧
    ((exact model).Possible (fun _ => True) (fun candidate => sentence.Holds candidate) ↔
      (room signature).Sat (Discrete.mk model) sentence) := by
  simp [certain_exact, possible_exact, room]

theorem empty_completions (empty : bounds.completions admissible = ∅) :
    bounds.Certain admissible query ∧ ¬ bounds.Possible admissible query := by
  simp [Certain, Possible, empty]

theorem possible_of_certain (nonempty : (bounds.completions admissible).Nonempty)
    (certain : bounds.Certain admissible query) : bounds.Possible admissible query :=
  let ⟨model, hm⟩ := nonempty
  ⟨model, hm, certain model hm⟩

theorem isLeast_lower (lo : admissible bounds.lower) :
    IsLeast (bounds.completions admissible) bounds.lower :=
  ⟨⟨⟨le_rfl, bounds.ordered⟩, lo⟩, fun _ hm => hm.1.1⟩

theorem isGreatest_upper (hi : admissible bounds.upper) :
    IsGreatest (bounds.completions admissible) bounds.upper :=
  ⟨⟨⟨bounds.ordered, le_rfl⟩, hi⟩, fun _ hm => hm.1.2⟩

/-- A least admissible model exists exactly when the infimum is admissible and within bounds. -/
theorem exists_isLeast_iff_sInf_mem :
    (∃ model, IsLeast (bounds.completions admissible) model) ↔
      sInf (bounds.completions admissible) ∈ bounds.completions admissible := by
  refine ⟨?_, fun hm => ⟨_, hm, fun _ h => sInf_le h⟩⟩
  rintro ⟨model, hm⟩
  simpa only [le_antisymm (sInf_le hm.1) (le_sInf hm.2)] using hm.1

/-- A greatest admissible model exists exactly when the supremum is admissible and within bounds. -/
theorem exists_isGreatest_iff_sSup_mem :
    (∃ model, IsGreatest (bounds.completions admissible) model) ↔
      sSup (bounds.completions admissible) ∈ bounds.completions admissible := by
  refine ⟨?_, fun hm => ⟨_, hm, fun _ h => le_sSup h⟩⟩
  rintro ⟨model, hm⟩
  simpa only [le_antisymm (sSup_le hm.2) (le_sSup hm.1)] using hm.1

theorem certain_iff_of_isLeast {least : PER α}
    (h : IsLeast (bounds.completions admissible) least) (mono : Monotone query) :
    bounds.Certain admissible query ↔ query least := IntervalProofs.certain_isLeast h mono

theorem possible_iff_of_isGreatest {greatest : PER α}
    (h : IsGreatest (bounds.completions admissible) greatest) (mono : Monotone query) :
    bounds.Possible admissible query ↔ query greatest := IntervalProofs.possible_isGreatest h mono

/-- Endpoint evaluation is exact for the positive EQ fragment when both
endpoints are admissible. Use `True` for the unrestricted interval. -/
theorem eqOnly_endpoints {sentence : CNF α} (positive : sentence.EqOnly)
    (lo : admissible bounds.lower) (hi : admissible bounds.upper) :
    (bounds.Certain admissible (fun model => sentence.Holds model) ↔ sentence.Holds bounds.lower) ∧
    (bounds.Possible admissible (fun model => sentence.Holds model) ↔ sentence.Holds bounds.upper) :=
  ⟨certain_iff_of_isLeast (isLeast_lower lo) (CNF.holds_mono_of_eqOnly positive),
   possible_iff_of_isGreatest (isGreatest_upper hi) (CNF.holds_mono_of_eqOnly positive)⟩

/-- Occurrence DISTINCT uses the opposite endpoints when all its terms
are already valid at the lower endpoint. -/
theorem distinctList_endpoints (bounds : Bounds α) {terms : List α}
    (lo : admissible bounds.lower) (hi : admissible bounds.upper)
    (valid : ∀ term ∈ terms, bounds.lower.Dom term) :
    (bounds.Certain admissible (fun model => DISTINCTList model terms) ↔ DISTINCTList bounds.upper terms) ∧
    (bounds.Possible admissible (fun model => DISTINCTList model terms) ↔ DISTINCTList bounds.lower terms) :=
  IntervalProofs.distinct_endpoints bounds lo hi valid

@[simp] theorem pull_id (bounds : Bounds α) : bounds.pull id = bounds := rfl

theorem pull_comp (bounds : Bounds γ) (first : α → β) (second : β → γ) :
    bounds.pull (second ∘ first) = (bounds.pull second).pull first := rfl

@[simp] theorem reduct_id {signature : Syntax} (bounds : Bounds signature.Term) :
    reduct (𝟙 signature) bounds = bounds := rfl

theorem reduct_comp {source middle target : Syntax} (first : source ⟶ middle) (second : middle ⟶ target)
    (bounds : Bounds target.Term) : reduct (first ≫ second) bounds = reduct first (reduct second bounds) := rfl

@[simp] theorem pull_exact (model : PER β) (rename : α → β) :
    (exact model).pull rename = exact (model.pull rename) := rfl

@[simp] theorem reduct_exact {source target : Syntax} (rename : source ⟶ target) (model : Model target) :
    reduct rename (exact model) = exact (PERConstraints.reduct rename model) := rfl

theorem refines_pull {more less : Bounds β} (refines : more.Refines less) (rename : α → β) :
    (more.pull rename).Refines (less.pull rename) :=
  ⟨fun _ _ h => refines.1 h, fun _ _ h => refines.2 h⟩

/-- Every completion pulls back, provided admissibility is preserved. -/
theorem pull_mapsTo (bounds : Bounds β) (rename : α → β)
    {sourceAdmissible : PER α → Prop} {targetAdmissible : PER β → Prop}
    (preserves : ∀ model, targetAdmissible model → sourceAdmissible (model.pull rename)) :
    Set.MapsTo (fun model => model.pull rename) (bounds.completions targetAdmissible)
      ((bounds.pull rename).completions sourceAdmissible) :=
  fun _ hm => ⟨⟨fun _ _ h => hm.1.1 h, fun _ _ h => hm.1.2 h⟩, preserves _ hm.2⟩

theorem pull_mapsTo_closed {source target : Congruence.Signature} (rename : source ⟶ target)
    (bounds : Bounds target.carrier.Term) :
    Set.MapsTo (fun model => model.pull rename.term) (bounds.completions target.constructors.Closed)
      ((bounds.pull rename.term).completions source.constructors.Closed) :=
  bounds.pull_mapsTo rename.term (fun _ => Congruence.closed_pull rename)

/-- Every unrestricted source completion extends across an injective term map,
within the given target bounds. -/
theorem pull_surjOn_of_injective (bounds : Bounds β) {rename : α → β}
    (injective : Function.Injective rename) :
    Set.SurjOn (fun model => model.pull rename) (bounds.completions (fun _ => True))
      ((bounds.pull rename).completions (fun _ => True)) :=
  IntervalProofs.pull_surjOn_of_injective bounds injective

variable {targetBounds : Bounds β} {rename : α → β}
  {sourceAdmissible : PER α → Prop} {targetAdmissible : PER β → Prop}

theorem certain_map
    (maps : Set.MapsTo (fun model => model.pull rename) (targetBounds.completions targetAdmissible)
      ((targetBounds.pull rename).completions sourceAdmissible)) (sentence : CNF α) :
    (targetBounds.pull rename).Certain sourceAdmissible (fun model => sentence.Holds model) →
    targetBounds.Certain targetAdmissible (fun model => (sentence.map rename).Holds model) :=
  IntervalProofs.certain_map maps sentence

theorem possible_of_map
    (maps : Set.MapsTo (fun model => model.pull rename) (targetBounds.completions targetAdmissible)
      ((targetBounds.pull rename).completions sourceAdmissible)) (sentence : CNF α) :
    targetBounds.Possible targetAdmissible (fun model => (sentence.map rename).Holds model) →
    (targetBounds.pull rename).Possible sourceAdmissible (fun model => sentence.Holds model) :=
  IntervalProofs.possible_map maps sentence

/-- Pullback of completions plus coverage of all source completions gives both
satisfaction equivalences. -/
theorem map_iff_of_coverage
    (maps : Set.MapsTo (fun model => model.pull rename) (targetBounds.completions targetAdmissible)
      ((targetBounds.pull rename).completions sourceAdmissible))
    (covers : Set.SurjOn (fun model => model.pull rename) (targetBounds.completions targetAdmissible)
      ((targetBounds.pull rename).completions sourceAdmissible)) (sentence : CNF α) :
    (targetBounds.Certain targetAdmissible (fun model => (sentence.map rename).Holds model) ↔
      (targetBounds.pull rename).Certain sourceAdmissible (fun model => sentence.Holds model)) ∧
    (targetBounds.Possible targetAdmissible (fun model => (sentence.map rename).Holds model) ↔
      (targetBounds.pull rename).Possible sourceAdmissible (fun model => sentence.Holds model)) :=
  IntervalProofs.map_iff_of_coverage maps covers sentence

end Bounds

theorem eqSeed_le_iff (equations : Set (Set α)) (model : PER α) :
    eqSeed equations ≤ model ↔ (CNF.ofAnd (Bound.eq '' equations)).Holds model :=
  IntervalProofs.eq_seed_le_iff equations model

/-- In a closed upper model of a conjunction of EQs, the closure of the
lower bound and the required pairs is the least admissible model. -/
theorem eq_conjunction_isLeast (bounds : Bounds α) (C : PER.Constructors α)
    (equations : Set (Set α)) (closed : C.Closed bounds.upper)
    (holds : (CNF.ofAnd (Bound.eq '' equations)).Holds bounds.upper) :
    IsLeast (bounds.completions (fun model => C.Closed model ∧
      (CNF.ofAnd (Bound.eq '' equations)).Holds model))
      (C.generated (bounds.lower ⊔ eqSeed equations)) :=
  IntervalProofs.eq_conjunction_isLeast bounds C equations closed holds

end Silmaril.Calculi.PERConstraints
