module
public import Silmaril.Formats.PER.Compatibility.Defs

public section
namespace Silmaril.Proofs.Formats.PER.Compatibility
open Silmaril.Formats Silmaril.Formats.PER
variable {α : Type} {R E : PER α}

theorem agrees (strict : R.StrictlyCompatible E) {left right : α} (valid : R.Dom left) :
    E.rel left right ↔ R.rel left right :=
  ⟨fun h => (strict.2 h).elim id (fun invalid => (invalid.1 valid).elim), fun h => strict.1 h⟩

theorem preserves (strict : R.StrictlyCompatible E) {left right : α} (related : E.rel left right) :
    R.Dom left ↔ R.Dom right :=
  ⟨fun h => R.dom_right ((agrees strict h).mp related),
   fun h => R.dom_right ((agrees strict h).mp (E.laws.symm related))⟩

theorem restrict_eq (strict : R.StrictlyCompatible E) : E.restrict R.Dom = R := by
  apply PER.ext
  intro left right
  exact ⟨fun h => (agrees strict h.1).mp h.2.2, fun h => ⟨R.dom_left h, R.dom_right h, strict.1 h⟩⟩

theorem weak_counterexample : ∃ R E : PER Bool, R.WeaklyCompatible E ∧
    E.rel true false ∧ R.Dom true ∧ ¬ R.Dom false := by
  refine ⟨(PER.equality Bool).restrict (· = true), PER.universal Bool, ⟨?_, ?_⟩, trivial, ?_, ?_⟩
  · exact fun _ _ _ => True.intro
  · intro left right _
    cases left <;> cases right <;> simp [PER.restrict, PER.Dom, PER.equality]
  · exact ⟨rfl, rfl, rfl⟩
  · simp [PER.restrict, PER.Dom]

theorem singleton_strict (R : PER α) : R.StrictlyCompatible R.singletonCompletion := by
  classical
  refine ⟨fun _ _ h => Or.inl h, ?_⟩
  rintro left right (h | rfl)
  · exact Or.inl h
  · exact if valid : R.Dom left then Or.inl valid else Or.inr ⟨valid, valid⟩

theorem invalid_total (R : PER α) (value : α) : R.invalidCompletion.Dom value := by
  classical
  exact if valid : R.Dom value then Or.inl valid else Or.inr ⟨valid, valid⟩

theorem strict_iff_between (total : ∀ x, E.Dom x) :
    R.StrictlyCompatible E ↔ R.singletonCompletion ≤ E ∧ E ≤ R.invalidCompletion := by
  constructor
  · intro h
    refine ⟨?_, fun _ _ hr => h.2 hr⟩
    rintro left right (hr | rfl)
    · exact h.1 hr
    · exact total left
  · exact fun h => ⟨fun _ _ hr => h.1 (Or.inl hr), fun _ _ hr => h.2 hr⟩

theorem completions_eq_iff (R : PER α) : R.singletonCompletion = R.invalidCompletion ↔
    ∀ ⦃left right⦄, ¬ R.Dom left → ¬ R.Dom right → left = right := by
  constructor
  · intro eq left right hl hr
    have h : R.invalidCompletion.rel left right := Or.inr ⟨hl, hr⟩
    rw [← eq] at h
    exact h.elim (fun rel => (hl (R.dom_left rel)).elim) id
  · intro unique
    exact le_antisymm (singleton_strict R).2 (fun _ _ h =>
      h.elim Or.inl (fun invalid => Or.inr (unique invalid.1 invalid.2)))

end Silmaril.Proofs.Formats.PER.Compatibility
