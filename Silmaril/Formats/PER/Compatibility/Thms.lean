module
public import Silmaril.Formats.PER.Compatibility.Defs
import Silmaril.Proofs.Formats.PER.Compatibility.Basic

public section
namespace Silmaril.Formats.PER
variable {α : Type} {R E : PER α}

theorem ofSetoid_toSetoid (R : PER α) (total : ∀ x, R.Dom x) : ofSetoid (R.toSetoid total) = R :=
  PER.ext fun _ _ => Iff.rfl

theorem WeaklyCompatible.agrees_on_support (h : R.WeaklyCompatible E) {left right : α}
    (hl : R.Dom left) (hr : R.Dom right) : E.rel left right ↔ R.rel left right :=
  ⟨fun rel => (h.2 rel).elim id (fun invalid => invalid.elim (fun bad => (bad hl).elim)
    (fun bad => (bad hr).elim)), fun rel => h.1 rel⟩

theorem StrictlyCompatible.weak (h : R.StrictlyCompatible E) : R.WeaklyCompatible E :=
  ⟨h.1, fun _ _ hr => (h.2 hr).imp_right (fun invalid => Or.inl invalid.1)⟩

theorem StrictlyCompatible.agrees (h : R.StrictlyCompatible E) {left right : α} (valid : R.Dom left) :
    E.rel left right ↔ R.rel left right := Proofs.Formats.PER.Compatibility.agrees h valid

/-- Original support is saturated in `E`; `E` may have extra support. -/
theorem StrictlyCompatible.preserves (h : R.StrictlyCompatible E) {left right : α}
    (related : E.rel left right) : R.Dom left ↔ R.Dom right :=
  Proofs.Formats.PER.Compatibility.preserves h related

theorem StrictlyCompatible.restrict_eq (h : R.StrictlyCompatible E) : E.restrict R.Dom = R :=
  Proofs.Formats.PER.Compatibility.restrict_eq h

theorem weak_counterexample : ∃ R E : PER Bool, R.WeaklyCompatible E ∧
    E.rel true false ∧ R.Dom true ∧ ¬ R.Dom false := Proofs.Formats.PER.Compatibility.weak_counterexample

theorem singletonCompletion_strict (R : PER α) : R.StrictlyCompatible R.singletonCompletion :=
  Proofs.Formats.PER.Compatibility.singleton_strict R

theorem singletonCompletion_total (R : PER α) (value : α) : R.singletonCompletion.Dom value :=
  Or.inr rfl

theorem invalidCompletion_strict (R : PER α) : R.StrictlyCompatible R.invalidCompletion :=
  ⟨fun _ _ h => Or.inl h, fun _ _ h => h⟩

theorem invalidCompletion_total (R : PER α) (value : α) : R.invalidCompletion.Dom value :=
  Proofs.Formats.PER.Compatibility.invalid_total R value

/-- The least and greatest strictly compatible total equivalences. -/
theorem strictlyCompatible_iff_between (total : ∀ x, E.Dom x) :
    R.StrictlyCompatible E ↔ R.singletonCompletion ≤ E ∧ E ≤ R.invalidCompletion :=
  Proofs.Formats.PER.Compatibility.strict_iff_between total

theorem completions_eq_iff (R : PER α) : R.singletonCompletion = R.invalidCompletion ↔
    ∀ ⦃left right⦄, ¬ R.Dom left → ¬ R.Dom right → left = right :=
  Proofs.Formats.PER.Compatibility.completions_eq_iff R

end Silmaril.Formats.PER
