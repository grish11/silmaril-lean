module

public import Silmaril.SSA.Peggy.EPEG.Saturation.NormalForms.Defs

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.NormalForms

open Silmaril.SSA.Peggy.EPEG.Saturation.NormalForms

universe u v

variable {State : Type u} {Label : Type v}
variable {order : State → State → Prop} {family : Family State Label}
variable {source target bound : State}

theorem reachable_order (refl : ∀ x, order x x) (trans : ∀ ⦃x y z⦄, order x y → order y z → order x z)
    (inflationary : ∀ label, Inflationary order (family label))
    (trace : Reachable family source target) : order source target := by
  induction trace with
  | refl => exact refl _
  | tail _ step ih =>
    obtain ⟨label, step⟩ := step
    exact trans ih (inflationary label step)

theorem reachable_below_stable (trans : ∀ ⦃x y z⦄, order x y → order y z → order x z)
    (simulate : ∀ label, MonotoneSimulation order (family label))
    (trace : Reachable family source target) (below : order source bound)
    (stable : Stable order family bound) : order target bound := by
  induction trace with
  | refl => exact below
  | tail _ step ih =>
    obtain ⟨label, step⟩ := step
    obtain ⟨next, delayed, covers⟩ := simulate label ih step
    exact trans covers (stable ⟨label, delayed⟩)

theorem stable_iff_no_progress :
    Stable order family target ↔ ∀ next, ¬ Progress order family target next := by
  constructor
  · intro stable _ progress
    exact progress.2 (stable progress.1)
  · intro terminal next step
    exact Classical.byContradiction fun absent => terminal next ⟨step, absent⟩

theorem paper_reachable_iff :
    Relation.ReflTransGen (PaperStep family) source target ↔ Reachable family source target := by
  constructor
  · intro trace
    induction trace with
    | refl => exact .refl
    | tail _ step ih => exact ih.tail step.1
  · intro trace
    induction trace with
    | refl => exact .refl
    | @tail mid next _ step ih =>
      by_cases same : mid = next
      · exact same ▸ ih
      · exact ih.tail ⟨step, same⟩

theorem paper_terminal_iff (refl : ∀ x, order x x) (antisymm : ∀ ⦃x y⦄, order x y → order y x → x = y)
    (inflationary : ∀ label, Inflationary order (family label)) :
    (∀ next, ¬ PaperStep family target next) ↔ Stable order family target := by
  constructor
  · intro terminal next step
    by_cases same : target = next
    · subst next
      exact refl _
    · exact (terminal next ⟨step, same⟩).elim
  · intro stable next step
    obtain ⟨label, applyLabel⟩ := step.1
    exact step.2 (antisymm (inflationary label applyLabel) (stable step.1))

end Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.NormalForms
