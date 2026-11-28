module

public import Silmaril.SSA.Peggy.EPEG.Saturation.NormalForms.Defs
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.NormalForms.Order

public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation.NormalForms

universe u v

variable {State : Type u} {Label : Type v}
variable {order : State → State → Prop} {family : Family State Label}
variable {source target bound first second : State}

/-- Equation (4.3) uses monotonicity of the delayed analysis and inflationarity
of the intervening analysis. -/
theorem delayed_step {a b : Analysis State}
    (simulate : MonotoneSimulation order a) (inflationary : Inflationary order b)
    (left : a source first) (right : b source second) :
    ∃ delayed, a second delayed ∧ order first delayed :=
  simulate (inflationary right) left

theorem reachable_order (refl : ∀ x, order x x) (trans : ∀ ⦃x y z⦄, order x y → order y z → order x z)
    (inflationary : ∀ label, Inflationary order (family label))
    (trace : Reachable family source target) : order source target :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.NormalForms.reachable_order refl trans inflationary trace

/-- A stable upper bound of the source covers every finite trace from it.
One-step simulation into the bound can stutter there. -/
theorem reachable_below_stable (trans : ∀ ⦃x y z⦄, order x y → order y z → order x z)
    (simulate : ∀ label, MonotoneSimulation order (family label))
    (trace : Reachable family source target) (below : order source bound)
    (stable : Stable order family bound) : order target bound :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.NormalForms.reachable_below_stable trans simulate trace below stable

theorem stable_iff_no_progress :
    Stable order family target ↔ ∀ next, ¬ Progress order family target next :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.NormalForms.stable_iff_no_progress

/-- A reachable stable state is a least stable upper bound of the source.
Together with reachability it also covers every reachable state. -/
theorem stableNormalForm_least (refl : ∀ x, order x x) (trans : ∀ ⦃x y z⦄, order x y → order y z → order x z)
    (inflationary : ∀ label, Inflationary order (family label))
    (simulate : ∀ label, MonotoneSimulation order (family label))
    (normal : StableNormalForm order family source target) :
    order source target ∧ ∀ upper, order source upper → Stable order family upper → order target upper :=
  ⟨reachable_order refl trans inflationary normal.1,
    fun _ below stable => reachable_below_stable trans simulate normal.1 below stable⟩

/-- Equation (4.4) on a preorder, with equivalence given by mutual comparison. -/
theorem stableNormalForm_unique (refl : ∀ x, order x x) (trans : ∀ ⦃x y z⦄, order x y → order y z → order x z)
    (inflationary : ∀ label, Inflationary order (family label))
    (simulate : ∀ label, MonotoneSimulation order (family label))
    (left : StableNormalForm order family source first)
    (right : StableNormalForm order family source second) :
    order first second ∧ order second first :=
  let firstBound := stableNormalForm_least refl trans inflationary simulate left
  let secondBound := stableNormalForm_least refl trans inflationary simulate right
  ⟨firstBound.2 _ secondBound.1 right.2, secondBound.2 _ firstBound.1 left.2⟩

theorem paperNormalForm_iff (refl : ∀ x, order x x) (antisymm : ∀ ⦃x y⦄, order x y → order y x → x = y)
    (inflationary : ∀ label, Inflationary order (family label)) :
    PaperNormalForm family source target ↔ StableNormalForm order family source target :=
  and_congr Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.NormalForms.paper_reachable_iff
    (Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.NormalForms.paper_terminal_iff refl antisymm inflationary)

/-- The paper's literal equality follows on a partial order, using exactly
its identity-filtered progress relation for the normal forms. -/
theorem paperNormalForm_unique (refl : ∀ x, order x x) (trans : ∀ ⦃x y z⦄, order x y → order y z → order x z)
    (antisymm : ∀ ⦃x y⦄, order x y → order y x → x = y)
    (inflationary : ∀ label, Inflationary order (family label))
    (simulate : ∀ label, MonotoneSimulation order (family label))
    (left : PaperNormalForm family source first) (right : PaperNormalForm family source second) :
    first = second :=
  let comparison := stableNormalForm_unique refl trans inflationary simulate
    ((paperNormalForm_iff refl antisymm inflationary).mp left)
    ((paperNormalForm_iff refl antisymm inflationary).mp right)
  antisymm comparison.1 comparison.2

end Silmaril.SSA.Peggy.EPEG.Saturation.NormalForms
