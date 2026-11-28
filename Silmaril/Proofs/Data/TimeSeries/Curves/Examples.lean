module

import Silmaril.Data.TimeSeries.Curves.Thms
import Mathlib.Tactic.Linarith

/-! Small checks of the public curve API, including the distinction between a class and its trace. -/

namespace Silmaril.Proofs.Data.TimeSeries.Curves.Examples

open Set
open Silmaril.Data.TimeSeries.Curves
open scoped ContDiff Manifold Silmaril.Data.TimeSeries.Curves

noncomputable section

private def openId : OpenSmooth 𝓘(ℝ) ℝ := ⟨id, contMDiff_id⟩

private theorem shift_mem (s : ℝ) : Equiv.addRight s ∈ Reparam.openIncreasing := by
  refine ⟨⟨?_, ?_⟩, fun _ _ h => add_lt_add_left h s⟩
  · exact (contDiff_id.add contDiff_const).contMDiff
  · rw [Equiv.addRight_symm]
    exact (contDiff_id.add contDiff_const).contMDiff

-- Translation of the clock preserves the open oriented class.
example (s : ℝ) :
    OpenSmooth.toOriented (openId.comp (Reparam.smoothMap 𝓘(ℝ) (Equiv.addRight s)
      (shift_mem s).1)) =
      openId.toOriented :=
  SmoothClass.mk_precomp (Reparam.increasing_le_diffeomorphisms (T := ℝ) 𝓘(ℝ)) openId (shift_mem s)

-- A finite window uses the original times and includes both endpoints.
example {a b : ℝ} [Fact (a < b)] :
    (openId.window a b).toOriented.start = a ∧ (openId.window a b).toOriented.finish = b :=
  ⟨rfl, rfl⟩

-- Ambient constructions and quotient endpoints agree on the closed interval.
example :
    (ClosedSmooth.ofContMDiffOn (I := 𝓘(ℝ)) id contMDiff_id.contMDiffOn).toOriented.finish = 1 :=
  rfl

private def closedId : ClosedSmooth (𝓡∂ 1) unitInterval := ⟨id, contMDiff_id⟩

private def reverseClock : Equiv.Perm unitInterval := unitInterval.symmHomeomorph.toEquiv

private theorem reverse_mem : reverseClock ∈ Reparam.diffeomorphisms (𝓡∂ 1) := by
  have h : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ unitInterval.symm := by
    refine contMDiff_iff_comp_subtypeVal_Icc.mpr ⟨unitInterval.continuous_symm, ?_⟩
    exact (contDiff_const.sub contDiff_id : ContDiff ℝ ∞ (fun t : ℝ => 1 - t)).contMDiff.comp
      contMDiff_subtypeVal_Icc
  exact ⟨h, h⟩

private def closedReverse : ClosedSmooth (𝓡∂ 1) unitInterval :=
  closedId.comp (Reparam.smoothMap (𝓡∂ 1) reverseClock reverse_mem)

-- The target may itself be a manifold with boundary.
example : closedId.toOriented.start = 0 ∧ closedId.toOriented.finish = 1 := ⟨rfl, rfl⟩

-- Reversal swaps the interval endpoints and changes the oriented class.
example : closedReverse.toOriented.start = 1 ∧ closedReverse.toOriented.finish = 0 :=
  ⟨unitInterval.symm_zero, unitInterval.symm_one⟩

example : closedId.toOriented ≠ closedReverse.toOriented := by
  intro h
  have hstart := congrArg (fun q : OrientedClosedSmooth (𝓡∂ 1) unitInterval => q.start) h
  exact zero_ne_one (hstart.trans unitInterval.symm_zero)

-- The two representatives agree after allowing reversal of the smooth clock.
example : closedReverse.toOriented.forgetOrientation = closedId.toOriented.forgetOrientation :=
  SmoothClass.mk_precomp le_rfl closedId reverse_mem

private def fold (t : unitInterval) : ℝ := |2 * (t : ℝ) - 1|

private theorem range_fold : range fold = unitInterval := by
  apply Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    exact ⟨abs_nonneg _, abs_le.mpr ⟨by linarith [t.2.1], by linarith [t.2.2]⟩⟩
  · intro y hy
    have hy₀ := hy.1
    have hy₁ := hy.2
    refine ⟨⟨(y + 1) / 2, by constructor <;> linarith⟩, ?_⟩
    have h : 2 * ((y + 1) / 2) - 1 = y := by linarith
    exact (congrArg abs h).trans (abs_of_nonneg hy₀)

-- Equal traces can still have different fibers up to any time bijection.
example : (Unparametrized.mk fold).trace =
    (Unparametrized.mk (fun t : unitInterval => (t : ℝ))).trace :=
  range_fold.trans Subtype.range_coe.symm

example : Unparametrized.mk (fun t : unitInterval => (t : ℝ)) ≠ Unparametrized.mk fold := by
  intro h
  obtain ⟨e, he⟩ := Unparametrized.mk_eq_mk_iff.mp h
  have hInj : Function.Injective fold := by
    rw [show fold = (fun t : unitInterval => (t : ℝ)) ∘ e from funext he]
    exact Subtype.coe_injective.comp e.injective
  exact zero_ne_one (hInj (show fold 0 = fold 1 by norm_num [fold]))

end

end Silmaril.Proofs.Data.TimeSeries.Curves.Examples
