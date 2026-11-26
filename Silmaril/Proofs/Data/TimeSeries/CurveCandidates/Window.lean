module

public import Silmaril.Data.TimeSeries.CurveCandidates.Defs
import Silmaril.Data.TimeSeries.Curves.Thms
import Silmaril.Data.TimeSeries.Thms

public section

namespace Silmaril.Proofs.Data.TimeSeries.CurveCandidates

open Silmaril.Data.TimeSeries

variable {n : Nat} {a b : ℝ} {Time Value Ideal Curve : Type*}

theorem mem_windowCurveCandidates_iff (nonempty : a ≤ b) (eval : Curve → Set.Icc a b → Ideal)
    (model : ErrorModel ℝ Ideal Time Value) (s : Series n Time Value)
    (validTimes : (Fin n → ℝ) → Prop) (budget : Error) (eligible : Series n Time Value → Curve → Prop)
    {c : Curve} :
    c ∈ windowCurveCandidates nonempty eval model s validTimes budget eligible ↔
      eligible s c ∧ ∃ times : Fin n → Set.Icc a b,
        validTimes (fun i => times i) ∧
          ∀ i, (model.error ⟨times i, eval c (times i)⟩ (s.get i)).Within budget := by
  constructor
  · rintro ⟨he, -, times, ⟨hv, hm⟩, hb⟩
    let schedule (i : Fin n) : Set.Icc a b := ⟨times i, hm i⟩
    refine ⟨he, schedule, hv, fun i => ?_⟩
    have hs := (ErrorModel.seriesError_within_iff _ _ _ _ _).mp hb i
    change (model.error ⟨schedule i, Curves.Window.extend nonempty (eval c) (schedule i)⟩
      (s.get i)).Within budget at hs
    simpa only [Curves.Window.extend_apply] using hs
  · rintro ⟨he, times, hv, hb⟩
    refine ⟨he, trivial, fun i => times i, ⟨hv, fun i => (times i).2⟩,
      (ErrorModel.seriesError_within_iff _ _ _ _ _).mpr (fun i => ?_)⟩
    simpa only [ErrorModel.sampleError, Curves.Window.extend_apply] using hb i

end Silmaril.Proofs.Data.TimeSeries.CurveCandidates
