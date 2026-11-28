module

public import Silmaril.Data.TimeSeries.CurveCandidates.Defs
import Silmaril.Proofs.Data.TimeSeries.CurveCandidates.Window

/-! Window membership can be checked directly on the interval subtype. -/

public section

namespace Silmaril.Data.TimeSeries

variable {n : Nat} {a b : ℝ} {Time Value Ideal Curve : Type*}

/-- The error test on a window evaluates the curve at a valid subtype time, with the
same per-index error and independent budgets as in the real-domain API. -/
theorem mem_windowCurveCandidates_iff (nonempty : a ≤ b) (eval : Curve → Set.Icc a b → Ideal)
    (model : ErrorModel ℝ Ideal Time Value) (s : Series n Time Value)
    (validTimes : (Fin n → ℝ) → Prop) (budget : Error) (eligible : Series n Time Value → Curve → Prop)
    {c : Curve} :
    c ∈ windowCurveCandidates nonempty eval model s validTimes budget eligible ↔
      eligible s c ∧ ∃ times : Fin n → Set.Icc a b,
        validTimes (fun i => times i) ∧
          ∀ i, (model.error ⟨times i, eval c (times i)⟩ (s.get i)).Within budget :=
  Proofs.Data.TimeSeries.CurveCandidates.mem_windowCurveCandidates_iff
    nonempty eval model s validTimes budget eligible

end Silmaril.Data.TimeSeries
