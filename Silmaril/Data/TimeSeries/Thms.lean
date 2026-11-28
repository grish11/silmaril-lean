module

public import Silmaril.Data.TimeSeries.Defs
public import Mathlib.Topology.MetricSpace.Lipschitz
import Silmaril.Proofs.Data.TimeSeries.Errors

/-! Laws for axis maps, componentwise budgets and candidate sets. -/

@[expose] public section

namespace Silmaril.Data.TimeSeries

open scoped NNReal

namespace Series

variable {n : Nat} {Row T₁ T₂ T₃ V₁ V₂ V₃ : Type*}

@[simp] theorem get_ofRows (time : Row → T₁) (value : Row → V₁) (rows : Fin n → Row)
    (i : Fin n) : (ofRows time value rows).get i = ⟨time (rows i), value (rows i)⟩ := rfl

@[simp] theorem get_map (time : T₁ → T₂) (value : V₁ → V₂) (s : Series n T₁ V₁)
    (i : Fin n) :
    (s.map time value).get i = ⟨time (s.get i).timestamp, value (s.get i).value⟩ := rfl

@[simp] theorem get_mapTime (time : T₁ → T₂) (s : Series n T₁ V₁) (i : Fin n) :
    (s.mapTime time).get i = ⟨time (s.get i).timestamp, (s.get i).value⟩ := rfl

@[simp] theorem get_mapValue (value : V₁ → V₂) (s : Series n T₁ V₁) (i : Fin n) :
    (s.mapValue value).get i = ⟨(s.get i).timestamp, value (s.get i).value⟩ := rfl

@[simp] theorem map_id (s : Series n T₁ V₁) : s.map id id = s := rfl

theorem map_map (t₁ : T₁ → T₂) (t₂ : T₂ → T₃) (v₁ : V₁ → V₂) (v₂ : V₂ → V₃)
    (s : Series n T₁ V₁) :
    (s.map t₁ v₁).map t₂ v₂ = s.map (t₂ ∘ t₁) (v₂ ∘ v₁) := rfl

@[simp] theorem mapTime_id (s : Series n T₁ V₁) : s.mapTime id = s := map_id s

@[simp] theorem mapValue_id (s : Series n T₁ V₁) : s.mapValue id = s := map_id s

theorem mapTime_mapTime (t₁ : T₁ → T₂) (t₂ : T₂ → T₃) (s : Series n T₁ V₁) :
    (s.mapTime t₁).mapTime t₂ = s.mapTime (t₂ ∘ t₁) := rfl

theorem mapValue_mapValue (v₁ : V₁ → V₂) (v₂ : V₂ → V₃) (s : Series n T₁ V₁) :
    (s.mapValue v₁).mapValue v₂ = s.mapValue (v₂ ∘ v₁) := rfl

theorem mapTime_mapValue (time : T₁ → T₂) (value : V₁ → V₂) (s : Series n T₁ V₁) :
    (s.mapTime time).mapValue value = (s.mapValue value).mapTime time := rfl

end Series

variable {n : Nat} {Time Value Ideal : Type*}

/-- A budget on each maximum is equivalent to both budgets holding at every index. -/
theorem ErrorModel.seriesError_within_iff (model : ErrorModel ℝ Ideal Time Value) (f : ℝ → Ideal)
    (sampleTimes : Fin n → ℝ) (s : Series n Time Value) (budget : Error) :
    (model.seriesError f sampleTimes s).Within budget ↔
      ∀ i, (model.sampleError f sampleTimes s i).Within budget :=
  Proofs.Data.TimeSeries.Errors.seriesError_within_iff model f sampleTimes s budget

/-- Enlarging either budget preserves all existing candidates. -/
theorem candidates_mono_budget (model : ErrorModel ℝ Ideal Time Value) (s : Series n Time Value)
    (validTimes : (Fin n → ℝ) → Prop) (eligible : Series n Time Value → (ℝ → Ideal) → Prop)
    {small large : Error} (h : small.Within large) :
    candidates model s validTimes small eligible ⊆ candidates model s validTimes large eligible := by
  rintro f ⟨heligible, sampleTimes, hvalid, hbudget⟩
  exact ⟨heligible, sampleTimes, hvalid, hbudget.1.trans h.1, hbudget.2.trans h.2⟩

/-- Decoded equality is the zero-budget case for metric losses. -/
theorem exactCandidates_eq_candidates_zero [MetricSpace Ideal]
    (s : Series n Time Value) (decodeTime : Time → ℝ) (decodeValue : Value → Ideal)
    (validTimes : (Fin n → ℝ) → Prop) (eligible : Series n Time Value → (ℝ → Ideal) → Prop) :
    exactCandidates s decodeTime decodeValue validTimes eligible =
      candidates (ErrorModel.ofDecode decodeTime decodeValue) s validTimes ⟨0, 0⟩ eligible :=
  Proofs.Data.TimeSeries.Errors.exactCandidates_eq_candidates_zero
    s decodeTime decodeValue validTimes eligible

/-- Evaluating at the decoded recorded time adds at most the speed bound times the time budget
to the latent-time value budget. -/
theorem recorded_value_error_le [PseudoMetricSpace Ideal]
    {s : Series n Time Value} {decodeTime : Time → ℝ} {decodeValue : Value → Ideal}
    {validTimes : (Fin n → ℝ) → Prop} {budget : Error}
    {eligible : Series n Time Value → (ℝ → Ideal) → Prop} {f : ℝ → Ideal} {K : ℝ≥0}
    (hf : LipschitzWith K f)
    (h : f ∈ candidates (ErrorModel.ofDecode decodeTime decodeValue) s validTimes budget eligible)
    (i : Fin n) :
    nndist (f (decodeTime (s.get i).timestamp)) (decodeValue (s.get i).value) ≤
      budget.value + K * budget.time :=
  Proofs.Data.TimeSeries.Errors.recorded_value_error_le hf h i

end Silmaril.Data.TimeSeries
