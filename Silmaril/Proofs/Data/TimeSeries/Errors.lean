module

public import Silmaril.Data.TimeSeries.Defs
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

namespace Silmaril.Proofs.Data.TimeSeries.Errors

open Silmaril.Data.TimeSeries
open scoped NNReal

variable {n : Nat} {Time Value Ideal : Type*}

theorem seriesError_within_iff (model : ErrorModel ℝ Ideal Time Value) (f : ℝ → Ideal)
    (sampleTimes : Fin n → ℝ) (s : Series n Time Value) (budget : Error) :
    (model.seriesError f sampleTimes s).Within budget ↔
      ∀ i, (model.sampleError f sampleTimes s i).Within budget := by
  constructor
  · intro h i
    exact ⟨(Finset.le_sup (f := fun j => (model.sampleError f sampleTimes s j).time)
        (Finset.mem_univ i)).trans h.1,
      (Finset.le_sup (f := fun j => (model.sampleError f sampleTimes s j).value)
        (Finset.mem_univ i)).trans h.2⟩
  · intro h
    exact ⟨Finset.sup_le fun i _ => (h i).1, Finset.sup_le fun i _ => (h i).2⟩

theorem exactCandidates_eq_candidates_zero [MetricSpace Ideal]
    (s : Series n Time Value) (decodeTime : Time → ℝ) (decodeValue : Value → Ideal)
    (validTimes : (Fin n → ℝ) → Prop) (eligible : Series n Time Value → (ℝ → Ideal) → Prop) :
    exactCandidates s decodeTime decodeValue validTimes eligible =
      candidates (ErrorModel.ofDecode decodeTime decodeValue) s validTimes ⟨0, 0⟩ eligible := by
  ext f
  constructor
  · rintro ⟨heligible, hvalid, hmatch⟩
    refine ⟨heligible, fun i => decodeTime (s.get i).timestamp, hvalid,
      (seriesError_within_iff _ _ _ _ _).2 ?_⟩
    intro i
    change nndist (decodeTime (s.get i).timestamp) (decodeTime (s.get i).timestamp) ≤ 0 ∧
      nndist (f (decodeTime (s.get i).timestamp)) (decodeValue (s.get i).value) ≤ 0
    simp [hmatch i]
  · rintro ⟨heligible, sampleTimes, hvalid, hbudget⟩
    have hsample := (seriesError_within_iff _ _ _ _ _).1 hbudget
    have htimes (i : Fin n) : sampleTimes i = decodeTime (s.get i).timestamp :=
      nndist_eq_zero.mp (le_antisymm (hsample i).1 zero_le)
    have hs : sampleTimes = fun i => decodeTime (s.get i).timestamp := funext htimes
    subst sampleTimes
    exact ⟨heligible, hvalid, fun i => nndist_eq_zero.mp (le_antisymm (hsample i).2 zero_le)⟩

theorem recorded_value_error_le [PseudoMetricSpace Ideal]
    {s : Series n Time Value} {decodeTime : Time → ℝ} {decodeValue : Value → Ideal}
    {validTimes : (Fin n → ℝ) → Prop} {budget : Error}
    {eligible : Series n Time Value → (ℝ → Ideal) → Prop} {f : ℝ → Ideal} {K : ℝ≥0}
    (hf : LipschitzWith K f)
    (h : f ∈ candidates (ErrorModel.ofDecode decodeTime decodeValue) s validTimes budget eligible)
    (i : Fin n) :
    nndist (f (decodeTime (s.get i).timestamp)) (decodeValue (s.get i).value) ≤
      budget.value + K * budget.time := by
  obtain ⟨_, sampleTimes, _, hbudget⟩ := h
  obtain ⟨htime, hvalue⟩ := (seriesError_within_iff _ _ _ _ _).1 hbudget i
  change nndist (sampleTimes i) (decodeTime (s.get i).timestamp) ≤ budget.time at htime
  change nndist (f (sampleTimes i)) (decodeValue (s.get i).value) ≤ budget.value at hvalue
  calc
    _ ≤ nndist (f (decodeTime (s.get i).timestamp)) (f (sampleTimes i)) +
        nndist (f (sampleTimes i)) (decodeValue (s.get i).value) :=
      nndist_triangle _ _ _
    _ ≤ K * budget.time + budget.value := by
      apply add_le_add _ hvalue
      refine (hf.nndist_le _ _).trans ?_
      rw [nndist_comm (decodeTime (s.get i).timestamp)]
      exact mul_le_mul_of_nonneg_left htime zero_le
    _ = _ := add_comm _ _

end Silmaril.Proofs.Data.TimeSeries.Errors
