module

public import Silmaril.Languages.Python.Core.Text.Slice.Defs
import Silmaril.Proofs.Languages.Python.Core.Text.Slice.Correctness

public section
namespace Silmaril.Languages.Python.Core

theorem SliceBounds.normalize_bounds (bounds : SliceBounds) (length : Nat) :
    let slice := bounds.normalize length
    let low : Int := if slice.step < 0 then -1 else 0
    let high : Int := if slice.step < 0 then (length : Int) - 1 else length
    low ≤ slice.start ∧ slice.start ≤ high ∧ low ≤ slice.stop ∧ slice.stop ≤ high :=
  Proofs.Languages.Python.Core.Text.Slice.normalize_bounds bounds length

theorem SliceBounds.normalize_omitted (length : Nat) (step : Option Int) :
    (SliceBounds.mk none none step).normalize length =
      (if step.getD 1 < 0 then ⟨(length : Int) - 1, -1, step.getD 1⟩ else ⟨0, length, step.getD 1⟩) := by
  by_cases negative : step.getD 1 < 0 <;> simp [SliceBounds.normalize, negative]

theorem NormalizedSlice.mem_indices {length : Nat} (slice : NormalizedSlice) (index : Fin length) :
    index ∈ slice.indices length ↔ slice.selects index.val = true := by
  by_cases negative : slice.step < 0 <;> simp [NormalizedSlice.indices, negative, List.mem_finRange]

theorem NormalizedSlice.mem_indices_forward {length : Nat} (slice : NormalizedSlice)
    (index : Fin length) (forward : 0 < slice.step) :
    let i : Int := index.val
    index ∈ slice.indices length ↔ slice.start ≤ i ∧ i < slice.stop ∧ (i - slice.start) % slice.step = 0 := by
  simp [mem_indices, NormalizedSlice.selects, show ¬ slice.step < 0 by omega]

theorem NormalizedSlice.mem_indices_reverse {length : Nat} (slice : NormalizedSlice)
    (index : Fin length) (reverse : slice.step < 0) :
    let i : Int := index.val
    index ∈ slice.indices length ↔ slice.stop < i ∧ i ≤ slice.start ∧ (slice.start - i) % (-slice.step) = 0 := by
  simp [mem_indices, NormalizedSlice.selects, reverse]

theorem NormalizedSlice.indices_forward (slice : NormalizedSlice) (length : Nat) (forward : 0 ≤ slice.step) :
    (slice.indices length).Pairwise (· < ·) := by
  simpa [NormalizedSlice.indices, Int.not_lt_of_ge forward] using
    (List.pairwise_lt_finRange length).filter (fun index => slice.selects index.val)

theorem NormalizedSlice.indices_reverse (slice : NormalizedSlice) (length : Nat) (reverse : slice.step < 0) :
    (slice.indices length).Pairwise (· > ·) := by
  simpa [NormalizedSlice.indices, reverse] using
    (List.pairwise_reverse.mpr (List.pairwise_lt_finRange length)).filter (fun index => slice.selects index.val)

theorem Text.slice_zero (value : Text) (bounds : SliceBounds) (zero : bounds.step = some 0) :
    value.slice? bounds = none := by
  simp [Text.slice?, SliceBounds.normalize, zero]

theorem Text.slice_points (value : Text) (bounds : SliceBounds) (nonzero : bounds.step.getD 1 ≠ 0) :
    (value.slice? bounds).map Text.points =
      some (((bounds.normalize value.points.length).indices value.points.length).map
        fun index => value.points[index.val]) := by
  simp [Text.slice?, SliceBounds.normalize, nonzero]

end Silmaril.Languages.Python.Core
