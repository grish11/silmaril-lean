module

import Silmaril.Data.TimeSeries.Operations.Thms
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-! # Kernel-checked examples of exact finite signal operations -/

namespace Silmaril.Data.TimeSeries.Operations

/-- The third time of the grid starting at one with step two is five. -/
example : sampleUniform 1 2 3 (fun t : ℝ => t ^ 2) (2 : Fin 3) = 25 := by
  norm_num [sampleUniform, sampleAt, uniformTimes]

/-- The sample difference is six and the elapsed time is two. -/
example : forwardSlope? (uniformTimes 0 2 2) ![(1 : ℝ), 7] 0 = some 3 := by
  rw [forwardSlope?_uniform _ _ (by norm_num)]
  norm_num [forwardDiff, segmentLeft, segmentRight, smul_eq_mul]

example : forwardSlope? ![(2 : ℝ), 2] ![(1 : ℝ), 7] 0 = none := by
  rw [forwardSlope?_eq_none_iff]
  rfl

/-- The grid interpolates between adjacent samples on a query between timestamps. -/
example : interpolateGrid? ![(0 : ℝ), 2] ![(1 : ℝ), 7] 1 = some 4 := by
  norm_num [interpolateGrid?, List.finRange_succ, interpolateSegment?, linearInterpolate,
    segmentLeft, segmentRight, smul_eq_mul]

/-- A duplicated timestamp returns the first matching sample. -/
example : interpolateGrid? ![(2 : ℝ), 2] ![(1 : ℝ), 7] 2 = some 1 := by
  simp [interpolateGrid?, List.finRange_succ]

example : interpolateGrid? ![(0 : ℝ), 2] ![(1 : ℝ), 7] 3 = none := by
  norm_num [interpolateGrid?, List.finRange_succ, interpolateSegment?, segmentLeft, segmentRight]

example : interpolateGrid? (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) 0 = none := rfl

example : weightedMean ![(1 : ℝ), 3] ![(2 : ℝ), 6] = 5 := by
  norm_num [weightedMean, Fin.sum_univ_two, smul_eq_mul]

/-- Half weight on each new sample gives outputs two and then four from seed zero. -/
example : ema (1 / 2) 0 ![(4 : ℝ), 6] (Fin.succ (0 : Fin 1)) = 4 := by
  rw [ema_succ, show (0 : Fin 1).castSucc = (0 : Fin 2) from rfl, ema_first]
  norm_num [smul_eq_mul]

end Silmaril.Data.TimeSeries.Operations
