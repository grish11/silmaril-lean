module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# Exact operations on finite signals

Samples are functions `Fin n → A`, and timestamps are functions `Fin n → ℝ`.
The two share their index type and can be supplied independently of any observation type.
Sampling evaluates a signal at the given times. Interpolation, slopes and filters specify
exact real arithmetic on real vector spaces. These specifications supply no floating-point
implementation or rounding guarantees.
-/

@[expose] public section

namespace Silmaril.Data.TimeSeries.Operations

open scoped BigOperators

variable {n : ℕ} {A : Type*}

/-- Evaluate `f` at each timestamp in index order. Empty grids give empty samples.
Repeated timestamps repeat the same evaluation. -/
def sampleAt (times : Fin n → ℝ) (f : ℝ → A) : Fin n → A :=
  fun i => f (times i)

/-- The grid starts at `start` and uses the signed step `step`.
A zero step repeats the start, and a negative step gives descending timestamps. -/
noncomputable def uniformTimes (start step : ℝ) (n : ℕ) : Fin n → ℝ :=
  fun i => start + (i.val : ℝ) * step

/-- Evaluate a signal on the uniform grid. -/
noncomputable def sampleUniform (start step : ℝ) (n : ℕ) (f : ℝ → A) : Fin n → A :=
  sampleAt (uniformTimes start step n) f

/-- First sample index of an adjacent pair. There are no pairs for zero or one sample. -/
def segmentLeft (i : Fin (n - 1)) : Fin n :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- Second sample index of an adjacent pair. -/
def segmentRight (i : Fin (n - 1)) : Fin n :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

/-- Forward differences are right sample minus left sample, one per adjacent pair. -/
def forwardDiff [Sub A] (x : Fin n → A) : Fin (n - 1) → A :=
  fun i => x (segmentRight i) - x (segmentLeft i)

variable [AddCommGroup A] [Module ℝ A]

/-- Divide each forward difference by its signed time step. An equal-time pair gives
`none` at that index. A descending pair uses a negative denominator. -/
noncomputable def forwardSlope? (times : Fin n → ℝ) (x : Fin n → A) :
    Fin (n - 1) → Option A := fun i =>
  let dt := forwardDiff times i
  if dt = 0 then none else some (dt⁻¹ • forwardDiff x i)

/-- Affine interpolation between `x₀` at `t₀` and `x₁` at `t₁`.
The formula extrapolates outside the interval and also accepts reversed endpoints.
If the times coincide it returns `x₀` at every query, using Lean's exact `r / 0 = 0`. -/
noncomputable def linearInterpolate (t₀ t₁ : ℝ) (x₀ x₁ : A) (t : ℝ) : A :=
  let u := (t - t₀) / (t₁ - t₀)
  (1 - u) • x₀ + u • x₁

/-- Interpolate on an adjacent pair when the query lies between its timestamps, including both
endpoints. The interpolation uses the signed time step in index order. An equal-time pair
accepts only its common time and returns the left sample. -/
noncomputable def interpolateSegment? (times : Fin n → ℝ) (x : Fin n → A)
    (i : Fin (n - 1)) (t : ℝ) : Option A :=
  let l := segmentLeft i
  let r := segmentRight i
  if min (times l) (times r) ≤ t ∧ t ≤ max (times l) (times r) then
    some (linearInterpolate (times l) (times r) (x l) (x r) t)
  else none

/-- Query a finite grid by time. An exact match takes priority over interpolation, and repeated
timestamps select the sample with the least index. Otherwise, use the bracketing adjacent pair
with the least left index, whether the pair's timestamps rise or fall. Return `none` if neither
search succeeds. On a strictly monotone grid this is piecewise linear interpolation with no
extrapolation. An empty grid always gives `none`. A singleton matches only at its timestamp. -/
noncomputable def interpolateGrid? (times : Fin n → ℝ) (x : Fin n → A) (t : ℝ) :
    Option A :=
  match (List.finRange n).find? (fun i => decide (times i = t)) with
  | some i => some (x i)
  | none => (List.finRange (n - 1)).findSome? (fun i => interpolateSegment? times x i t)

/-- A normalized weighted sum. A smoothing window can give weight zero to samples outside
the window and use one row of weights per desired output. Weights may be signed.
If the total weight is zero, including the empty case, the result is zero. -/
noncomputable def weightedMean (weights : Fin n → ℝ) (x : Fin n → A) : A :=
  (∑ i, weights i)⁻¹ • ∑ i, weights i • x i

/-- Exponential moving average with the seed as the state before the first sample.
At each index the output is `(1 - alpha) • previous + alpha • current`.
Alpha zero retains the seed and alpha one passes the samples through. The usual smoothing
range is `0 ≤ alpha ≤ 1`, and the recurrence is defined for all real alpha.
An empty input has no outputs. -/
noncomputable def ema (alpha : ℝ) (seed : A) : {n : ℕ} → (Fin n → A) → Fin n → A
  | 0, _ => Fin.elim0
  | _ + 1, x =>
    Fin.induction ((1 - alpha) • seed + alpha • x 0)
      (fun i prev => (1 - alpha) • prev + alpha • x i.succ)

end Silmaril.Data.TimeSeries.Operations
