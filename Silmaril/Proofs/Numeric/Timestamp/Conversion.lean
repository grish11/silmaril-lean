module

public import Silmaril.Numeric.Timestamp.Defs

public section

namespace Silmaril.Proofs.Numeric.Timestamp

open Silmaril.Numeric.Timestamp

variable {kind : Kind} {source target : TickUnit}

private theorem scale_ne_zero (unit : TickUnit) : unit.nanosecondsPerTick ≠ 0 := by
  cases unit <;> decide

theorem rescale_eq_some_iff {value : Ticks kind source} {result : Ticks kind target} :
    value.rescale target = some result ↔ value.denote = result.denote := by
  constructor
  · intro h
    simp only [Ticks.rescale] at h
    split at h
    next exactTick =>
      cases Option.some.inj h
      exact congrArg Ticks.mk (Int.ediv_mul_cancel_of_emod_eq_zero exactTick).symm
    next => contradiction
  · intro h
    have sameOffset := congrArg Ticks.ticks h
    change value.denote.ticks = result.ticks * target.nanosecondsPerTick at sameOffset
    cases result
    simp [Ticks.rescale, sameOffset, scale_ne_zero]

theorem toInt64_eq_ok_iff {value : Ticks kind source} {payload : Int64} :
    value.toInt64 target = .ok payload ↔ value.denote = (Ticks.ofInt64 kind target payload).denote := by
  constructor
  · intro h
    unfold Ticks.toInt64 at h
    split at h
    next => contradiction
    next result hRescale =>
      split at h
      next bounds =>
        cases Except.ok.inj h
        simpa [Ticks.ofInt64] using rescale_eq_some_iff.mp hRescale
      next => contradiction
  · intro h
    have hRescale := rescale_eq_some_iff.mpr h
    have bounds : Int64.minValue.toInt ≤ payload.toInt ∧ payload.toInt ≤ Int64.maxValue.toInt :=
      ⟨payload.minValue_le_toInt, payload.toInt_le⟩
    simp only [Ticks.toInt64, hRescale, Ticks.ofInt64, dite_eq_left bounds, Int64.ofIntLE_toInt]

end Silmaril.Proofs.Numeric.Timestamp
