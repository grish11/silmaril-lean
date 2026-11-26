module

public import Silmaril.Data.TimeSeries.Sampling.Defs

/-! Laws for exact sampling and additive observations in the finite series representation. -/

public section

namespace Silmaril.Data.TimeSeries.Series

variable {n : Nat} {Time Value : Type*}

@[simp] theorem timestamps_ofColumns (time : Fin n → Time) (value : Fin n → Value) :
    (ofColumns time value).timestamps = time := rfl

@[simp] theorem values_ofColumns (time : Fin n → Time) (value : Fin n → Value) :
    (ofColumns time value).values = value := rfl

@[simp] theorem ofColumns_timestamps_values (s : Series n Time Value) :
    ofColumns s.timestamps s.values = s := rfl

@[simp] theorem timestamps_sample (times : Fin n → ℝ) (f : ℝ → Value) :
    (sample times f).timestamps = times := rfl

@[simp] theorem values_sample (times : Fin n → ℝ) (f : ℝ → Value) :
    (sample times f).values = Operations.sampleAt times f := rfl

@[simp] theorem timestamps_addNoise [Add Value] (s : Series n Time Value)
    (noise : Fin n → Value) : (s.addNoise noise).timestamps = s.timestamps := rfl

@[simp] theorem values_addNoise [Add Value] (s : Series n Time Value) (noise : Fin n → Value) :
    (s.addNoise noise).values = s.values + noise := rfl

end Silmaril.Data.TimeSeries.Series
