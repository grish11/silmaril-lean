module

public import Silmaril.Data.TimeSeries.Defs
public import Silmaril.Data.TimeSeries.Operations.Defs

/-! Sample a real-domain function into a series, and perturb its values at fixed timestamps. -/

@[expose] public section

namespace Silmaril.Data.TimeSeries.Series

variable {n : Nat} {Time Value : Type*}

/-- Read the recorded timestamps in index order. -/
def timestamps (s : Series n Time Value) : Fin n → Time :=
  fun i => (s.get i).timestamp

/-- Read the recorded values in the same index order as the timestamps. -/
def values (s : Series n Time Value) : Fin n → Value :=
  fun i => (s.get i).value

/-- Build a series from timestamp and value columns aligned on the same index. -/
def ofColumns (time : Fin n → Time) (value : Fin n → Value) : Series n Time Value :=
  ⟨fun i => ⟨time i, value i⟩⟩

/-- Record the supplied times and their exact evaluations under `f`. -/
def sample (times : Fin n → ℝ) (f : ℝ → Value) : Series n ℝ Value :=
  ofColumns times (Operations.sampleAt times f)

/-- Add one value error per index, retaining the series' recorded timestamps. -/
def addNoise [Add Value] (s : Series n Time Value) (noise : Fin n → Value) : Series n Time Value :=
  ofColumns s.timestamps (s.values + noise)

end Silmaril.Data.TimeSeries.Series
