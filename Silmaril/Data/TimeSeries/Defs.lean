module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-! Finite observations with typed recorded timestamps and values, and their
compatibility with real-domain functions under separate time and value losses. -/

@[expose] public section

namespace Silmaril.Data.TimeSeries

open scoped NNReal

/-- A recorded timestamp and a recorded value may have different types. -/
structure Observation (Time Value : Type*) where
  timestamp : Time
  value : Value

/-- Samples are ordered by their shared index. Timestamps may repeat or be out of order. -/
structure Series (n : Nat) (Time Value : Type*) where
  get : Fin n → Observation Time Value

namespace Series

variable {n : Nat} {Row Time Time' Value Value' : Type*}

/-- Project two typed columns from an already ordered collection of rows. -/
def ofRows (timestamp : Row → Time) (value : Row → Value) (rows : Fin n → Row) :
    Series n Time Value :=
  ⟨fun i => ⟨timestamp (rows i), value (rows i)⟩⟩

/-- Transform the two axes without changing their shared index. -/
def map (time : Time → Time') (value : Value → Value') (s : Series n Time Value) :
    Series n Time' Value' :=
  ofRows (time ∘ Observation.timestamp) (value ∘ Observation.value) s.get

def mapTime (time : Time → Time') (s : Series n Time Value) : Series n Time' Value :=
  s.map time id

def mapValue (value : Value → Value') (s : Series n Time Value) : Series n Time Value' :=
  s.map id value

end Series

/-- A nonnegative loss from an ideal value to a recorded value. Custom losses
can be asymmetric and can have their own notion of zero error. -/
abbrev Loss (Ideal Recorded : Type*) := Ideal → Recorded → ℝ≥0

namespace Loss

/-- Compare an ideal value with the decoded recording in the ideal space. -/
noncomputable def ofDecode {Ideal Recorded : Type*} [PseudoMetricSpace Ideal]
    (decode : Recorded → Ideal) : Loss Ideal Recorded :=
  fun ideal recorded => nndist ideal (decode recorded)

end Loss

/-- Time and value errors, also used for the corresponding independent budgets. -/
structure Error where
  time : ℝ≥0
  value : ℝ≥0

/-- Each error component must fit its own budget. -/
def Error.Within (error budget : Error) : Prop :=
  error.time ≤ budget.time ∧ error.value ≤ budget.value

/-- The two recording losses may use different ideal and recorded types. -/
structure ErrorModel (IdealTime IdealValue RecordedTime RecordedValue : Type*) where
  timeLoss : Loss IdealTime RecordedTime
  valueLoss : Loss IdealValue RecordedValue

namespace ErrorModel

variable {IdealTime IdealValue RecordedTime RecordedValue : Type*}

def error (model : ErrorModel IdealTime IdealValue RecordedTime RecordedValue)
    (ideal : Observation IdealTime IdealValue) (recorded : Observation RecordedTime RecordedValue) :
    Error :=
  ⟨model.timeLoss ideal.timestamp recorded.timestamp, model.valueLoss ideal.value recorded.value⟩

/-- Decode each recorded axis and compare it with its ideal counterpart. -/
noncomputable def ofDecode [PseudoMetricSpace IdealTime] [PseudoMetricSpace IdealValue]
    (decodeTime : RecordedTime → IdealTime) (decodeValue : RecordedValue → IdealValue) :
    ErrorModel IdealTime IdealValue RecordedTime RecordedValue :=
  ⟨Loss.ofDecode decodeTime, Loss.ofDecode decodeValue⟩

variable {n : Nat}

/-- Error at the latent sample time. Recorded timestamps enter only through the time loss. -/
def sampleError (model : ErrorModel ℝ IdealValue RecordedTime RecordedValue)
    (f : ℝ → IdealValue) (sampleTimes : Fin n → ℝ) (s : Series n RecordedTime RecordedValue)
    (i : Fin n) : Error :=
  model.error ⟨sampleTimes i, f (sampleTimes i)⟩ (s.get i)

/-- The componentwise maximum over the sample indices. The empty series has zero error. -/
noncomputable def seriesError (model : ErrorModel ℝ IdealValue RecordedTime RecordedValue)
    (f : ℝ → IdealValue) (sampleTimes : Fin n → ℝ) (s : Series n RecordedTime RecordedValue) :
    Error :=
  ⟨Finset.univ.sup (fun i => (model.sampleError f sampleTimes s i).time),
    Finset.univ.sup (fun i => (model.sampleError f sampleTimes s i).value)⟩

end ErrorModel

variable {n : Nat} {Time Value Ideal : Type*}

/-- A candidate admits one valid latent schedule for both budgets. A validity
predicate may constrain individual times or the whole schedule, including
their order. Eligibility may depend on the observed series. -/
def candidates (model : ErrorModel ℝ Ideal Time Value) (s : Series n Time Value)
    (validTimes : (Fin n → ℝ) → Prop) (budget : Error)
    (eligible : Series n Time Value → (ℝ → Ideal) → Prop := fun _ _ => True) :
    Set (ℝ → Ideal) :=
  {f | eligible s f ∧
    ∃ sampleTimes, validTimes sampleTimes ∧ (model.seriesError f sampleTimes s).Within budget}

/-- Exact matching uses the decoded recorded timestamps as the sample times
and requires equality with every decoded recorded value. -/
def exactCandidates (s : Series n Time Value) (decodeTime : Time → ℝ)
    (decodeValue : Value → Ideal) (validTimes : (Fin n → ℝ) → Prop)
    (eligible : Series n Time Value → (ℝ → Ideal) → Prop := fun _ _ => True) :
    Set (ℝ → Ideal) :=
  let sampleTimes := fun i => decodeTime (s.get i).timestamp
  {f | eligible s f ∧ validTimes sampleTimes ∧
    ∀ i, f (sampleTimes i) = decodeValue (s.get i).value}

end Silmaril.Data.TimeSeries
