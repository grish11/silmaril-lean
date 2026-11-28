module

public import Silmaril.Numeric.TimeZone.Defs
public import Silmaril.Numeric.UnixClock.Defs

/-! # Exact handoff between physical clocks and nominal time zone rules -/

@[expose] public section

namespace Silmaril.Numeric.UnixInterop

open TimeZone UnixClock

/-- Give the unique signed nanosecond stamp if the real reading lies on the exact grid. -/
noncomputable def exactNanoseconds? (seconds : ℝ) : Option UnixTime := by
  classical
  let ticks : Int := ⌊seconds * 1000000000⌋
  exact if (ticks : ℝ) = seconds * 1000000000 then some ⟨ticks⟩ else none

/-- The clock support is carried by the input. Off-grid readings and readings outside
    the zone rule's nominal horizon return `none`. -/
noncomputable def readWall? (clock : Convention) (rules : Rules) (t : clock.domain) :
    Option WallTime :=
  (exactNanoseconds? (clock.forward t)).bind rules.toLocal?

/-- Read Gregorian fields in the local, uniform-day coordinate. -/
noncomputable def readCivil? (clock : Convention) (rules : Rules) (t : clock.domain) :
    Option CivilReading :=
  (readWall? clock rules t).map CivilReading.ofWall

/-- All supported physical instants for this wall reading, retaining every nominal
    zone candidate and every instant in each clock fiber. -/
def physicalCandidates (clock : Convention) (rules : Rules) (wall : WallTime) : Set ℝ :=
  {t | ∃ stamp ∈ rules.candidates wall, t ∈ clock.fiber (unixSeconds stamp)}

/-- The length of one payload tick in normalized nominal seconds. -/
noncomputable def tickSeconds (unit : Timestamp.TickUnit) : ℝ :=
  (unit.nanosecondsPerTick : ℝ) / 1000000000

end Silmaril.Numeric.UnixInterop
