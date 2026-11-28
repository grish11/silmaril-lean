module

public import Silmaril.Numeric.Gregorian.Defs
public import Silmaril.Numeric.Timestamp.Defs

/-! # Time zone rules on nominal Unix coordinates -/

@[expose] public section

namespace Silmaril.Numeric.TimeZone

open Timestamp

/-- Signed nominal Unix nanoseconds since 1970-01-01. The caller supplies any
    conversion from a physical timescale or UTC label. -/
abbrev UnixTime := Ticks .utcInstant .nanosecond

/-- Signed local nanoseconds since local 1970-01-01 on uniform 86,400-second days. -/
abbrev WallTime := Ticks .localReading .nanosecond

/-- A signed additive displacement from nominal Unix time to local wall time. -/
structure Offset where
  nanoseconds : Int
  deriving DecidableEq, Repr

namespace Offset

def ofSeconds (seconds : Int) : Offset :=
  ⟨seconds * TickUnit.second.nanosecondsPerTick⟩

def toLocal (offset : Offset) (time : UnixTime) : WallTime :=
  ⟨time.ticks + offset.nanoseconds⟩

def fromLocal (offset : Offset) (wall : WallTime) : UnixTime :=
  ⟨wall.ticks - offset.nanoseconds⟩

end Offset

def nanosecondsPerDay : Int := 86400 * TickUnit.second.nanosecondsPerTick

/-- A Gregorian date and a zero-based within-day nanosecond count. -/
structure CivilReading where
  date : Gregorian.CivilDate
  nanosecondsOfDay : Int
  deriving DecidableEq, Repr

namespace CivilReading

/-- Euclidean division puts a pre-epoch reading on its containing civil day. -/
def ofWall (wall : WallTime) : CivilReading :=
  ⟨Gregorian.CivilDate.ofEpochDay (wall.ticks / nanosecondsPerDay),
    wall.ticks % nanosecondsPerDay⟩

/-- Invalid Gregorian dates and counts outside the uniform day yield `none`. -/
def toWall? (civil : CivilReading) : Option WallTime := do
  let day ← civil.date.toEpochDay?
  if 0 ≤ civil.nanosecondsOfDay ∧ civil.nanosecondsOfDay < nanosecondsPerDay then
    some ⟨day * nanosecondsPerDay + civil.nanosecondsOfDay⟩
  else
    none

end CivilReading

/-- A transition starts using `offsetAfter` at `instant`, inclusive. -/
structure Transition where
  instant : UnixTime
  offsetAfter : Offset

/-- A half-open nominal Unix interval with a constant offset. -/
structure Segment where
  start : UnixTime
  stop : UnixTime
  offset : Offset

namespace Segment

def Contains (segment : Segment) (time : UnixTime) : Prop :=
  segment.start.ticks ≤ time.ticks ∧ time.ticks < segment.stop.ticks

instance (segment : Segment) (time : UnixTime) : Decidable (segment.Contains time) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The translated half-open interval on the wall coordinate. -/
def ContainsWall (segment : Segment) (wall : WallTime) : Prop :=
  (segment.offset.toLocal segment.start).ticks ≤ wall.ticks ∧
    wall.ticks < (segment.offset.toLocal segment.stop).ticks

instance (segment : Segment) (wall : WallTime) : Decidable (segment.ContainsWall wall) :=
  inferInstanceAs (Decidable (_ ∧ _))

def candidate? (segment : Segment) (wall : WallTime) : Option UnixTime :=
  let time := segment.offset.fromLocal wall
  if segment.Contains time then some time else none

end Segment

namespace Schedule

/-- Every transition lies strictly inside the support and the list is increasing. -/
def Ordered (start stop : UnixTime) : List Transition → Prop
  | [] => start.ticks < stop.ticks
  | transition :: rest =>
    start.ticks < transition.instant.ticks ∧ Ordered transition.instant stop rest

instance orderedDecidable (start stop : UnixTime) (transitions : List Transition) :
    Decidable (Ordered start stop transitions) :=
  match transitions with
  | [] => inferInstanceAs (Decidable (start.ticks < stop.ticks))
  | transition :: rest =>
    letI := orderedDecidable transition.instant stop rest
    inferInstanceAs (Decidable (start.ticks < transition.instant.ticks ∧ Ordered transition.instant stop rest))

namespace Internal

def segmentsFrom (start stop : UnixTime) (offset : Offset) : List Transition → List Segment
  | [] => [⟨start, stop, offset⟩]
  | transition :: rest =>
    ⟨start, transition.instant, offset⟩ :: segmentsFrom transition.instant stop transition.offsetAfter rest

end Internal
end Schedule

/-- A dated transition schedule valid on the explicit support `[start, stop)`. -/
structure Schedule where
  start : UnixTime
  stop : UnixTime
  initial : Offset
  transitions : List Transition
  ordered : Schedule.Ordered start stop transitions

namespace Schedule

/-- Check both support endpoints and the strict order of the transition dates. -/
def ofTransitions? (start stop : UnixTime) (initial : Offset)
    (transitions : List Transition) : Option Schedule :=
  if h : Ordered start stop transitions then some ⟨start, stop, initial, transitions, h⟩ else none

def Supports (schedule : Schedule) (time : UnixTime) : Prop :=
  schedule.start.ticks ≤ time.ticks ∧ time.ticks < schedule.stop.ticks

def segments (schedule : Schedule) : List Segment :=
  Internal.segmentsFrom schedule.start schedule.stop schedule.initial schedule.transitions

def offsetAt? (schedule : Schedule) (time : UnixTime) : Option Offset :=
  schedule.segments.findSome? fun segment =>
    if segment.Contains time then some segment.offset else none

end Schedule

/-- A total fixed offset or a transition schedule with a finite validity horizon. -/
inductive Rules where
  | fixed (offset : Offset)
  | scheduled (schedule : Schedule)

inductive ResolvePolicy where
  | unique
  | earliest
  | latest

namespace Rules

def Supports (rules : Rules) (time : UnixTime) : Prop :=
  match rules with
  | .fixed _ => True
  | .scheduled schedule => schedule.Supports time

def offsetAt? (rules : Rules) (time : UnixTime) : Option Offset :=
  match rules with
  | .fixed offset => some offset
  | .scheduled schedule => schedule.offsetAt? time

def toLocal? (rules : Rules) (time : UnixTime) : Option WallTime :=
  (rules.offsetAt? time).map (·.toLocal time)

def toCivil? (rules : Rules) (time : UnixTime) : Option CivilReading :=
  (rules.toLocal? time).map CivilReading.ofWall

/-- The inverse relation on the nominal Unix coordinate. -/
def Matches (rules : Rules) (wall : WallTime) (time : UnixTime) : Prop :=
  rules.toLocal? time = some wall

/-- All supported nominal Unix readings of a wall coordinate, in increasing order. -/
def candidates (rules : Rules) (wall : WallTime) : List UnixTime :=
  match rules with
  | .fixed offset => [offset.fromLocal wall]
  | .scheduled schedule => schedule.segments.filterMap (·.candidate? wall)

/-- An invalid civil reading yields `none`. A valid reading with no supported candidate
    yields `some []`. -/
def civilCandidates? (rules : Rules) (civil : CivilReading) : Option (List UnixTime) :=
  civil.toWall?.map rules.candidates

/-- Select from existing candidates. Empty candidate lists fail under every policy.
    The unique policy also fails for a fold. -/
def resolve? (rules : Rules) (wall : WallTime) : ResolvePolicy → Option UnixTime
  | .unique =>
    match rules.candidates wall with
    | [time] => some time
    | _ => none
  | .earliest => (rules.candidates wall).head?
  | .latest => (rules.candidates wall).getLast?

/-- A common range of offsets, in signed nanoseconds, for all supported inputs. -/
def OffsetsWithin (rules : Rules) (lower upper : Int) : Prop :=
  match rules with
  | .fixed offset => lower ≤ offset.nanoseconds ∧ offset.nanoseconds ≤ upper
  | .scheduled schedule =>
    ∀ segment ∈ schedule.segments, lower ≤ segment.offset.nanoseconds ∧
      segment.offset.nanoseconds ≤ upper

end Rules
end Silmaril.Numeric.TimeZone
