module

public import Silmaril.Numeric.TimeZone.Defs

/-! # Supplied named-zone tables with whole-second transition rows -/

@[expose] public section

namespace Silmaril.Numeric.TimeZone

open Timestamp

/-- A nominal Unix cut and its inclusive new offset, both in whole seconds. -/
structure SecondTransition where
  instant : Ticks .utcInstant .second
  offsetAfterSeconds : Int

/-- Embed a supplied transition in the shared nanosecond schedule exactly. -/
def SecondTransition.toTransition (row : SecondTransition) : Transition :=
  ⟨row.instant.denote, Offset.ofSeconds row.offsetAfterSeconds⟩

/-- An opaque name and a strictly ordered table on a half-open Unix interval. -/
structure NamedZone where
  name : String
  start : Ticks .utcInstant .second
  stop : Ticks .utcInstant .second
  initialOffsetSeconds : Int
  transitions : List SecondTransition
  ordered : Schedule.Ordered start.denote stop.denote (transitions.map SecondTransition.toTransition)

/-- Resolution within the supplied interval. An ambiguous result contains at
    least two candidates and retains every additional candidate. -/
inductive LocalResolution where
  | noSolution
  | unique (instant : UnixTime)
  | ambiguous (first second : UnixTime) (rest : List UnixTime)
  deriving DecidableEq, Repr

def LocalResolution.candidates : LocalResolution → List UnixTime
  | .noSolution => []
  | .unique instant => [instant]
  | .ambiguous first second rest => first :: second :: rest

namespace NamedZone

/-- Check the support endpoints and strict ordering of the supplied cuts. -/
def ofTransitions? (name : String) (start stop : Ticks .utcInstant .second)
    (initialOffsetSeconds : Int) (transitions : List SecondTransition) : Option NamedZone :=
  if h : Schedule.Ordered start.denote stop.denote (transitions.map SecondTransition.toTransition) then
    some ⟨name, start, stop, initialOffsetSeconds, transitions, h⟩
  else none

def rules (zone : NamedZone) : Rules :=
  .scheduled ⟨zone.start.denote, zone.stop.denote, Offset.ofSeconds zone.initialOffsetSeconds,
    zone.transitions.map SecondTransition.toTransition, zone.ordered⟩

def Supports (zone : NamedZone) {unit : TickUnit} (instant : Ticks .utcInstant unit) : Prop :=
  zone.start.denote.ticks ≤ instant.denote.ticks ∧ instant.denote.ticks < zone.stop.denote.ticks

/-- Return the exact wall coordinate of a covered instant, at nanosecond precision. -/
def toLocal? (zone : NamedZone) {unit : TickUnit} (instant : Ticks .utcInstant unit) : Option WallTime :=
  zone.rules.toLocal? instant.denote

/-- Classify all covered preimages of the exact wall coordinate. -/
def resolveLocal (zone : NamedZone) {unit : TickUnit} (wall : Ticks .localReading unit) : LocalResolution :=
  match zone.rules.candidates wall.denote with
  | [] => .noSolution
  | [instant] => .unique instant
  | first :: second :: rest => .ambiguous first second rest

end NamedZone

end Silmaril.Numeric.TimeZone
