module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Real
public import Silmaril.Numeric.Gregorian.Defs
public import Silmaril.Numeric.Timestamp.Defs

/-! # Unix clock coordinates and supported conventions

A physical coordinate is an SI-second count from 1970-01-01 00:00:00 TAI.
A nominal coordinate is a Gregorian count from the label 1970-01-01 00:00:00 UTC,
with 86400 nominal seconds per day. Each convention specifies its physical domain.
-/

@[expose] public section

namespace Silmaril.Numeric.UnixClock

open Set
open scoped ENNReal
open Gregorian (CivilDate)

noncomputable section

/-- A partial forward convention on normalized physical seconds, with readings in nominal seconds. -/
structure Convention where
  domain : Set ℝ
  forward : domain → ℝ

/-- All supported physical instants having the specified reading. -/
def Convention.fiber (clock : Convention) (reading : ℝ) : Set ℝ :=
  {t | ∃ h : t ∈ clock.domain, clock.forward ⟨t, h⟩ = reading}

/-- An explicitly selected branch of the inverse relation on a specified set of readings. -/
structure Convention.Resolver (clock : Convention) where
  domain : Set ℝ
  resolve : domain → clock.domain
  forward_resolve : ∀ y, clock.forward (resolve y) = y.val

/-- Invert an injective restriction on its exact image. -/
def Convention.equivRange (clock : Convention) (h : Function.Injective clock.forward) :
    clock.domain ≃ Set.range clock.forward :=
  Equiv.ofInjective clock.forward h

/-- Turn a one-to-one supported convention into a resolver on its exact image. -/
def Convention.resolverOfInjective (clock : Convention) (h : Function.Injective clock.forward) :
    clock.Resolver where
  domain := Set.range clock.forward
  resolve := (clock.equivRange h).symm
  forward_resolve := fun y => congrArg Subtype.val ((clock.equivRange h).apply_symm_apply y)

/-- View a resolver as a partial function in the other direction, for error comparisons. -/
def Convention.Resolver.asConvention {clock : Convention} (resolver : clock.Resolver) : Convention :=
  ⟨resolver.domain, fun y => (resolver.resolve y).val⟩

/-- The least upper bound of absolute errors in seconds on the intersection of the domains.
    The empty comparison has value zero and an unbounded comparison has value infinity. -/
def Convention.worstError (a b : Convention) : ℝ≥0∞ :=
  ⨆ t : ↑(a.domain ∩ b.domain),
    ENNReal.ofReal |a.forward ⟨t.val, t.property.1⟩ - b.forward ⟨t.val, t.property.2⟩|

/-- Compare selected physical instants only on the readings supported by both resolvers. -/
def Convention.Resolver.worstError {a b : Convention} (ra : a.Resolver) (rb : b.Resolver) :
    ℝ≥0∞ :=
  ra.asConvention.worstError rb.asConvention

/-- A UTC label carries a Gregorian date and elapsed seconds since that day's midnight.
    On a positive leap day, [86400, 86401) denotes 23:59:60 with its fractional part. -/
@[ext] structure CivilLabel where
  date : CivilDate
  secondOfDay : ℝ

/-- The civil label at nominal Unix zero. -/
def unixEpoch : CivilLabel := ⟨⟨1970, 1, 1⟩, 0⟩

/-- Exact normalization of the existing UTC-instant Unix ticks to nominal seconds. -/
def unixSeconds {unit : Timestamp.TickUnit} (stamp : Timestamp.Ticks .utcInstant unit) : ℝ :=
  (stamp.denote.ticks : ℝ) / 1000000000

/-- Signed unit changes of TAI minus nominal UTC. -/
inductive Leap where
  | positive | negative
  deriving DecidableEq, Repr

def Leap.seconds : Leap → Int
  | .positive => 1
  | .negative => -1

/-- Finite UTC transitions keyed by the signed Gregorian day of the first midnight
    after the leap. The baseline is TAI minus nominal UTC before all listed transitions.
    The sign is used only on listed transitions. -/
structure Schedule where
  baseline : Int
  transitions : Finset Int
  leap : Int → Leap

namespace Schedule

variable (schedule : Schedule)

/-- The accumulated offset at the beginning of the given day. -/
def offset (day : Int) : Int :=
  ∑ d ∈ schedule.transitions.filter (· ≤ day), (schedule.leap d).seconds

/-- Physical TAI seconds at UTC midnight, with the origin at 1970-01-01 00:00:00 TAI. -/
def midnight (day : Int) : Int :=
  day * 86400 + schedule.baseline + schedule.offset day

/-- The change applied at the given midnight. -/
def adjustment (day : Int) : Int :=
  if day ∈ schedule.transitions then (schedule.leap day).seconds else 0

/-- The physical length of a UTC day, including any insertion or deletion at its end. -/
def dayLength (day : Int) : Int := 86400 + schedule.adjustment (day + 1)

/-- Valid second-of-day readings on the given UTC day. -/
def validSecond (day : Int) (second : ℝ) : Prop :=
  0 ≤ second ∧ second < schedule.dayLength day

instance (day : Int) (second : ℝ) : Decidable (schedule.validSecond day second) :=
  inferInstanceAs (Decidable (0 ≤ second ∧ second < (schedule.dayLength day : ℝ)))

/-- Convert a civil label to physical seconds, rejecting invalid dates and labels. -/
def toTAI? (label : CivilLabel) : Option ℝ := do
  let day ← label.date.toEpochDay?
  if schedule.validSecond day label.secondOfDay then
    some ((schedule.midnight day : ℝ) + label.secondOfDay)
  else none

/-- The day whose physical midnight is the last one at or before the instant. -/
def dayAt (t : ℝ) : Int := sSup {d : Int | (schedule.midnight d : ℝ) ≤ t}

/-- Recover the Gregorian UTC label on the day containing this physical instant.
    The generic finite schedule extends by a constant offset on both tails. -/
def ofTAI (t : ℝ) : CivilLabel :=
  ⟨CivilDate.ofEpochDay (schedule.dayAt t), t - schedule.midnight (schedule.dayAt t)⟩

/-- TAI minus UTC in integral seconds. A positive leap label uses the offset
    of the day on which it occurs, up to the following midnight. -/
def taiMinusUTC (t : ℝ) : Int := schedule.baseline + schedule.offset (schedule.dayAt t)

/-- Right-edge step: the new offset applies from the transition midnight inclusive. -/
def step (edge t : ℝ) : ℝ := if edge ≤ t then 1 else 0

/-- The right-edge sharp clock repeats the first nominal second after a positive leap
    and skips the last nominal second before a negative leap. -/
def sharp (t : ℝ) : ℝ :=
  t - schedule.baseline -
    ∑ d ∈ schedule.transitions, ((schedule.leap d).seconds : ℝ) * step (schedule.midnight d) t

/-- Sharp clock exposed on an explicitly supported physical domain. -/
def sharpOn (domain : Set ℝ) : Convention := ⟨domain, fun t => schedule.sharp t⟩

end Schedule

/-- Uniform Gregorian days, used for the nominal epoch conversion. -/
def nominalSchedule : Schedule := ⟨0, ∅, fun _ => .positive⟩

/-- Encode ordinary Gregorian labels in nominal Unix seconds. -/
def civilToUnix? (label : CivilLabel) : Option ℝ := nominalSchedule.toTAI? label

/-- Decode nominal Unix seconds into ordinary Gregorian fields. -/
def unixToCivil (seconds : ℝ) : CivilLabel := nominalSchedule.ofTAI seconds

/-- A continuous nondecreasing unit ramp whose endpoints bracket the sharp step.
    The endpoints may coincide with the step, with a strictly positive window length. -/
structure Ramp (edge : ℝ) where
  left : ℝ
  right : ℝ
  left_lt_right : left < right
  left_le_edge : left ≤ edge
  edge_le_right : edge ≤ right
  value : ℝ → ℝ
  continuous_value : Continuous value
  monotone_value : Monotone value
  range_value : ∀ t, value t ∈ Icc 0 1
  before : ∀ t ≤ left, value t = 0
  after : ∀ t ≥ right, value t = 1

/-- The half-open window containing all possible disagreements with the right-edge step. -/
def Ramp.window {edge : ℝ} (ramp : Ramp edge) : Set ℝ := Ico ramp.left ramp.right

instance {edge : ℝ} (ramp : Ramp edge) (t : ℝ) : Decidable (t ∈ ramp.window) :=
  inferInstanceAs (Decidable (ramp.left ≤ t ∧ t < ramp.right))

/-- A clamped linear ramp. Its value is continuous, with corners at the two endpoints. -/
def Ramp.linear {edge : ℝ} {left right : ℝ} (hlt : left < right)
    (hl : left ≤ edge) (hr : edge ≤ right) : Ramp edge where
  left := left
  right := right
  left_lt_right := hlt
  left_le_edge := hl
  edge_le_right := hr
  value t := min 1 (max 0 ((t - left) / (right - left)))
  continuous_value := continuous_const.min (continuous_const.max
    ((continuous_id.sub continuous_const).div_const _))
  monotone_value _ _ h := min_le_min_left _ (max_le_max_left _
    (div_le_div_of_nonneg_right (sub_le_sub_right h _) (sub_nonneg.mpr hlt.le)))
  range_value _ := ⟨le_min zero_le_one (le_max_left ..), min_le_left ..⟩
  before t ht := by rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht)
    (sub_nonneg.mpr hlt.le)), min_eq_right zero_le_one]
  after t ht := by rw [min_eq_left (le_max_of_le_right
    ((le_div_iff₀ (sub_pos.mpr hlt)).mpr (by simpa using sub_le_sub_right ht left)))]

namespace Schedule

variable (schedule : Schedule)

/-- A ramp for each transition. Ramps at days outside the schedule are ignored. -/
abbrev Ramps := (d : Int) → Ramp (schedule.midnight d : ℝ)

/-- Clamped linear ramps with per-transition durations before and after midnight. -/
def linearRamps (before after : Int → ℝ) (hb : ∀ d, 0 ≤ before d) (ha : ∀ d, 0 ≤ after d)
    (hwidth : ∀ d, 0 < before d + after d) : schedule.Ramps := fun d =>
  Ramp.linear (left := (schedule.midnight d : ℝ) - before d)
    (right := (schedule.midnight d : ℝ) + after d)
    (sub_lt_iff_lt_add.mpr (by rw [add_assoc, add_comm (after d)]; exact lt_add_of_pos_right _ (hwidth d)))
    (sub_le_self _ (hb d)) (le_add_of_nonneg_right (ha d))

/-- The days whose smear windows are active at this physical instant. -/
def active (ramps : schedule.Ramps) (t : ℝ) : Finset Int :=
  schedule.transitions.filter fun d => t ∈ (ramps d).window

/-- The signed sum of the ramp corrections. -/
def correction (ramps : schedule.Ramps) (t : ℝ) : ℝ :=
  ∑ d ∈ schedule.transitions, ((schedule.leap d).seconds : ℝ) * (ramps d).value t

/-- The same scale and baseline as the sharp clock, with continuous corrections. -/
def smear (ramps : schedule.Ramps) (t : ℝ) : ℝ := t - schedule.baseline - schedule.correction ramps t

/-- The smeared clock exposed on an explicitly supported physical domain. -/
def smearOn (ramps : schedule.Ramps) (domain : Set ℝ) : Convention :=
  ⟨domain, fun t => schedule.smear ramps t⟩

end Schedule

/-- The historical step-era UTC table, from the IERS Leap_Second.dat revision
    through Bulletin C 72 (July 2026). All changes in this snapshot are positive.
    The first row supplies the initial offset of 10 seconds on 1972-01-01. -/
def iersSchedule : Schedule where
  baseline := 10
  transitions :=
    {912, 1096, 1461, 1826, 2191, 2557, 2922, 3287, 3652, 4199, 4564, 4929, 5660,
      6574, 7305, 7670, 8217, 8582, 8947, 9496, 10043, 10592, 13149, 14245, 15522,
      16617, 17167}
  leap := fun _ => .positive

/-- First supported Gregorian day (1972-01-01). -/
def iersFirstDay : Int := 730

/-- Exclusive Gregorian bound at the table expiry (2027-06-28). -/
def iersEndDay : Int := 20997

/-- The supported physical interval for the published snapshot. -/
def iersDomain : Set ℝ :=
  Ico (iersSchedule.midnight iersFirstDay : ℝ) (iersSchedule.midnight iersEndDay : ℝ)

instance (t : ℝ) : Decidable (t ∈ iersDomain) :=
  inferInstanceAs (Decidable ((iersSchedule.midnight iersFirstDay : ℝ) ≤ t ∧
    t < (iersSchedule.midnight iersEndDay : ℝ)))

/-- The POSIX-shaped right-edge projection of the published UTC step model.
    The forward convention is supported only on the published interval. -/
def iersUnix : Convention := iersSchedule.sharpOn iersDomain

/-- Convert a valid UTC label only when its instant is within the published interval. -/
def iersToTAI? (label : CivilLabel) : Option ℝ := do
  let t ← iersSchedule.toTAI? label
  if t ∈ iersDomain then some t else none

/-- Decode a physical instant only when it is within the published interval. -/
def iersOfTAI? (t : ℝ) : Option CivilLabel :=
  if t ∈ iersDomain then some (iersSchedule.ofTAI t) else none

/-- The published TAI − UTC offset at a supported physical instant. -/
def iersTAIMinusUTC? (t : ℝ) : Option Int :=
  (iersOfTAI? t).map fun _ => iersSchedule.taiMinusUTC t

end

end Silmaril.Numeric.UnixClock
