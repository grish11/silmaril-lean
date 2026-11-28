module

public import Silmaril.Numeric.UnixClock.Defs
public import Silmaril.Numeric.UnixProfiles.Defs
import Mathlib.Tactic.NormNum

/-! Supported software clock conventions on the core's physical TAI axis. -/

@[expose] public section

namespace Silmaril.Numeric.UnixProfiles.Integration

open UnixClock (Convention Schedule)

noncomputable section

/-- Google ramps around each physical transition midnight. -/
def googleRamps (s : Schedule) : s.Ramps :=
  s.linearRamps (fun day => 43200 + ((s.leap day).seconds : ℝ)) (fun _ => 43200)
    (by intro day; cases s.leap day <;> norm_num [UnixClock.Leap.seconds])
    (by intro; norm_num)
    (by intro day; cases s.leap day <;> norm_num [UnixClock.Leap.seconds])

/-- Java UTC-SLS ramps end at each physical transition midnight. -/
def javaRamps (s : Schedule) : s.Ramps :=
  s.linearRamps (fun _ => 1000) (fun _ => 0)
    (by intro; norm_num) (fun _ => le_rfl) (by intro; norm_num)

/-- Each positive Linux step is one physical second earlier than the core step. -/
def linuxOn (s : Schedule) (domain : Set ℝ) : Convention :=
  ⟨domain, fun t => s.sharp t.val - ∑ day ∈ s.transitions,
    if s.leap day = .positive ∧
        (s.midnight day : ℝ) - 1 ≤ t.val ∧ t.val < (s.midnight day : ℝ)
      then 1 else 0⟩

/-- Map the profile sign to the corresponding core leap. -/
def coreLeap : Leap → UnixClock.Leap
  | .insert => .positive
  | .delete => .negative

/-- A core schedule with just the event under comparison, at the given epoch day. -/
def oneEvent (leap : Leap) (offset day : Int) : Schedule :=
  ⟨offset, {day}, fun _ => coreLeap leap⟩

/-- Unix reading at noon before the transition keyed by `day`. -/
def nominalNoon (day : Int) : ℝ := (day : ℝ) * 86400 - 43200

/-- TAI coordinate of that noon with pre-leap offset `offset`. -/
def physicalNoon (offset day : Int) : ℝ := nominalNoon day + offset

/-- Physical interval of the inserted second, before the core midnight cut. -/
def insertedSecond (offset day : Int) : Set ℝ :=
  let m : ℝ := (oneEvent .insert offset day).midnight day
  Set.Ico (m - 1) m

/-- Exact one-event absolute error for Google versus Linux. -/
def googleLinuxBound : Leap → ℝ
  | .insert => 43201 / 86401
  | .delete => 43200 / 86399

/-- Exact one-event absolute error for Google versus Java. -/
def googleJavaBound : Leap → ℝ
  | .insert => 43200 / 86401
  | .delete => 43200 / 86399

/-- Exact one-event absolute error for Java versus Linux. -/
def javaLinuxBound : Leap → ℝ
  | .insert => 999 / 1000
  | .delete => 1

end

end Silmaril.Numeric.UnixProfiles.Integration
