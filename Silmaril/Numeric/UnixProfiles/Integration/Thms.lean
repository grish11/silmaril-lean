module

public import Silmaril.Numeric.UnixProfiles.Integration.Defs
import Silmaril.Proofs.Numeric.UnixProfiles.Integration

/-! Exact alignment of the supported conventions with the one-event software profiles. -/

public section

namespace Silmaril.Numeric.UnixProfiles.Integration

open UnixClock (Schedule)
open scoped ENNReal

/-- Google's active ramp window includes the actual transition midnight. -/
theorem google_midnight_mem_window (s : Schedule) (day : Int) :
    (s.midnight day : ℝ) ∈ (googleRamps s day).window :=
  Proofs.Numeric.UnixProfiles.Integration.google_midnight_mem_window s day

/-- The Java ramp includes the actual transition midnight as its right endpoint,
    where it is complete. The core's half-open active window excludes that endpoint. -/
theorem java_midnight_endpoint (s : Schedule) (day : Int) :
    (javaRamps s day).right = (s.midnight day : ℝ) ∧
      (javaRamps s day).value (s.midnight day : ℝ) = 1 ∧
      (s.midnight day : ℝ) ∉ (javaRamps s day).window :=
  Proofs.Numeric.UnixProfiles.Integration.java_midnight_endpoint s day

theorem oneEvent_midnight (leap : Leap) (offset day : Int) :
    ((oneEvent leap offset day).midnight day : ℝ) =
      physicalNoon offset day + leap.midnight :=
  Proofs.Numeric.UnixProfiles.Integration.oneEvent_midnight leap offset day

theorem google_forward (leap : Leap) (offset day : Int) (domain : Set ℝ) (t : domain) :
    ((oneEvent leap offset day).smearOn (googleRamps (oneEvent leap offset day)) domain).forward t =
      googleSmear leap (nominalNoon day) (t.val - physicalNoon offset day) :=
  Proofs.Numeric.UnixProfiles.Integration.google_forward leap offset day domain t

theorem java_forward (leap : Leap) (offset day : Int) (domain : Set ℝ) (t : domain) :
    ((oneEvent leap offset day).smearOn (javaRamps (oneEvent leap offset day)) domain).forward t =
      javaUtcSls leap (nominalNoon day) (t.val - physicalNoon offset day) :=
  Proofs.Numeric.UnixProfiles.Integration.java_forward leap offset day domain t

/-- The supported Linux map is the core schedule step sum with just the
positive edges moved one physical second earlier. -/
theorem linuxOn_eq_shifted_steps (s : Schedule) (domain : Set ℝ) (t : domain) :
    (linuxOn s domain).forward t = t.val - (s.baseline : ℝ) -
      ∑ day ∈ s.transitions, ((s.leap day).seconds : ℝ) *
        Schedule.step ((s.midnight day : ℝ) - if s.leap day = .positive then 1 else 0) t.val :=
  Proofs.Numeric.UnixProfiles.Integration.linuxOn_eq_shifted_steps s domain t

theorem linux_forward (leap : Leap) (offset day : Int) (domain : Set ℝ) (t : domain) :
    (linuxOn (oneEvent leap offset day) domain).forward t =
      linuxRealtime leap (nominalNoon day) (t.val - physicalNoon offset day) :=
  Proofs.Numeric.UnixProfiles.Integration.linux_forward leap offset day domain t

/-- With the correct initial offset, the same-instant configured Linux
TAI reading on the core coordinate is the physical input. -/
theorem linux_configured_tai (leap : Leap) (offset day : Int) (domain : Set ℝ) (t : domain) :
    (linuxOn (oneEvent leap offset day) domain).forward t +
      ((offset : ℝ) + linuxLeapAdjustment leap (t.val - physicalNoon offset day)) = t.val :=
  Proofs.Numeric.UnixProfiles.Integration.linux_configured_tai leap offset day domain t

/-- The positive Linux fold shares the preceding nominal second. Each
candidate is retained only if it belongs to the supplied support. -/
theorem linux_positive_fiber (offset day : Int) {domain : Set ℝ} {t f : ℝ}
    (hf : f ∈ Set.Ico (0 : ℝ) 1) :
    t ∈ (linuxOn (oneEvent .insert offset day) domain).fiber (nominalNoon day + 43199 + f) ↔
      t ∈ domain ∧ (t = physicalNoon offset day + 43199 + f ∨
        t = physicalNoon offset day + 43200 + f) :=
  Proofs.Numeric.UnixProfiles.Integration.linux_positive_fiber offset day hf

/-- The positive Linux reading is one nominal second below the core sharp
    reading during the inserted second, with equality elsewhere. -/
theorem sharp_linux_insert_delta (offset day : Int) (domain : Set ℝ) (t : domain) :
    let s := oneEvent .insert offset day
    let m : ℝ := s.midnight day
    (s.sharpOn domain).forward t - (linuxOn s domain).forward t =
      if m - 1 ≤ t.val ∧ t.val < m then 1 else 0 :=
  Proofs.Numeric.UnixProfiles.Integration.sharp_linux_insert_delta offset day domain t

/-- On the supplied support, the positive sharp and Linux readings disagree
    precisely on the half-open inserted second. -/
theorem sharp_linux_insert_disagrees (offset day : Int) (domain : Set ℝ) (t : domain) :
    let s := oneEvent .insert offset day
    (s.sharpOn domain).forward t ≠ (linuxOn s domain).forward t ↔
      t.val ∈ insertedSecond offset day :=
  Proofs.Numeric.UnixProfiles.Integration.sharp_linux_insert_disagrees offset day domain t

/-- For a single deletion, both clocks step at the actual UTC midnight. -/
theorem sharp_linux_delete_forward (offset day : Int) (domain : Set ℝ) (t : domain) :
    let s := oneEvent .delete offset day
    (s.sharpOn domain).forward t = (linuxOn s domain).forward t :=
  Proofs.Numeric.UnixProfiles.Integration.sharp_linux_delete_forward offset day domain t

/-- The positive supremum is one second exactly when the support meets the
    inserted second. Otherwise the two readings agree on the support. -/
theorem sharp_linux_insert_worstError (offset day : Int) (domain : Set ℝ) :
    let s := oneEvent .insert offset day
    let error := (s.sharpOn domain).worstError (linuxOn s domain)
    (error = 1 ↔ (domain ∩ insertedSecond offset day).Nonempty) ∧
    (error = 0 ↔ ¬ (domain ∩ insertedSecond offset day).Nonempty) :=
  Proofs.Numeric.UnixProfiles.Integration.sharp_linux_insert_worstError offset day domain

/-- The positive bound on the full physical line is attained at the
start of the inserted second. -/
theorem sharp_linux_insert_worstError_univ (offset day : Int) :
    let s := oneEvent .insert offset day
    (s.sharpOn Set.univ).worstError (linuxOn s Set.univ) = 1 :=
  Proofs.Numeric.UnixProfiles.Integration.sharp_linux_insert_worstError_univ offset day

/-- The two single-deletion clocks have zero worst error on any support. -/
theorem sharp_linux_delete_worstError (offset day : Int) (domain : Set ℝ) :
    let s := oneEvent .delete offset day
    (s.sharpOn domain).worstError (linuxOn s domain) = 0 :=
  Proofs.Numeric.UnixProfiles.Integration.sharp_linux_delete_worstError offset day domain

/-- All six real optimal bounds become exact core worst errors on any shared
domain containing the physical noon-to-noon window of a single event. -/
theorem oneEvent_worstErrors (leap : Leap) (offset day : Int) (domain : Set ℝ)
    (hdom : Set.Icc (physicalNoon offset day) (physicalNoon offset day + leap.googleEnd) ⊆
      domain) :
    let s := oneEvent leap offset day
    let g := s.smearOn (googleRamps s) domain
    let j := s.smearOn (javaRamps s) domain
    let l := linuxOn s domain
    g.worstError l = ENNReal.ofReal
      (googleLinuxBound leap) ∧
    g.worstError j = ENNReal.ofReal
      (googleJavaBound leap) ∧
    j.worstError l = ENNReal.ofReal
      (javaLinuxBound leap) :=
  Proofs.Numeric.UnixProfiles.Integration.oneEvent_worstErrors leap offset day domain hdom

end Silmaril.Numeric.UnixProfiles.Integration
