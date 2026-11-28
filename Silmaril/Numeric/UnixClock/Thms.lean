module

public import Silmaril.Numeric.UnixClock.Defs
import Silmaril.Proofs.Numeric.UnixClock.Civil
import Silmaril.Proofs.Numeric.UnixClock.Convention
import Silmaril.Proofs.Numeric.UnixClock.Smear

/-! # Unix clock conversion, inverse fibers and smear bounds -/

public section

namespace Silmaril.Numeric.UnixClock

open Set
open scoped ENNReal

namespace Convention

/-- An upper bound on the worst error is exactly a bound on every common sample. -/
theorem worstError_le_iff (a b : Convention) (bound : ℝ≥0∞) :
    a.worstError b ≤ bound ↔ ∀ (t : ℝ) (ha : t ∈ a.domain) (hb : t ∈ b.domain),
      ENNReal.ofReal |a.forward ⟨t, ha⟩ - b.forward ⟨t, hb⟩| ≤ bound :=
  Proofs.Numeric.UnixClock.worstError_le_iff a b bound

/-- Disjoint support gives no comparison samples and zero worst error. -/
theorem worstError_empty {a b : Convention} (h : Disjoint a.domain b.domain) :
    a.worstError b = 0 :=
  Proofs.Numeric.UnixClock.worstError_empty h

/-- Every strict lower bound is exceeded by some common sample. -/
theorem worstError_approx (a b : Convention) {bound : ℝ≥0∞} (h : bound < a.worstError b) :
    ∃ (t : ℝ) (ha : t ∈ a.domain) (hb : t ∈ b.domain),
      bound < ENNReal.ofReal |a.forward ⟨t, ha⟩ - b.forward ⟨t, hb⟩| :=
  Proofs.Numeric.UnixClock.worstError_approx a b h

/-- Infinity occurs exactly when no finite bound suffices. -/
theorem worstError_eq_top_iff (a b : Convention) :
    a.worstError b = ⊤ ↔ ∀ bound : ℝ, 0 ≤ bound →
      ∃ (t : ℝ) (ha : t ∈ a.domain) (hb : t ∈ b.domain),
        bound < |a.forward ⟨t, ha⟩ - b.forward ⟨t, hb⟩| :=
  Proofs.Numeric.UnixClock.worstError_eq_top_iff a b

/-- The supremum is attained at a sample exactly when that sample dominates every common sample. -/
theorem worstError_eq_sample_iff (a b : Convention) {t : ℝ}
    (ha : t ∈ a.domain) (hb : t ∈ b.domain) :
    a.worstError b = ENNReal.ofReal |a.forward ⟨t, ha⟩ - b.forward ⟨t, hb⟩| ↔
      ∀ (x : ℝ) (hxa : x ∈ a.domain) (hxb : x ∈ b.domain),
        ENNReal.ofReal |a.forward ⟨x, hxa⟩ - b.forward ⟨x, hxb⟩| ≤
          ENNReal.ofReal |a.forward ⟨t, ha⟩ - b.forward ⟨t, hb⟩| :=
  Proofs.Numeric.UnixClock.worstError_eq_sample_iff a b ha hb

namespace Resolver

/-- A selected inverse is a member of the physical fiber for every supported reading. -/
theorem resolve_mem_fiber {clock : Convention} (resolver : clock.Resolver) (y : resolver.domain) :
    (resolver.resolve y).val ∈ clock.fiber y.val :=
  ⟨(resolver.resolve y).property, resolver.forward_resolve y⟩

/-- Bounds for inverse comparison are in physical SI seconds at common nominal readings. -/
theorem worstError_le_iff {a b : Convention} (ra : a.Resolver) (rb : b.Resolver) (bound : ℝ≥0∞) :
    ra.worstError rb ≤ bound ↔ ∀ (y : ℝ) (ha : y ∈ ra.domain) (hb : y ∈ rb.domain),
      ENNReal.ofReal |(ra.resolve ⟨y, ha⟩).val - (rb.resolve ⟨y, hb⟩).val| ≤ bound :=
  Convention.worstError_le_iff _ _ _

end Resolver
end Convention

namespace Schedule

variable (s : Schedule)

/-- Every civil day has 86400 seconds, give or take one. -/
theorem dayLength_bounds (d : Int) : 86399 ≤ s.dayLength d ∧ s.dayLength d ≤ 86401 :=
  Proofs.Numeric.UnixClock.dayLength_bounds s d

/-- Consecutive UTC midnights are separated by the length of the earlier day. -/
theorem midnight_succ (d : Int) : s.midnight (d + 1) = s.midnight d + s.dayLength d :=
  Proofs.Numeric.UnixClock.midnight_succ s d

/-- The physical UTC midnights are strictly ordered. -/
theorem midnight_strictMono : StrictMono s.midnight :=
  Proofs.Numeric.UnixClock.midnight_strictMono s

/-- Half-open civil days cover the physical line. -/
theorem dayAt_spec (t : ℝ) :
    (s.midnight (s.dayAt t) : ℝ) ≤ t ∧ t < s.midnight (s.dayAt t + 1) :=
  Proofs.Numeric.UnixClock.dayAt_spec s t

/-- The half-open interval identifies the civil day uniquely. -/
theorem dayAt_eq_iff {t : ℝ} {d : Int} :
    s.dayAt t = d ↔ (s.midnight d : ℝ) ≤ t ∧ t < s.midnight (d + 1) :=
  Proofs.Numeric.UnixClock.dayAt_eq_iff s

/-- A valid date and valid second-of-day encode to physical midnight plus seconds. -/
theorem toTAI_eq_some_iff {label : CivilLabel} {t : ℝ} :
    s.toTAI? label = some t ↔
      ∃ d, label.date.toEpochDay? = some d ∧ s.validSecond d label.secondOfDay ∧
        t = (s.midnight d : ℝ) + label.secondOfDay :=
  Proofs.Numeric.UnixClock.toTAI_eq_some_iff s

/-- Every physical instant survives decoding to a valid UTC label and re-encoding. -/
theorem toTAI_ofTAI (t : ℝ) : s.toTAI? (s.ofTAI t) = some t :=
  Proofs.Numeric.UnixClock.toTAI_ofTAI s t

/-- Encoding a valid UTC label preserves its date and second-of-day. -/
theorem ofTAI_toTAI {label : CivilLabel} {t : ℝ} (h : s.toTAI? label = some t) :
    s.ofTAI t = label :=
  Proofs.Numeric.UnixClock.ofTAI_toTAI s h

/-- The sharp projection uses uniform nominal midnights and preserves the second-of-day. -/
theorem sharp_toTAI {label : CivilLabel} {t : ℝ} {d : Int}
    (h : s.toTAI? label = some t) (hd : label.date.toEpochDay? = some d) :
    s.sharp t = (d : ℝ) * 86400 + label.secondOfDay :=
  Proofs.Numeric.UnixClock.sharp_toTAI s h hd

/-- The instantaneous sharp correction is the effective TAI − UTC offset. -/
theorem tai_sub_sharp (t : ℝ) : t - s.sharp t = (s.taiMinusUTC t : ℝ) :=
  Proofs.Numeric.UnixClock.tai_sub_sharp s t

/-- A restriction to a single UTC day is injective and can be inverted on its exact image. -/
theorem sharpOn_injective_of_subset_day {domain : Set ℝ} {d : Int}
    (h : domain ⊆ Ico (s.midnight d : ℝ) (s.midnight (d + 1) : ℝ)) :
    Function.Injective (s.sharpOn domain).forward :=
  Proofs.Numeric.UnixClock.sharpOn_injective_of_subset_day s h

/-- A nominal reading has at most two candidates, further limited by the support of the clock. -/
theorem mem_sharp_fiber_iff {domain : Set ℝ} {t : ℝ} {d : Int} {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 86400) :
    t ∈ (s.sharpOn domain).fiber ((d : ℝ) * 86400 + u) ↔
      t ∈ domain ∧
        ((s.validSecond d u ∧ t = (s.midnight d : ℝ) + u) ∨
          (s.validSecond (d - 1) (86400 + u) ∧
            t = (s.midnight (d - 1) : ℝ) + (86400 + u))) :=
  Proofs.Numeric.UnixClock.mem_sharp_fiber_iff s hu

/-- A positive leap folds 23:59:60 and the following 00:00:00 into one nominal second. -/
theorem positive_fiber {domain : Set ℝ} {t : ℝ} {d : Int} {f : ℝ}
    (h : s.adjustment d = 1) (hf : f ∈ Ico (0 : ℝ) 1) :
    t ∈ (s.sharpOn domain).fiber ((d : ℝ) * 86400 + f) ↔
      t ∈ domain ∧
        (t = (s.midnight d : ℝ) + f ∨ t = (s.midnight d : ℝ) - 1 + f) :=
  Proofs.Numeric.UnixClock.positive_fiber s h hf

/-- A negative leap leaves an empty fiber for the deleted final nominal second. -/
theorem negative_fiber {domain : Set ℝ} {d : Int} {f : ℝ}
    (h : s.adjustment d = -1) (hf : f ∈ Ico (0 : ℝ) 1) :
    (s.sharpOn domain).fiber (((d : ℝ) - 1) * 86400 + (86399 + f)) = ∅ :=
  Proofs.Numeric.UnixClock.negative_fiber s h hf

end Schedule

namespace Ramp

/-- Outside the half-open window the step and ramp agree. -/
theorem step_eq_ramp_off_window {edge : ℝ} (ramp : Ramp edge) {t : ℝ}
    (ht : t ∉ ramp.window) : Schedule.step edge t = ramp.value t :=
  Proofs.Numeric.UnixClock.step_eq_ramp_off_window ramp ht

/-- Clamping preserves the inverse-width Lipschitz bound for a linear ramp. -/
theorem linear_ramp_abs_sub_le {edge left right : ℝ} (hlt : left < right)
    (hl : left ≤ edge) (hr : edge ≤ right) (x y : ℝ) :
    |(Ramp.linear hlt hl hr).value y - (Ramp.linear hlt hl hr).value x| ≤
      |y - x| / (right - left) :=
  Proofs.Numeric.UnixClock.linear_ramp_abs_sub_le hlt hl hr x y

end Ramp

namespace Schedule

variable (s : Schedule) (ramps : s.Ramps)

/-- Only active windows contribute to the signed difference. -/
theorem smear_sub_sharp (t : ℝ) :
    s.smear ramps t - s.sharp t =
      ∑ d ∈ s.active ramps t, ((s.leap d).seconds : ℝ) *
        (Schedule.step (s.midnight d) t - (ramps d).value t) :=
  Proofs.Numeric.UnixClock.smear_sub_sharp s ramps t

/-- Each active window contributes at most one second in absolute value. -/
theorem smear_error_le_active (t : ℝ) :
    |s.smear ramps t - s.sharp t| ≤ (s.active ramps t).card :=
  Proofs.Numeric.UnixClock.smear_error_le_active s ramps t

/-- The two clocks agree outside the union of the windows. -/
theorem smear_eq_sharp_off_windows {t : ℝ}
    (h : ∀ d ∈ s.transitions, t ∉ (ramps d).window) : s.smear ramps t = s.sharp t :=
  Proofs.Numeric.UnixClock.smear_eq_sharp_off_windows s ramps h

/-- The greatest allowed overlap bounds the worst error on any common support. -/
theorem smear_worstError_le {smearDomain sharpDomain : Set ℝ} {k : Nat}
    (h : ∀ t ∈ smearDomain ∩ sharpDomain, (s.active ramps t).card ≤ k) :
    (s.smearOn ramps smearDomain).worstError (s.sharpOn sharpDomain) ≤ k :=
  Proofs.Numeric.UnixClock.smear_worstError_le s ramps h

/-- Nonoverlapping windows give a one-second worst-case bound. -/
theorem smear_worstError_le_one {smearDomain sharpDomain : Set ℝ}
    (h : ∀ d ∈ s.transitions, ∀ e ∈ s.transitions, d ≠ e →
      Disjoint (ramps d).window (ramps e).window) :
    (s.smearOn ramps smearDomain).worstError (s.sharpOn sharpDomain) ≤ 1 :=
  Proofs.Numeric.UnixClock.smear_worstError_le_one s ramps h

/-- The one-second bound is attained at a right-edge step when its ramp starts
    there and is the only active window. -/
theorem smear_error_at_left_edge {d : Int} (h : s.active ramps (s.midnight d) = {d})
    (hleft : (ramps d).left = s.midnight d) :
    |s.smear ramps (s.midnight d) - s.sharp (s.midnight d)| = 1 :=
  Proofs.Numeric.UnixClock.smear_error_at_left_edge s ramps h hleft

/-- A finite sum of continuous ramp corrections gives a continuous clock. -/
theorem smear_continuous : Continuous (s.smear ramps) :=
  Proofs.Numeric.UnixClock.smear_continuous s ramps

/-- The full-line smear reaches every nominal reading by continuity and bounded correction. -/
theorem smear_surjective : Function.Surjective (s.smear ramps) :=
  Proofs.Numeric.UnixClock.smear_surjective s ramps

/-- A uniform upper slope bound below one on the total correction gives strict monotonicity. -/
theorem smear_strictMono {k : ℝ} (hk : k < 1)
    (h : ∀ x y : ℝ, x < y → s.correction ramps y - s.correction ramps x ≤ k * (y - x)) :
    StrictMono (s.smear ramps) :=
  Proofs.Numeric.UnixClock.smear_strictMono s ramps hk h

/-- A sum of reciprocal linear window lengths below one suffices, including with overlap. -/
theorem linear_smear_strictMono (before after : Int → ℝ)
    (hb : ∀ d, 0 ≤ before d) (ha : ∀ d, 0 ≤ after d)
    (hw : ∀ d, 0 < before d + after d)
    (hk : (∑ d ∈ s.transitions, 1 / (before d + after d)) < 1) :
    StrictMono (s.smear (s.linearRamps before after hb ha hw)) :=
  Proofs.Numeric.UnixClock.linear_smear_strictMono s before after hb ha hw hk

/-- Strictly increasing smears have a two-sided inverse on the full line.
    For supported restrictions, use the exact image of the restriction as the reverse domain. -/
noncomputable def smearEquiv (h : StrictMono (s.smear ramps)) : ℝ ≃ ℝ :=
  Equiv.ofBijective (s.smear ramps) ⟨h.injective, s.smear_surjective ramps⟩

end Schedule

/-- Ordinary Gregorian labels use exactly 86400 nominal seconds per day. -/
theorem civilToUnix_eq_some_iff {label : CivilLabel} {y : ℝ} :
    civilToUnix? label = some y ↔
      ∃ d : Int, label.date.toEpochDay? = some d ∧ 0 ≤ label.secondOfDay ∧
        label.secondOfDay < 86400 ∧ y = (d : ℝ) * 86400 + label.secondOfDay :=
  Proofs.Numeric.UnixClock.civilToUnix_eq_some_iff

/-- 1970-01-01 00:00:00 UTC has nominal Unix coordinate zero. -/
theorem civilToUnix_epoch : civilToUnix? unixEpoch = some 0 :=
  Proofs.Numeric.UnixClock.civilToUnix_epoch

/-- A whole-second UTC-instant Unix tick already uses the nominal unit. -/
theorem unixSeconds_whole (ticks : Int) :
    unixSeconds (⟨ticks⟩ : Timestamp.Ticks .utcInstant .second) = (ticks : ℝ) :=
  Proofs.Numeric.UnixClock.unixSeconds_whole ticks

/-- All nominal Unix coordinates decode and round-trip. -/
theorem civilToUnix_unixToCivil (y : ℝ) : civilToUnix? (unixToCivil y) = some y :=
  nominalSchedule.toTAI_ofTAI y

/-- Successful nominal conversion preserves the original fields. -/
theorem unixToCivil_civilToUnix {label : CivilLabel} {y : ℝ} (h : civilToUnix? label = some y) :
    unixToCivil y = label :=
  nominalSchedule.ofTAI_toTAI h

/-- Equal exact tick denotations give equal nominal second counts, across units. -/
theorem unixSeconds_eq_of_denote_eq {source target : Timestamp.TickUnit}
    {a : Timestamp.Ticks .utcInstant source} {b : Timestamp.Ticks .utcInstant target}
    (h : a.denote = b.denote) : unixSeconds a = unixSeconds b :=
  congrArg (fun stamp : Timestamp.Ticks .utcInstant .nanosecond => (stamp.ticks : ℝ) / 1000000000) h

/-- Exact handoff from nominal seconds to a signed nanosecond Unix timestamp. -/
theorem unixSeconds_nanoseconds_eq_iff (stamp : Timestamp.Ticks .utcInstant .nanosecond)
    (seconds : ℝ) : unixSeconds stamp = seconds ↔ (stamp.ticks : ℝ) = seconds * 1000000000 :=
  Proofs.Numeric.UnixClock.unixSeconds_nanoseconds_eq_iff stamp seconds

/-- A nominal reading has a unique exact timestamp precisely on the nanosecond grid. -/
theorem existsUnique_unixSeconds_nanosecond_iff (seconds : ℝ) :
    (∃! stamp : Timestamp.Ticks .utcInstant .nanosecond, unixSeconds stamp = seconds) ↔
      ∃ ticks : Int, (ticks : ℝ) = seconds * 1000000000 :=
  Proofs.Numeric.UnixClock.existsUnique_unixSeconds_nanosecond_iff seconds

/-- The historical encoder accepts exactly the valid labels in the published interval. -/
theorem iersToTAI_eq_some_iff {label : CivilLabel} {t : ℝ} :
    iersToTAI? label = some t ↔ t ∈ iersDomain ∧ iersSchedule.toTAI? label = some t :=
  Proofs.Numeric.UnixClock.iersToTAI_eq_some_iff

/-- The historical decoder accepts exactly the published physical interval. -/
theorem iersOfTAI_eq_some_iff {label : CivilLabel} {t : ℝ} :
    iersOfTAI? t = some label ↔ t ∈ iersDomain ∧ iersSchedule.ofTAI t = label :=
  Proofs.Numeric.UnixClock.iersOfTAI_eq_some_iff

/-- A supported UTC label and its physical coordinate determine each other. -/
theorem iers_roundtrip {label : CivilLabel} {t : ℝ} :
    iersToTAI? label = some t ↔ iersOfTAI? t = some label := by
  rw [iersToTAI_eq_some_iff, iersOfTAI_eq_some_iff]
  exact and_congr_right fun _ => ⟨iersSchedule.ofTAI_toTAI, fun h => h ▸ iersSchedule.toTAI_ofTAI t⟩

/-- The historical offset is defined on the same interval as the historical decoder. -/
theorem iersTAIMinusUTC_eq_some_iff {t : ℝ} {offset : Int} :
    iersTAIMinusUTC? t = some offset ↔ t ∈ iersDomain ∧ iersSchedule.taiMinusUTC t = offset := by
  by_cases ht : t ∈ iersDomain <;> simp [iersTAIMinusUTC?, iersOfTAI?, ht]

end Silmaril.Numeric.UnixClock
