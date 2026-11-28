module

public import Silmaril.Numeric.UnixProfiles.Integration.Defs
public import Silmaril.Numeric.UnixClock.Thms
public import Silmaril.Numeric.UnixProfiles.Thms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.Proofs.Numeric.UnixProfiles.Integration

open Silmaril.Numeric.UnixClock (Convention Schedule)
open Silmaril.Numeric.UnixProfiles
open Silmaril.Numeric.UnixProfiles.Integration
open scoped ENNReal

theorem google_midnight_mem_window (s : Schedule) (day : Int) :
    (s.midnight day : ℝ) ∈ (googleRamps s day).window := by
  let m : ℝ := s.midnight day
  change m - (43200 + ((s.leap day).seconds : ℝ)) ≤ m ∧ m < m + 43200
  have h : 0 ≤ 43200 + ((s.leap day).seconds : ℝ) := by
    cases s.leap day <;> norm_num [Silmaril.Numeric.UnixClock.Leap.seconds]
  exact ⟨sub_le_self _ h, by linarith⟩

theorem java_midnight_endpoint (s : Schedule) (day : Int) :
    (javaRamps s day).right = (s.midnight day : ℝ) ∧
      (javaRamps s day).value (s.midnight day : ℝ) = 1 ∧
      (s.midnight day : ℝ) ∉ (javaRamps s day).window := by
  have hr : (javaRamps s day).right = (s.midnight day : ℝ) := by
    change (s.midnight day : ℝ) + 0 = (s.midnight day : ℝ)
    exact add_zero _
  refine ⟨hr, (javaRamps s day).after _ hr.le, ?_⟩
  intro hmem
  exact (not_lt_of_ge hr.le) hmem.2

private theorem sign_eq (leap : Leap) : leap.sign = ((coreLeap leap).seconds : ℝ) := by
  cases leap <;> norm_num [Leap.sign, coreLeap, Silmaril.Numeric.UnixClock.Leap.seconds]

theorem oneEvent_midnight (leap : Leap) (offset day : Int) :
    ((oneEvent leap offset day).midnight day : ℝ) =
      physicalNoon offset day + leap.midnight := by
  have hf : ({day} : Finset Int).filter (· ≤ day) = {day} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨And.left, fun h => ⟨h, h.le⟩⟩
  simp only [oneEvent, Schedule.midnight, Schedule.offset, hf, Finset.sum_singleton,
    Int.cast_add, Int.cast_mul, Int.cast_ofNat, ← sign_eq]
  unfold physicalNoon nominalNoon Leap.midnight
  ring

private theorem google_value (leap : Leap) (offset day : Int) (t : ℝ) :
    (googleRamps (oneEvent leap offset day) day).value t =
      min 1 (max 0 ((t - physicalNoon offset day) / leap.googleEnd)) := by
  let m : ℝ := (oneEvent leap offset day).midnight day
  change min 1 (max 0 ((t - (m - (43200 + ((coreLeap leap).seconds : ℝ)))) /
    ((m + 43200) - (m - (43200 + ((coreLeap leap).seconds : ℝ)))))) = _
  rw [← sign_eq]
  have hleft : m - (43200 + leap.sign) = physicalNoon offset day := by
    dsimp [m]
    rw [oneEvent_midnight, Leap.midnight]
    ring
  have hwidth : m + 43200 - physicalNoon offset day = leap.googleEnd := by
    dsimp [m]
    rw [oneEvent_midnight, Leap.midnight, Leap.googleEnd]
    ring
  rw [hleft, hwidth]

private theorem java_value (leap : Leap) (offset day : Int) (t : ℝ) :
    (javaRamps (oneEvent leap offset day) day).value t =
      min 1 (max 0 ((t - physicalNoon offset day - leap.javaStart) / 1000)) := by
  let m : ℝ := (oneEvent leap offset day).midnight day
  change min 1 (max 0 ((t - (m - 1000)) / ((m + 0) - (m - 1000)))) = _
  rw [add_zero, show m - (m - 1000) = 1000 by ring]
  have h : t - (m - 1000) = t - physicalNoon offset day - leap.javaStart := by
    dsimp [m]
    rw [oneEvent_midnight, Leap.javaStart]
    ring
  rw [h]

private theorem unshifted_reading (offset day : Int) (t : ℝ) :
    t - (offset : ℝ) = nominalNoon day + (t - physicalNoon offset day) := by
  unfold physicalNoon
  ring

theorem google_forward (leap : Leap) (offset day : Int) (domain : Set ℝ) (t : domain) :
    ((oneEvent leap offset day).smearOn (googleRamps (oneEvent leap offset day)) domain).forward t =
      googleSmear leap (nominalNoon day) (t.val - physicalNoon offset day) := by
  change (oneEvent leap offset day).smear (googleRamps (oneEvent leap offset day)) t.val = _
  rw [Schedule.smear, Schedule.correction]
  rw [show (oneEvent leap offset day).transitions = {day} from rfl, Finset.sum_singleton]
  change t.val - (offset : ℝ) - ((coreLeap leap).seconds : ℝ) *
    (googleRamps (oneEvent leap offset day) day).value t.val = _
  rw [google_value, ← sign_eq]
  unfold googleSmear
  rw [unshifted_reading]

theorem java_forward (leap : Leap) (offset day : Int) (domain : Set ℝ) (t : domain) :
    ((oneEvent leap offset day).smearOn (javaRamps (oneEvent leap offset day)) domain).forward t =
      javaUtcSls leap (nominalNoon day) (t.val - physicalNoon offset day) := by
  change (oneEvent leap offset day).smear (javaRamps (oneEvent leap offset day)) t.val = _
  rw [Schedule.smear, Schedule.correction]
  rw [show (oneEvent leap offset day).transitions = {day} from rfl, Finset.sum_singleton]
  change t.val - (offset : ℝ) - ((coreLeap leap).seconds : ℝ) *
    (javaRamps (oneEvent leap offset day) day).value t.val = _
  rw [java_value, ← sign_eq]
  unfold javaUtcSls
  rw [unshifted_reading]

private theorem step_one_early (m t : ℝ) :
    Schedule.step (m - 1) t = Schedule.step m t + (if m - 1 ≤ t ∧ t < m then 1 else 0) := by
  by_cases late : m ≤ t
  · have early : m - 1 ≤ t := by linarith
    simp [Schedule.step, late, early, not_lt.mpr late]
  · by_cases early : m - 1 ≤ t
    · simp [Schedule.step, late, early, lt_of_not_ge late]
    · simp [Schedule.step, late, early]

theorem linuxOn_eq_shifted_steps (s : Schedule) (domain : Set ℝ) (t : domain) :
    (linuxOn s domain).forward t = t.val - (s.baseline : ℝ) -
      ∑ day ∈ s.transitions, ((s.leap day).seconds : ℝ) *
        Schedule.step ((s.midnight day : ℝ) - if s.leap day = .positive then 1 else 0) t.val := by
  dsimp only [linuxOn, Schedule.sharp]
  conv_lhs => rw [sub_sub, ← Finset.sum_add_distrib]
  apply congrArg (fun v : ℝ => t.val - (s.baseline : ℝ) - v)
  apply Finset.sum_congr rfl
  intro day _
  cases s.leap day <;> simp [Silmaril.Numeric.UnixClock.Leap.seconds, step_one_early]

private theorem adjustment_eq_step (leap : Leap) (noon t : ℝ) :
    linuxLeapAdjustment leap (t - noon) = leap.sign * Schedule.step (noon + leap.linuxStep) t := by
  by_cases h : noon + leap.linuxStep ≤ t
  · have hx : leap.linuxStep ≤ t - noon := by linarith
    simp [linuxLeapAdjustment, Schedule.step, hx, h]
  · have hx : ¬ leap.linuxStep ≤ t - noon := by
      intro hx
      exact h (by linarith)
    simp [linuxLeapAdjustment, Schedule.step, hx, h]

private theorem linux_edge (leap : Leap) (noon : ℝ) :
    noon + leap.midnight - (if coreLeap leap = .positive then 1 else 0) =
      noon + leap.linuxStep := by
  cases leap with
  | insert =>
    norm_num [Leap.linuxStep, Leap.midnight, Leap.sign, coreLeap]
    ring
  | delete => norm_num [Leap.linuxStep, Leap.midnight, Leap.sign, coreLeap]

theorem linux_forward (leap : Leap) (offset day : Int) (domain : Set ℝ) (t : domain) :
    (linuxOn (oneEvent leap offset day) domain).forward t =
      linuxRealtime leap (nominalNoon day) (t.val - physicalNoon offset day) := by
  rw [linuxOn_eq_shifted_steps,
    show (oneEvent leap offset day).transitions = {day} from rfl, Finset.sum_singleton]
  change t.val - (offset : ℝ) - ((coreLeap leap).seconds : ℝ) *
    Schedule.step (((oneEvent leap offset day).midnight day : ℝ) -
      if coreLeap leap = .positive then 1 else 0) t.val = _
  rw [oneEvent_midnight, linux_edge, ← sign_eq, ← adjustment_eq_step, linuxRealtime]
  rw [unshifted_reading]

theorem linux_configured_tai (leap : Leap) (offset day : Int) (domain : Set ℝ) (t : domain) :
    (linuxOn (oneEvent leap offset day) domain).forward t +
      ((offset : ℝ) + linuxLeapAdjustment leap (t.val - physicalNoon offset day)) = t.val := by
  rw [linux_forward]
  change linuxClockTai leap (nominalNoon day) offset (t.val - physicalNoon offset day) = t.val
  rw [linux_tai_eq]
  unfold physicalNoon
  ring

theorem linux_positive_fiber (offset day : Int) {domain : Set ℝ} {t f : ℝ}
    (hf : f ∈ Set.Ico (0 : ℝ) 1) :
    t ∈ (linuxOn (oneEvent .insert offset day) domain).fiber (nominalNoon day + 43199 + f) ↔
      t ∈ domain ∧ (t = physicalNoon offset day + 43199 + f ∨
        t = physicalNoon offset day + 43200 + f) := by
  unfold Convention.fiber
  change (∃ ht : t ∈ domain,
    (linuxOn (oneEvent .insert offset day) domain).forward ⟨t, ht⟩ =
      nominalNoon day + 43199 + f) ↔ _
  constructor
  · rintro ⟨ht, hr⟩
    have hread := (linux_forward .insert offset day domain ⟨t, ht⟩).symm.trans hr
    norm_num [linuxRealtime, linuxLeapAdjustment, Leap.linuxStep, Leap.sign] at hread
    refine ⟨ht, ?_⟩
    split_ifs at hread
    · right
      linarith
    · left
      linarith
  · rintro ⟨ht, h | h⟩
    all_goals
      refine ⟨ht, (linux_forward .insert offset day domain ⟨t, ht⟩).trans ?_⟩
      norm_num [linuxRealtime, linuxLeapAdjustment, Leap.linuxStep, Leap.sign]
      split_ifs <;> linarith [hf.1, hf.2]

theorem sharp_linux_insert_delta (offset day : Int) (domain : Set ℝ) (t : domain) :
    let s := oneEvent .insert offset day
    let m : ℝ := s.midnight day
    (s.sharpOn domain).forward t - (linuxOn s domain).forward t =
      if m - 1 ≤ t.val ∧ t.val < m then 1 else 0 := by
  dsimp only [Schedule.sharpOn, linuxOn]
  simp only [oneEvent, Finset.sum_singleton, coreLeap, true_and, sub_sub_cancel]
  split_ifs with h
  · exact (ite_eq_left h).symm
  · exact (ite_eq_right h).symm

theorem sharp_linux_insert_disagrees (offset day : Int) (domain : Set ℝ) (t : domain) :
    let s := oneEvent .insert offset day
    (s.sharpOn domain).forward t ≠ (linuxOn s domain).forward t ↔
      t.val ∈ insertedSecond offset day := by
  dsimp only
  rw [← sub_ne_zero, sharp_linux_insert_delta]
  let m : ℝ := (oneEvent .insert offset day).midnight day
  change ((if m - 1 ≤ t.val ∧ t.val < m then (1 : ℝ) else 0) ≠ 0) ↔
    (m - 1 ≤ t.val ∧ t.val < m)
  split_ifs with h
  · exact iff_of_true (by norm_num) h
  · exact iff_of_false (fun hzero => hzero rfl) h

theorem sharp_linux_delete_forward (offset day : Int) (domain : Set ℝ) (t : domain) :
    let s := oneEvent .delete offset day
    (s.sharpOn domain).forward t = (linuxOn s domain).forward t := by
  simp [Schedule.sharpOn, linuxOn, oneEvent, coreLeap]

theorem sharp_linux_insert_worstError (offset day : Int) (domain : Set ℝ) :
    let s := oneEvent .insert offset day
    let error := (s.sharpOn domain).worstError (linuxOn s domain)
    (error = 1 ↔ (domain ∩ insertedSecond offset day).Nonempty) ∧
    (error = 0 ↔ ¬ (domain ∩ insertedSecond offset day).Nonempty) := by
  let s := oneEvent .insert offset day
  let a := s.sharpOn domain
  let b := linuxOn s domain
  let m : ℝ := s.midnight day
  change (a.worstError b = 1 ↔ _) ∧ (a.worstError b = 0 ↔ _)
  have delta (t : ℝ) (ha : t ∈ a.domain) (hb : t ∈ b.domain) :
      a.forward ⟨t, ha⟩ - b.forward ⟨t, hb⟩ =
        if m - 1 ≤ t ∧ t < m then 1 else 0 :=
    sharp_linux_insert_delta offset day domain ⟨t, ha⟩
  by_cases h : (domain ∩ insertedSecond offset day).Nonempty
  · obtain ⟨t, ht, hi⟩ := h
    have hi' : m - 1 ≤ t ∧ t < m := hi
    have hmax : a.worstError b = 1 := by
      apply le_antisymm
      · apply (a.worstError_le_iff b 1).2
        intro x ha hb
        rw [delta x ha hb]
        split_ifs <;> norm_num
      · have hsample := (a.worstError_le_iff b (a.worstError b)).1 le_rfl t ht ht
        rw [delta t ht ht, ite_eq_left hi'] at hsample
        simpa using hsample
    have hinter : (domain ∩ insertedSecond offset day).Nonempty := ⟨t, ht, hi⟩
    simp [hmax, hinter]
  · have hzero : a.worstError b = 0 := by
      apply le_antisymm _ bot_le
      apply (a.worstError_le_iff b 0).2
      intro t ha hb
      have hout : ¬ (m - 1 ≤ t ∧ t < m) := fun hi => h ⟨t, ha, hi⟩
      rw [delta t ha hb, ite_eq_right hout]
      norm_num
    simp [hzero, h]

theorem sharp_linux_insert_worstError_univ (offset day : Int) :
    let s := oneEvent .insert offset day
    (s.sharpOn Set.univ).worstError (linuxOn s Set.univ) = 1 := by
  apply (sharp_linux_insert_worstError offset day Set.univ).1.2
  let m : ℝ := (oneEvent .insert offset day).midnight day
  exact ⟨m - 1, Set.mem_univ _, le_rfl, by linarith⟩

theorem sharp_linux_delete_worstError (offset day : Int) (domain : Set ℝ) :
    let s := oneEvent .delete offset day
    (s.sharpOn domain).worstError (linuxOn s domain) = 0 := by
  dsimp only
  apply le_antisymm _ bot_le
  apply (Convention.worstError_le_iff _ _ 0).2
  intro t ha hb
  have he :
      ((oneEvent .delete offset day).sharpOn domain).forward ⟨t, ha⟩ =
        (linuxOn (oneEvent .delete offset day) domain).forward ⟨t, hb⟩ :=
    sharp_linux_delete_forward offset day domain ⟨t, ha⟩
  rw [he, sub_self, abs_zero, ENNReal.ofReal_zero]

/-- Transfer a real supremum to the core's supported discrepancy. The common
support contains the transition window, and the readings agree outside it. -/
private theorem worstError_on_window {a b : Convention} {f g : ℝ → ℝ} {left width r : ℝ}
    (ha : ∀ t : a.domain, a.forward t = f (t.val - left))
    (hb : ∀ t : b.domain, b.forward t = g (t.val - left))
    (hdom : Set.Icc left (left + width) ⊆ a.domain ∩ b.domain)
    (hoff : ∀ x, x < 0 ∨ width < x → f x = g x)
    (hbound : IsLUB (Set.range fun x => |f x - g x|) r) :
    a.worstError b = ENNReal.ofReal r := by
  have hu : a.worstError b ≤ ENNReal.ofReal r :=
    (a.worstError_le_iff b _).2 fun t hat hbt => by
      rw [ha, hb]
      exact ENNReal.ofReal_le_ofReal (hbound.1 ⟨t - left, rfl⟩)
  have hfinite : a.worstError b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  have hl : r ≤ (a.worstError b).toReal := by
    apply hbound.2
    rintro _ ⟨x, rfl⟩
    change |f x - g x| ≤ _
    by_cases hx : x ∈ Set.Icc (0 : ℝ) width
    · have ht : left + x ∈ Set.Icc left (left + width) :=
        ⟨le_add_of_nonneg_right hx.1, by linarith [hx.2]⟩
      have hd := hdom ht
      have hsample := (a.worstError_le_iff b _).1 le_rfl (left + x) hd.1 hd.2
      rw [ha, hb, show left + x - left = x by ring] at hsample
      exact (ENNReal.ofReal_le_iff_le_toReal hfinite).1 hsample
    · have hout : x < 0 ∨ width < x := by
        by_cases h0 : 0 ≤ x
        · exact Or.inr (lt_of_not_ge fun hwidth => hx ⟨h0, hwidth⟩)
        · exact Or.inl (lt_of_not_ge h0)
      rw [hoff x hout, sub_self, abs_zero]
      exact ENNReal.toReal_nonneg
  exact le_antisymm hu ((ENNReal.ofReal_le_ofReal hl).trans_eq (ENNReal.ofReal_toReal hfinite))

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
      (javaLinuxBound leap) := by
  dsimp only
  let n := nominalNoon day
  have hgl : IsLUB (Set.range fun x => |googleSmear leap n x - linuxRealtime leap n x|)
      (googleLinuxBound leap) := by
    cases leap
    · exact (google_linux_insert n).isLUB
    · exact (google_linux_delete n).isLUB
  have hgj : IsLUB (Set.range fun x => |googleSmear leap n x - javaUtcSls leap n x|)
      (googleJavaBound leap) := by
    cases leap
    · exact (google_java_insert n).isLUB
    · exact (google_java_delete n).isLUB
  have hjl : IsLUB (Set.range fun x => |javaUtcSls leap n x - linuxRealtime leap n x|)
      (javaLinuxBound leap) := by
    cases leap
    · exact (java_linux_insert n).1
    · exact (java_linux_delete n).1
  have hout (x : ℝ) (hx : x < 0 ∨ leap.googleEnd < x) :
      linuxRealtime leap n x = googleSmear leap n x ∧
      googleSmear leap n x = javaUtcSls leap n x := by
    rcases hx with hx | hx
    · obtain ⟨hl, hg, hj⟩ := before_noon leap n x hx.le
      exact ⟨hl.trans hg.symm, hg.trans hj.symm⟩
    · obtain ⟨hl, hg, hj⟩ := after_noon leap n x hx.le
      exact ⟨hl.trans hg.symm, hg.trans hj.symm⟩
  have hs : Set.Icc (physicalNoon offset day) (physicalNoon offset day + leap.googleEnd) ⊆
      domain ∩ domain := fun _ hx => ⟨hdom hx, hdom hx⟩
  exact ⟨
    worstError_on_window (google_forward leap offset day domain)
      (linux_forward leap offset day domain) hs (fun x hx => (hout x hx).1.symm) hgl,
    worstError_on_window (google_forward leap offset day domain)
      (java_forward leap offset day domain) hs (fun x hx => (hout x hx).2) hgj,
    worstError_on_window (java_forward leap offset day domain)
      (linux_forward leap offset day domain) hs
      (fun x hx => (hout x hx).2.symm.trans (hout x hx).1.symm) hjl⟩

end Silmaril.Proofs.Numeric.UnixProfiles.Integration
