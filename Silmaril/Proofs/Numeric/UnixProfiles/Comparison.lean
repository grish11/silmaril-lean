module

public import Silmaril.Numeric.UnixProfiles.Defs
public import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.Proofs.Numeric.UnixProfiles

open Silmaril.Numeric.UnixProfiles

theorem before_noon (leap : Leap) (noon x : ℝ) (hx : x ≤ 0) :
    linuxRealtime leap noon x = noon + x ∧
    googleSmear leap noon x = noon + x ∧
    javaUtcSls leap noon x = noon + x := by
  have hs : ¬ leap.linuxStep ≤ x := by
    cases leap <;> norm_num [Leap.linuxStep, Leap.sign] <;> linarith
  have hg : x / leap.googleEnd ≤ 0 := by
    cases leap <;> norm_num [Leap.googleEnd, Leap.sign] <;> linarith
  have hj : (x - leap.javaStart) / 1000 ≤ 0 := by
    cases leap <;> norm_num [Leap.javaStart, Leap.midnight, Leap.sign] <;> linarith
  simp [linuxRealtime, linuxLeapAdjustment, googleSmear, javaUtcSls, hs,
    max_eq_left hg, max_eq_left hj]

theorem after_noon (leap : Leap) (noon x : ℝ) (hx : leap.googleEnd ≤ x) :
    linuxRealtime leap noon x = noon + x - leap.sign ∧
    googleSmear leap noon x = noon + x - leap.sign ∧
    javaUtcSls leap noon x = noon + x - leap.sign := by
  have hs : leap.linuxStep ≤ x := by
    cases leap <;> norm_num [Leap.googleEnd, Leap.linuxStep, Leap.sign] at hx ⊢ <;> linarith
  have hg : 1 ≤ x / leap.googleEnd := by
    cases leap <;> norm_num [Leap.googleEnd, Leap.sign] at hx ⊢ <;> linarith
  have hj : 1 ≤ (x - leap.javaStart) / 1000 := by
    cases leap <;>
      norm_num [Leap.googleEnd, Leap.javaStart, Leap.midnight, Leap.sign] at hx ⊢ <;> linarith
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  simp [linuxRealtime, linuxLeapAdjustment, googleSmear, javaUtcSls, hs,
    max_eq_right (h01.trans hg), max_eq_right (h01.trans hj), min_eq_left hg, min_eq_left hj]

theorem linux_tai_eq (leap : Leap) (noon offset x : ℝ) :
    linuxClockTai leap noon offset x = noon + offset + x := by
  unfold linuxClockTai linuxRealtime
  ring

theorem google_linux_signed_envelope (leap : Leap) (noon x : ℝ) :
    -(leap.linuxStep / leap.googleEnd) <
      leap.sign * (googleSmear leap noon x - linuxRealtime leap noon x) ∧
    leap.sign * (googleSmear leap noon x - linuxRealtime leap noon x) ≤
      (leap.googleEnd - leap.linuxStep) / leap.googleEnd := by
  cases leap <;>
    norm_num [googleSmear, linuxRealtime, linuxLeapAdjustment, Leap.googleEnd, Leap.linuxStep,
      Leap.sign, min_def, max_def] <;>
    split_ifs <;> constructor <;> linarith

private theorem googleLinux_le (leap : Leap) (noon x : ℝ) :
    |googleSmear leap noon x - linuxRealtime leap noon x| ≤
      (match leap with | .insert => 43201 / 86401 | .delete => 43200 / 86399) := by
  have h := google_linux_signed_envelope leap noon x
  apply abs_le.mpr
  cases leap <;> norm_num [Leap.sign, Leap.linuxStep, Leap.googleEnd] at h ⊢ <;>
    constructor <;> linarith [h.1, h.2]

theorem google_linux_rebiased_le (leap : Leap) (noon x : ℝ) :
    |googleSmear leap noon x - linuxRealtime leap noon x - leap.sign / (2 * leap.googleEnd)| ≤
      1 / 2 := by
  have h := google_linux_signed_envelope leap noon x
  apply abs_le.mpr
  cases leap <;> norm_num [Leap.sign, Leap.linuxStep, Leap.googleEnd] at h ⊢ <;>
    constructor <;> linarith [h.1, h.2]

private theorem googleJava_le (leap : Leap) (noon x : ℝ) :
    |googleSmear leap noon x - javaUtcSls leap noon x| ≤
      (match leap with | .insert => 43200 / 86401 | .delete => 43200 / 86399) := by
  cases leap <;>
    norm_num [googleSmear, javaUtcSls, Leap.googleEnd, Leap.javaStart, Leap.midnight,
      Leap.sign, min_def, max_def] <;>
    split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

/-- The signed difference at the realtime step supplies an attaining witness. -/
theorem google_linux_insert (noon : ℝ) :
    IsGreatest (Set.range fun x => |googleSmear .insert noon x - linuxRealtime .insert noon x|)
      (43201 / 86401) := by
  refine ⟨⟨43200, ?_⟩, ?_⟩
  · have h :
        googleSmear .insert noon 43200 - linuxRealtime .insert noon 43200 = 43201 / 86401 := by
      norm_num [googleSmear, linuxRealtime, linuxLeapAdjustment, Leap.googleEnd, Leap.linuxStep,
        Leap.sign, min_def, max_def]
    dsimp only
    rw [h, abs_of_nonneg (by norm_num)]
  · rintro _ ⟨x, rfl⟩
    exact googleLinux_le .insert noon x

theorem google_linux_delete (noon : ℝ) :
    IsGreatest (Set.range fun x => |googleSmear .delete noon x - linuxRealtime .delete noon x|)
      (43200 / 86399) := by
  refine ⟨⟨43199, ?_⟩, ?_⟩
  · have h :
        googleSmear .delete noon 43199 - linuxRealtime .delete noon 43199 = -(43200 / 86399) := by
      norm_num [googleSmear, linuxRealtime, linuxLeapAdjustment, Leap.googleEnd, Leap.linuxStep,
        Leap.sign, min_def, max_def]
    dsimp only
    rw [h, abs_neg, abs_of_nonneg (by norm_num)]
  · rintro _ ⟨x, rfl⟩
    exact googleLinux_le .delete noon x

/-- UTC midnight supplies an attaining witness for the two continuous profiles. -/
theorem google_java_insert (noon : ℝ) :
    IsGreatest (Set.range fun x => |googleSmear .insert noon x - javaUtcSls .insert noon x|)
      (43200 / 86401) := by
  refine ⟨⟨43201, ?_⟩, ?_⟩
  · have h :
        googleSmear .insert noon 43201 - javaUtcSls .insert noon 43201 = 43200 / 86401 := by
      norm_num [googleSmear, javaUtcSls, Leap.googleEnd, Leap.javaStart, Leap.midnight,
        Leap.sign, min_def, max_def]
    dsimp only
    rw [h, abs_of_nonneg (by norm_num)]
  · rintro _ ⟨x, rfl⟩
    exact googleJava_le .insert noon x

theorem google_java_delete (noon : ℝ) :
    IsGreatest (Set.range fun x => |googleSmear .delete noon x - javaUtcSls .delete noon x|)
      (43200 / 86399) := by
  refine ⟨⟨43199, ?_⟩, ?_⟩
  · have h :
        googleSmear .delete noon 43199 - javaUtcSls .delete noon 43199 = -(43200 / 86399) := by
      norm_num [googleSmear, javaUtcSls, Leap.googleEnd, Leap.javaStart, Leap.midnight,
        Leap.sign, min_def, max_def]
    dsimp only
    rw [h, abs_neg, abs_of_nonneg (by norm_num)]
  · rintro _ ⟨x, rfl⟩
    exact googleJava_le .delete noon x

private noncomputable def javaLinuxBound : Leap → ℝ
  | .insert => 999 / 1000
  | .delete => 1

private theorem javaLinux_lt (leap : Leap) (noon x : ℝ) :
    |javaUtcSls leap noon x - linuxRealtime leap noon x| < javaLinuxBound leap := by
  cases leap <;>
    norm_num [javaUtcSls, linuxRealtime, linuxLeapAdjustment, Leap.javaStart, Leap.midnight,
      Leap.linuxStep, Leap.sign, javaLinuxBound, min_def, max_def] <;>
    split_ifs <;> apply abs_lt.mpr <;> constructor <;> linarith

/-- Each error strictly below the bound can be realized on the ramp before the step. -/
private theorem javaLinux_before (leap : Leap) (noon y : ℝ)
    (hy0 : 0 ≤ y) (hy : y < javaLinuxBound leap) :
    ∃ x, |javaUtcSls leap noon x - linuxRealtime leap noon x| = y := by
  let x := leap.javaStart + 1000 * y
  have hstep : x < leap.linuxStep := by
    cases leap <;>
      norm_num [x, Leap.javaStart, Leap.midnight, Leap.linuxStep, Leap.sign, javaLinuxBound] at * <;>
      linarith
  have hy1 : y ≤ 1 := by
    cases leap <;> norm_num [javaLinuxBound] at hy <;> linarith
  have hramp : (x - leap.javaStart) / 1000 = y := by dsimp [x]; ring
  refine ⟨x, ?_⟩
  rw [javaUtcSls, linuxRealtime, linuxLeapAdjustment, ite_eq_right (not_le.mpr hstep),
    hramp, max_eq_right hy0, min_eq_right hy1]
  have h : noon + x - leap.sign * y - (noon + x - 0) = -(leap.sign * y) := by ring
  rw [h, abs_neg, abs_mul, abs_of_nonneg hy0]
  cases leap <;> norm_num [Leap.sign]

private theorem javaLinux_isLUB (leap : Leap) (noon : ℝ) :
    IsLUB (Set.range fun x => |javaUtcSls leap noon x - linuxRealtime leap noon x|)
      (javaLinuxBound leap) := by
  constructor
  · rintro _ ⟨x, rfl⟩
    exact (javaLinux_lt leap noon x).le
  · intro candidate hc
    by_contra h
    have hpos : 0 < javaLinuxBound leap := by cases leap <;> norm_num [javaLinuxBound]
    obtain ⟨y, hymax, hy⟩ := exists_between (max_lt (lt_of_not_ge h) hpos)
    have hy0 : 0 ≤ y := (le_max_right candidate 0).trans hymax.le
    obtain ⟨x, hx⟩ := javaLinux_before leap noon y hy0 hy
    exact ((le_max_left candidate 0).trans_lt hymax).not_ge (hc ⟨x, hx⟩)

theorem java_linux_insert (noon : ℝ) :
    IsLUB (Set.range fun x => |javaUtcSls .insert noon x - linuxRealtime .insert noon x|)
      (999 / 1000) ∧
    ∀ x, |javaUtcSls .insert noon x - linuxRealtime .insert noon x| < 999 / 1000 := by
  exact ⟨javaLinux_isLUB .insert noon, javaLinux_lt .insert noon⟩

theorem java_linux_delete (noon : ℝ) :
    IsLUB (Set.range fun x => |javaUtcSls .delete noon x - linuxRealtime .delete noon x|) 1 ∧
    ∀ x, |javaUtcSls .delete noon x - linuxRealtime .delete noon x| < 1 := by
  exact ⟨javaLinux_isLUB .delete noon, javaLinux_lt .delete noon⟩

end Silmaril.Proofs.Numeric.UnixProfiles
