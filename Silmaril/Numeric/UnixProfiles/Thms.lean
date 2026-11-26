module

public import Silmaril.Numeric.UnixProfiles.Defs
public import Mathlib.Order.Bounds.Basic
import Silmaril.Proofs.Numeric.UnixProfiles.Comparison

/-! The one-event envelope and exact pairwise error bounds, in nominal seconds. -/

public section

namespace Silmaril.Numeric.UnixProfiles

/-- All three readings agree through the starting noon. -/
theorem before_noon (leap : Leap) (noon x : ℝ) (hx : x ≤ 0) :
    linuxRealtime leap noon x = noon + x ∧
    googleSmear leap noon x = noon + x ∧
    javaUtcSls leap noon x = noon + x :=
  Proofs.Numeric.UnixProfiles.before_noon leap noon x hx

/-- All three readings agree from the following noon onward. -/
theorem after_noon (leap : Leap) (noon x : ℝ) (hx : leap.googleEnd ≤ x) :
    linuxRealtime leap noon x = noon + x - leap.sign ∧
    googleSmear leap noon x = noon + x - leap.sign ∧
    javaUtcSls leap noon x = noon + x - leap.sign :=
  Proofs.Numeric.UnixProfiles.after_noon leap noon x hx

/-- The realtime jump cancels the configured TAI offset change at the
same instant. Equality to ideal TAI requires the pre-leap offset to be correct. -/
theorem linux_tai_eq (leap : Leap) (noon offset x : ℝ) :
    linuxClockTai leap noon offset x = noon + offset + x :=
  Proofs.Numeric.UnixProfiles.linux_tai_eq leap noon offset x

/-- The signed Google–Linux error interval, multiplied by the leap sign
to orient both cases alike. Its width is one nominal second. -/
theorem google_linux_signed_envelope (leap : Leap) (noon x : ℝ) :
    -(leap.linuxStep / leap.googleEnd) <
      leap.sign * (googleSmear leap noon x - linuxRealtime leap noon x) ∧
    leap.sign * (googleSmear leap noon x - linuxRealtime leap noon x) ≤
      (leap.googleEnd - leap.linuxStep) / leap.googleEnd :=
  Proofs.Numeric.UnixProfiles.google_linux_signed_envelope leap noon x

/-- Centering the signed error interval gives a half-second upper bound. -/
theorem google_linux_rebiased_le (leap : Leap) (noon x : ℝ) :
    |googleSmear leap noon x - linuxRealtime leap noon x - leap.sign / (2 * leap.googleEnd)| ≤
      1 / 2 :=
  Proofs.Numeric.UnixProfiles.google_linux_rebiased_le leap noon x

/-- The positive Google–Linux bound is attained at the Linux adjustment. -/
theorem google_linux_insert (noon : ℝ) :
    IsGreatest (Set.range fun x => |googleSmear .insert noon x - linuxRealtime .insert noon x|)
      (43201 / 86401) :=
  Proofs.Numeric.UnixProfiles.google_linux_insert noon

/-- The negative Google–Linux bound is attained at the Linux adjustment. -/
theorem google_linux_delete (noon : ℝ) :
    IsGreatest (Set.range fun x => |googleSmear .delete noon x - linuxRealtime .delete noon x|)
      (43200 / 86399) :=
  Proofs.Numeric.UnixProfiles.google_linux_delete noon

/-- The positive Google–Java bound is attained at UTC midnight. -/
theorem google_java_insert (noon : ℝ) :
    IsGreatest (Set.range fun x => |googleSmear .insert noon x - javaUtcSls .insert noon x|)
      (43200 / 86401) :=
  Proofs.Numeric.UnixProfiles.google_java_insert noon

/-- The negative Google–Java bound is attained at UTC midnight. -/
theorem google_java_delete (noon : ℝ) :
    IsGreatest (Set.range fun x => |googleSmear .delete noon x - javaUtcSls .delete noon x|)
      (43200 / 86399) :=
  Proofs.Numeric.UnixProfiles.google_java_delete noon

/-- The positive Java–Linux supremum is approached from before the Linux
adjustment. Every reading pair lies strictly below it. -/
theorem java_linux_insert (noon : ℝ) :
    IsLUB (Set.range fun x => |javaUtcSls .insert noon x - linuxRealtime .insert noon x|)
      (999 / 1000) ∧
    ∀ x, |javaUtcSls .insert noon x - linuxRealtime .insert noon x| < 999 / 1000 :=
  Proofs.Numeric.UnixProfiles.java_linux_insert noon

/-- The negative Java–Linux supremum is approached from before the Linux
adjustment. Every reading pair lies strictly below it. -/
theorem java_linux_delete (noon : ℝ) :
    IsLUB (Set.range fun x => |javaUtcSls .delete noon x - linuxRealtime .delete noon x|) 1 ∧
    ∀ x, |javaUtcSls .delete noon x - linuxRealtime .delete noon x| < 1 :=
  Proofs.Numeric.UnixProfiles.java_linux_delete noon

end Silmaril.Numeric.UnixProfiles
