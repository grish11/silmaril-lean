module

public import Mathlib.Basic.Real.Basic

/-! One UTC leap event on a common physical axis. The input `x` is SI seconds
from UTC noon before the transition. Outputs are nominal seconds with the
same epoch and agree at the input noon `x = 0`. -/

@[expose] public section

namespace Silmaril.Numeric.UnixProfiles

/-- The sign of a whole leap second. -/
inductive Leap where
  | insert
  | delete

/-- The change in TAI minus UTC introduced by the leap. -/
noncomputable def Leap.sign : Leap → ℝ
  | .insert => 1
  | .delete => -1

/-- Physical seconds from the starting noon to the next UTC midnight. -/
noncomputable def Leap.midnight (leap : Leap) : ℝ :=
  43200 + leap.sign

/-- Physical seconds from the starting noon to Linux's realtime adjustment. -/
noncomputable def Leap.linuxStep (leap : Leap) : ℝ :=
  43200 + min 0 leap.sign

/-- Physical seconds from the starting noon to the next UTC noon. -/
noncomputable def Leap.googleEnd (leap : Leap) : ℝ :=
  86400 + leap.sign

/-- Physical seconds from the starting noon to the Java UTC-SLS ramp start. -/
noncomputable def Leap.javaStart (leap : Leap) : ℝ :=
  leap.midnight - 1000

/-- The signed correction added to Linux's configured TAI offset. At the
adjustment boundary the new offset applies. -/
noncomputable def linuxLeapAdjustment (leap : Leap) (x : ℝ) : ℝ :=
  if leap.linuxStep ≤ x then leap.sign else 0

/-- Idealized Linux v6.12 `CLOCK_REALTIME` with the kernel leap armed. The
parameter `noon` is the nominal Unix reading at the starting UTC noon.
See `second_overflow` in `kernel/time/ntp.c`. -/
noncomputable def linuxRealtime (leap : Leap) (noon x : ℝ) : ℝ :=
  noon + x - linuxLeapAdjustment leap x

/-- Idealized Linux `CLOCK_TAI` on the same state as `linuxRealtime`.
The parameter `offset` is the configured offset before the leap. -/
noncomputable def linuxClockTai (leap : Leap) (noon offset x : ℝ) : ℝ :=
  linuxRealtime leap noon x + (offset + linuxLeapAdjustment leap x)

/-- The linear noon-to-noon smear documented by Google Public NTP. -/
noncomputable def googleSmear (leap : Leap) (noon x : ℝ) : ℝ :=
  noon + x - leap.sign * min 1 (max 0 (x / leap.googleEnd))

/-- The abstract UTC-SLS segment of the Java SE 21 time-scale. The ramp
spans the final 1,000 physical seconds of the UTC leap day. -/
noncomputable def javaUtcSls (leap : Leap) (noon x : ℝ) : ℝ :=
  noon + x - leap.sign * min 1 (max 0 ((x - leap.javaStart) / 1000))

end Silmaril.Numeric.UnixProfiles
