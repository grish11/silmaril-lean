module

import Silmaril.Numeric.UnixProfiles.Thms
import Mathlib.Tactic.NormNum

/-! Exact real-coordinate fixtures. See `docs/projects/unix-profiles.md`
for the source dates and the synthetic deletion convention. -/

open Silmaril.Numeric.UnixProfiles

-- IERS Bulletin C 52. The two fractional labels share a realtime reading.
example :
    linuxRealtime .insert 1483185600 (43199 + 1 / 4) = 1483228799 + 1 / 4 ∧
    linuxRealtime .insert 1483185600 (43200 + 1 / 4) = 1483228799 + 1 / 4 ∧
    linuxRealtime .insert 1483185600 43200 = 1483228799 ∧
    linuxRealtime .insert 1483185600 43201 = 1483228800 := by
  norm_num [linuxRealtime, linuxLeapAdjustment, Leap.linuxStep, Leap.sign]

example :
    linuxClockTai .insert 1483185600 36 (43199 + 1 / 4) = 1483228835 + 1 / 4 ∧
    linuxClockTai .insert 1483185600 36 (43200 + 1 / 4) = 1483228836 + 1 / 4 := by
  norm_num [linux_tai_eq]

-- A hypothetical deletion jumps over the last nominal second before midnight.
example :
    linuxRealtime .delete 0 (43199 - 1 / 4) = 43199 - 1 / 4 ∧
    linuxRealtime .delete 0 43199 = 43200 ∧
    linuxClockTai .delete 0 37 43199 = 43236 := by
  norm_num [linuxRealtime, linuxLeapAdjustment, Leap.linuxStep, Leap.sign, linux_tai_eq]

-- Google's hypothetical end-of-2022 example. The physical midpoint is
-- exactly the indicated midnight, halfway through the inserted second.
example :
    googleSmear .insert 1672488000 0 = 1672488000 ∧
    googleSmear .insert 1672488000 (43200 + 1 / 2) = 1672531200 ∧
    googleSmear .insert 1672488000 86401 = 1672574400 ∧
    googleSmear .delete 0 (43199 + 1 / 2) = 43200 ∧
    googleSmear .delete 0 86399 = 86400 := by
  norm_num [googleSmear, Leap.googleEnd, Leap.sign, min_def, max_def]

-- Both Java ramp starts, first physical seconds on the ramps, and midnight joins.
example :
    javaUtcSls .insert 0 42201 = 42201 ∧
    javaUtcSls .insert 0 42202 = 42201 + 999 / 1000 ∧
    javaUtcSls .insert 0 43201 = 43200 ∧
    javaUtcSls .delete 0 42199 = 42199 ∧
    javaUtcSls .delete 0 42200 = 42199 + 1001 / 1000 ∧
    javaUtcSls .delete 0 43199 = 43200 := by
  norm_num [javaUtcSls, Leap.javaStart, Leap.midnight, Leap.sign, min_def, max_def]

-- Java–Linux errors just before and at each step. The adjustment instant
-- itself uses the post-step branch, which is essential for nonattainment.
example :
    |javaUtcSls .insert 0 (43200 - 1 / 2) - linuxRealtime .insert 0 (43200 - 1 / 2)| =
      1997 / 2000 ∧
    |javaUtcSls .insert 0 43200 - linuxRealtime .insert 0 43200| = 1 / 1000 ∧
    |javaUtcSls .delete 0 (43199 - 1 / 2) - linuxRealtime .delete 0 (43199 - 1 / 2)| =
      1999 / 2000 ∧
    |javaUtcSls .delete 0 43199 - linuxRealtime .delete 0 43199| = 0 := by
  norm_num [javaUtcSls, linuxRealtime, linuxLeapAdjustment, Leap.javaStart, Leap.midnight,
    Leap.linuxStep, Leap.sign, min_def, max_def]
