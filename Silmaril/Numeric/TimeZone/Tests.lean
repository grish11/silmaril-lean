module

import Silmaril.Numeric.TimeZone.Thms
-- Expose the standard calendar definitions to kernel reduction in the fixtures.
import all Std.Time.Date.Unit.Year
import all Std.Time.Date.Unit.Month
import all Std.Time.Internal.UnitVal

/-! # Kernel-checked time zone examples

The transition rows are from IANA tzdata 2025b. The project note records
the archive hash, dates, support intervals and reproduction commands.
-/

namespace Silmaril.Numeric.TimeZone

private def unix (seconds : Int) : UnixTime :=
  (⟨seconds⟩ : Timestamp.Ticks .utcInstant .second).denote

private def civil (year : Int) (month day : Nat) (secondsOfDay : Int)
    (extraNanoseconds : Int := 0) : CivilReading :=
  ⟨⟨year, month, day⟩, secondsOfDay * 1000000000 + extraNanoseconds⟩

private def newYorkSchedule : Schedule :=
  ⟨unix 1735689600, unix 1767225600, Offset.ofSeconds (-18000),
    [⟨unix 1741503600, Offset.ofSeconds (-14400)⟩, ⟨unix 1762063200, Offset.ofSeconds (-18000)⟩],
    by decide +kernel⟩

private def newYork : Rules := .scheduled newYorkSchedule

-- March 9, 2025, 07:00:00 nominal UTC. The wall clock skips [02:00, 03:00).
example : CivilReading.ofWall ⟨(unix 1741503600).ticks⟩ = civil 2025 3 9 (7 * 3600) := by decide +kernel
example : newYork.toCivil? ⟨(unix 1741503600).ticks - 1⟩ =
    some (civil 2025 3 9 (2 * 3600) (-1)) := by decide +kernel
example : newYork.toCivil? (unix 1741503600) = some (civil 2025 3 9 (3 * 3600)) := by decide +kernel
example : newYork.civilCandidates? (civil 2025 3 9 (2 * 3600) (-1)) =
    some [⟨(unix 1741503600).ticks - 1⟩] := by decide +kernel
example : newYork.civilCandidates? (civil 2025 3 9 (2 * 3600)) = some [] := by decide +kernel
example : newYork.civilCandidates? (civil 2025 3 9 (3 * 3600) (-1)) = some [] := by decide +kernel
example : newYork.civilCandidates? (civil 2025 3 9 (3 * 3600)) = some [unix 1741503600] := by decide +kernel

-- November 2, 2025, 06:00:00 nominal UTC. The wall clock repeats [01:00, 02:00).
example : CivilReading.ofWall ⟨(unix 1762063200).ticks⟩ = civil 2025 11 2 (6 * 3600) := by decide +kernel
example : newYork.toCivil? ⟨(unix 1762063200).ticks - 1⟩ =
    some (civil 2025 11 2 (2 * 3600) (-1)) := by decide +kernel
example : newYork.toCivil? (unix 1762063200) = some (civil 2025 11 2 3600) := by decide +kernel
example : newYork.civilCandidates? (civil 2025 11 2 3600 (-1)) =
    some [⟨(unix 1762059600).ticks - 1⟩] := by decide +kernel
example : newYork.civilCandidates? (civil 2025 11 2 3600) =
    some [unix 1762059600, unix 1762063200] := by decide +kernel
example : newYork.civilCandidates? (civil 2025 11 2 (2 * 3600) (-1)) =
    some [⟨(unix 1762063200).ticks - 1⟩, ⟨(unix 1762066800).ticks - 1⟩] := by decide +kernel
example : newYork.civilCandidates? (civil 2025 11 2 (2 * 3600)) =
    some [unix 1762066800] := by decide +kernel

private def foldStart : WallTime := ⟨(unix 1762045200).ticks⟩
example : (civil 2025 11 2 3600).toWall? = some foldStart := by decide +kernel
example : newYork.resolve? foldStart .unique = none := by decide +kernel
example : newYork.resolve? foldStart .earliest = some (unix 1762059600) := by decide +kernel
example : newYork.resolve? foldStart .latest = some (unix 1762063200) := by decide +kernel

example : newYork.offsetAt? ⟨(unix 1735689600).ticks - 1⟩ = none := by decide +kernel
example : newYork.offsetAt? (unix 1735689600) = some (Offset.ofSeconds (-18000)) := by decide +kernel
example : newYork.offsetAt? ⟨(unix 1767225600).ticks - 1⟩ = some (Offset.ofSeconds (-18000)) :=
  by decide +kernel
example : newYork.offsetAt? (unix 1767225600) = none := by decide +kernel
example : newYork.civilCandidates? (civil 2024 12 30 0) = some [] := by decide +kernel

-- Kathmandu advances by 15 minutes, from +05:30 to +05:45.
private def kathmandu : Rules :=
  .scheduled ⟨unix 504835200, unix 505008000, Offset.ofSeconds 19800,
    [⟨unix 504901800, Offset.ofSeconds 20700⟩], by decide +kernel⟩

example : CivilReading.ofWall ⟨(unix 504901800).ticks⟩ =
    civil 1985 12 31 (18 * 3600 + 30 * 60) := by decide +kernel
example : kathmandu.toCivil? ⟨(unix 504901800).ticks - 1⟩ =
    some (civil 1985 12 31 86400 (-1)) := by decide +kernel
example : kathmandu.toCivil? (unix 504901800) = some (civil 1986 1 1 (15 * 60)) := by decide +kernel
example : kathmandu.civilCandidates? (civil 1985 12 31 86400 (-1)) =
    some [⟨(unix 504901800).ticks - 1⟩] := by decide +kernel
example : kathmandu.civilCandidates? (civil 1986 1 1 0) = some [] := by decide +kernel
example : kathmandu.civilCandidates? (civil 1986 1 1 (15 * 60) (-1)) = some [] := by decide +kernel
example : kathmandu.civilCandidates? (civil 1986 1 1 (15 * 60)) =
    some [unix 504901800] := by decide +kernel

-- Exact fixed-offset conversion with a pre-epoch input and a fractional second.
private def plusFiveFortyFive : Rules := .fixed (Offset.ofSeconds 20700)

example : plusFiveFortyFive.toCivil? ⟨-1⟩ = some (civil 1970 1 1 20700 (-1)) := by decide +kernel
example : plusFiveFortyFive.civilCandidates? (civil 1970 1 1 20700 (-1)) = some [⟨-1⟩] :=
  by decide +kernel
example : CivilReading.ofWall ⟨-1⟩ = civil 1969 12 31 86400 (-1) := by decide +kernel
example : plusFiveFortyFive.civilCandidates? (civil 2025 2 29 0) = none := by decide +kernel
example : plusFiveFortyFive.civilCandidates? (civil 2025 1 1 0 (-1)) = none := by decide +kernel
example : plusFiveFortyFive.civilCandidates? (civil 2025 1 1 86400) = none := by decide +kernel

-- Synthetic subsecond cuts and offsets. General schedules can have more than two preimages.
private def overlapping : Rules :=
  .scheduled ⟨⟨0⟩, ⟨30⟩, ⟨20⟩, [⟨⟨10⟩, ⟨10⟩⟩, ⟨⟨20⟩, ⟨0⟩⟩], by decide +kernel⟩

example : overlapping.candidates ⟨20⟩ = [⟨0⟩, ⟨10⟩, ⟨20⟩] := by decide +kernel
example : overlapping.candidates ⟨30⟩ = [] := by decide +kernel
example : overlapping.resolve? ⟨20⟩ .unique = none := by decide +kernel
example : overlapping.resolve? ⟨30⟩ .earliest = none := by decide +kernel
example : overlapping.resolve? ⟨30⟩ .latest = none := by decide +kernel

-- The first jump skips wall 15 for its adjacent pair. The third segment covers it.
private def filledGap : Rules :=
  .scheduled ⟨⟨0⟩, ⟨30⟩, ⟨0⟩, [⟨⟨10⟩, ⟨10⟩⟩, ⟨⟨20⟩, ⟨-5⟩⟩], by decide +kernel⟩

example : filledGap.candidates ⟨15⟩ = [⟨20⟩] := by decide +kernel
example : filledGap.resolve? ⟨15⟩ .unique = some ⟨20⟩ := by decide +kernel

-- A large backward jump can leave the two translated short intervals disjoint.
private def shortSegments : Rules :=
  .scheduled ⟨⟨0⟩, ⟨10⟩, ⟨10⟩, [⟨⟨5⟩, ⟨0⟩⟩], by decide +kernel⟩

example : shortSegments.candidates ⟨7⟩ = [⟨7⟩] := by decide +kernel
example : shortSegments.candidates ⟨10⟩ = [⟨0⟩] := by decide +kernel

example : (Schedule.ofTransitions? ⟨0⟩ ⟨0⟩ ⟨0⟩ []).isNone = true := by decide +kernel
example : (Schedule.ofTransitions? ⟨0⟩ ⟨10⟩ ⟨0⟩ [⟨⟨0⟩, ⟨1⟩⟩]).isNone = true := by decide +kernel
example : (Schedule.ofTransitions? ⟨0⟩ ⟨10⟩ ⟨0⟩ [⟨⟨10⟩, ⟨1⟩⟩]).isNone = true := by decide +kernel
example : (Schedule.ofTransitions? ⟨0⟩ ⟨10⟩ ⟨0⟩
    [⟨⟨5⟩, ⟨1⟩⟩, ⟨⟨5⟩, ⟨2⟩⟩]).isNone = true := by decide +kernel
example : (Schedule.ofTransitions? ⟨0⟩ ⟨10⟩ ⟨0⟩
    [⟨⟨6⟩, ⟨1⟩⟩, ⟨⟨5⟩, ⟨2⟩⟩]).isNone = true := by decide +kernel
example : (Schedule.ofTransitions? ⟨0⟩ ⟨10⟩ ⟨0⟩
    [⟨⟨5⟩, ⟨1⟩⟩, ⟨⟨6⟩, ⟨2⟩⟩]).isSome = true := by decide +kernel

end Silmaril.Numeric.TimeZone
