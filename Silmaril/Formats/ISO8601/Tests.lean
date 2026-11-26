module

import Silmaril.Formats.ISO8601.Thms
meta import Silmaril.Formats.ISO8601.Defs

/-! Regression vectors and small kernel reductions for the calendar text profile. -/

open Silmaril.Formats.ISO8601

private def utcNanos (input : String) : Except Error Int :=
  (parse input).map (fun value => value.utcTicks.ticks)

-- RFC 3339 §5.8. The leap-second spellings are negative controls for this profile.
#guard parseInt64 "1985-04-12T23:20:50.52Z" .millisecond = .ok 482196050520
#guard utcNanos "1996-12-19T16:39:57-08:00" = .ok 851042397000000000
#guard utcNanos "1996-12-20T00:39:57Z" = .ok 851042397000000000
#guard parse "1990-12-31T23:59:60Z" = .error .invalidTime
#guard parse "1990-12-31T15:59:60-08:00" = .error .invalidTime
#guard utcNanos "1937-01-01T12:00:27.87+00:20" = .ok (-1041337172130000000)

-- UTC-second vectors transcribed from the pinned Arrow fixture, batch 0, f11, rows 0 and 2.
#guard parseInt64 "0001-01-01T00:00:00Z" .second = .ok (-62135596800)
#guard parseInt64 "7604-03-19T00:16:49Z" .second = .ok 177798586609

-- An explicit local reading and a normalized instant can lie on different days.
#guard (parse "1970-01-01T00:00:00.5+00:01").map (fun value => value.reading.localTicks.ticks) =
  .ok 500000000
#guard utcNanos "1970-01-01T00:00:00.5+00:01" = .ok (-59500000000)
#guard utcNanos "1969-12-31T23:59:59.999999999Z" = .ok (-1)
#guard parseInt64 "1969-12-31T23:59:59.999Z" .millisecond = .ok (-1)
#guard parseInt64 "1969-12-31T23:59:59.999999999Z" .microsecond = .error (.conversion .precisionLoss)
#guard parseInt64 "1970-01-01T00:00:00.000000001Z" .second = .error (.conversion .precisionLoss)
#guard utcNanos "1969-12-31T23:59:59-00:01" = .ok 59000000000
#guard utcNanos "1970-01-01T23:59:00+23:59" = .ok 0
#guard utcNanos "1969-12-31T00:01:00-23:59" = .ok 0
#guard (parse "1970-01-01T00:00:00+00:00").map (fun value => value.offset) =
  .ok (.ahead ⟨0, by decide⟩)
#guard utcNanos "1970-01-01T00:00:00+00:00" = .ok 0

-- Calendar validation and normalization across leap day and the textual year limits.
#guard utcNanos "2000-03-01T00:00:00+00:01" = .ok 951868740000000000
#guard utcNanos "2024-02-29T23:59:59-00:01" = .ok 1709251259000000000
#guard parse "1900-02-29T00:00:00Z" = .error .invalidDate
#guard parse "2023-02-29T00:00:00Z" = .error .invalidDate
#guard parse "2024-04-31T00:00:00Z" = .error .invalidDate
#guard parse "2024-00-01T00:00:00Z" = .error .invalidDate
#guard (parse "0000-02-29T00:00:00Z").map (fun value => value.reading.date) = .ok ⟨0, 2, 29⟩
#guard parseInt64 "0000-01-01T00:00:00+00:01" .second = .ok (-62167219260)
#guard parseInt64 "9999-12-31T23:59:59-00:01" .second = .ok 253402300859

-- Both signed endpoints, offset normalization before range checking, and adjacent overflow.
#guard parseInt64 "1677-09-21T00:12:43.145224192Z" .nanosecond = .ok Int64.minValue
#guard parseInt64 "2262-04-11T23:47:16.854775807Z" .nanosecond = .ok Int64.maxValue
#guard parseInt64 "2262-04-12T00:47:16.854775807+01:00" .nanosecond = .ok Int64.maxValue
#guard parseInt64 "1677-09-21T00:12:43.145224191Z" .nanosecond = .error (.conversion .outOfRange)
#guard parseInt64 "2262-04-11T23:47:16.854775808Z" .nanosecond = .error (.conversion .outOfRange)

-- Precision and exact consumption are part of the text profile.
#guard parse "2024-01-01T00:00:00.1234567890Z" = .error .fractionPrecision
#guard parse "2024-01-01T00:00:00.Z" = .error .syntax
#guard parse "2024-01-01T00:00:00,5Z" = .error .syntax
#guard parse "2024-01-01T24:00:00Z" = .error .invalidTime
#guard parse "2024-01-01T00:60:00Z" = .error .invalidTime
#guard parse "2024-01-01T00:00:00-00:00" = .error .invalidOffset
#guard parse "2024-01-01T00:00:00+24:00" = .error .invalidOffset
#guard parse "2024-01-01T00:00:00-00:60" = .error .invalidOffset
#guard parse "2024-01-01T00:00:00" = .error .syntax
#guard parse "2024-01-01t00:00:00Z" = .error .syntax
#guard parse "2024-01-01T00:00:00z" = .error .syntax
#guard parse "２０２４-01-01T00:00:00Z" = .error .syntax
#guard parse "2024-01-01T00:00:00+0100" = .error .syntax
#guard parse "2024-01-01T00:00:00+01:00:00" = .error .syntax
#guard parse "2024-01-01T00:00:00Z[Europe/London]" = .error .syntax
#guard parse "2024-01-01T00:00:00Z " = .error .syntax
#guard parse "20240101T000000Z" = .error .syntax
#guard parse "+02024-01-01T00:00:00Z" = .error .syntax
#guard parse "2024-001T00:00:00Z" = .error .syntax
#guard parse "2024-W01-1T00:00:00Z" = .error .syntax
#guard parse "P1D" = .error .syntax

example : parse "2024-01-01T00:00:00.1234567890Z" = .error .fractionPrecision := rfl
example : parse "2024-01-01T00:00:00-0000" = .error .syntax := rfl
