# One-event software clock profiles

`Silmaril.Numeric.UnixProfiles.Thms` compares three ideal readings on the
same physical axis. The inputs are the sign `e` of one whole leap second
(`+1` for insertion or `−1` for deletion), physical SI seconds `x` from UTC noon on the leap day, and that noon's
nominal Unix second count `P`. The following UTC midnight is at
`b = 43200 + e` and the following noon is at `W = 86400 + e`.
On the chosen TAI coordinate, whose zero is 1970-01-01 00:00:00 TAI,
ideal TAI is `P + d + x` when `d` is the TAI−UTC offset at the starting
noon. This alignment uses a covered interval in the whole-leap UTC era.
[ITU-R TF.460-6 (02/2002), Annex 1 B–E and Annex 3](https://www.itu.int/dms_pubrec/itu-r/rec/tf/R-REC-TF.460-6-200202-I!!PDF-E.pdf)

POSIX.1-2024 §4.19 gives a nominal calendar coordinate with 86,400 seconds
per day and leaves the relationship between the running system clock and
actual IERS UTC unspecified. The Linux row models a specific kernel leap
policy. For a valid positive leap label, substituting `tm_sec = 60` in the
POSIX calendar expression produces the following nominal midnight, while
the Linux realtime policy repeats the preceding nominal second.
[POSIX.1-2024, Issue 8, Base Definitions §4.19](https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/V1_chap04.html#tag_04_19)
· [`<time.h>` second field](https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/time.h.html)

## Maps and evidence

Let `clip(z) = min(1, max(0, z))`. Each reading has the form
`P + x − e·h(x)`.

| Map | Progress `h(x)` | Physical transition |
| --- | --- | --- |
| `linuxRealtime` | `1` for `x ≥ 43200 + min(0,e)`, otherwise `0` | Insertion repeats the preceding nominal second from `x = 43200`. Deletion skips the last nominal second at `x = 43199`. |
| `googleSmear` | `clip(x/W)` | The noon-to-noon window lasts 86,401 or 86,399 SI seconds and advances 86,400 indicated seconds. |
| `javaUtcSls` | `clip((x − (b − 1000))/1000)` | The last 1,000 SI seconds of the leap day advance 999 or 1,001 indicated seconds. The UTC starts are 23:43:21 or 23:43:19. |

- **Linux v6.12.** The armed NTP state applies a signed realtime
  correction and makes the opposite change to the configured TAI offset.
  The positive adjustment applies at the start of the repeat interval,
  one SI second before the following labelled midnight. The theorem
  `linux_tai_eq` gives `P + offset + x` for a coherent state in the
  idealized model. Identifying that value with ideal TAI requires the
  correct initial offset and appropriately tracked realtime. Kernel
  arithmetic range, clocksource precision, administrative changes and
  sampling skew between separate reads remain deployment conditions.
  [Linux v6.12 commit `adc218676eef`, `second_overflow`](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/kernel/time/ntp.c#L400-L445)
  · [Leap and offset update](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/kernel/time/timekeeping.c#L2194-L2227)
  · [Shared clock base](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/kernel/time/timekeeping.c#L875-L898)
  · [Offset configuration](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/kernel/time/ntp.c#L743-L752)
- **Google Public NTP.** The explanation and example disambiguate the
  physical and indicated denominators. The negative policy is
  prospective. The example's decimals and the NTP timestamp wire
  precision supply no deployment error bound. The checked text view of
  the document is dated 2023-10-23 and has SHA-256
  `f7d5c05b776fad4d7150a05eaecc1acf260fc783761f01e6758864b4561563a5`.
  [Google Leap Smear, proposed smear and worked example](https://developers.google.com/time/smear#example_of_the_standard_smear)
  · [Text view](https://developers.google.com/time/smear.md.txt)
  · [Companion converter commit `e1e447d`, forward and inverse interpolation](https://github.com/google/unsmear/blob/e1e447d836359e3a0726c19ebe38a661a7295e68/unsmear/leap_table.cc#L204-L230)
  · [RFC 5905 §6, wire timestamps](https://www.rfc-editor.org/rfc/rfc5905.html#section-6)
- **Java SE 21.** The modeled UTC-SLS segment begins at Java's specified
  November 1972 UT1/UTC crossing. The cited Internet-Draft gives the
  physical window and both signed formulas. Java permits system clocks
  without an actual UTC-SLS slew, leap awareness, smoothness, monotonicity
  or subsecond accuracy. The theorem describes the abstract time-scale.
  [Java SE 21 `Instant`, Time-scale](https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/time/Instant.html#time-scale-heading)
  · [`draft-kuhn-leapsecond-00`, January 2006, §§4–5](https://datatracker.ietf.org/doc/html/draft-kuhn-leapsecond-00#section-4)

## Proven bounds and fixtures

`before_noon` and `after_noon` state agreement outside the common window,
including both endpoints. `google_linux_signed_envelope` gives the
sign-oriented error interval `(−s/W, (W−s)/W]`, where
`s = 43200 + min(0,e)`. Its width is one second.
`google_linux_rebiased_le` bounds the absolute difference by one half
second after subtracting `e/(2W)` from the signed Google-minus-Linux
difference. The bias shifts agreement outside the window.
For each pair the exact supremum is over all real inputs at the same
instant, in nominal seconds.

| Absolute difference | Insertion | Deletion | Attainment |
| --- | ---: | ---: | --- |
| Google − Linux | `43201/86401` | `43200/86399` | At the Linux adjustment |
| Google − Java | `43200/86401` | `43200/86399` | At UTC midnight |
| Java − Linux | `999/1000` | `1` | Approached from before the Linux adjustment |

The first four bounds are greatest elements. The last two theorems give
least upper bounds and strict pointwise inequalities. The proof realizes
any nonnegative error below the bound on the Java ramp before the Linux
adjustment. The fixtures exercise fractions inside the Linux repeat, the
synthetic deletion, both Java ramp starts and midnight joins, and the
Google positive midpoint and negative duration.
The positive Linux fixture uses the 2016 IERS decision and its offsets
36 and 37 seconds. The Google midpoint uses the vendor's hypothetical
end-of-2022 example. Google used its earlier 20-hour smear for the actual
2016 event.
[IERS Bulletin C 52, 6 July 2016](https://datacenter.iers.org/data/16/bulletinc-052.txt)
· [Google example and earlier profiles](https://developers.google.com/time/smear#example_of_the_standard_smear)

## Integration boundary

A shared event timetable can use linear ramps around the transition
midnight with before/after durations `(43200 + e, 43200)` for Google
and `(1000, 0)` for Java. Linux uses a step at transition midnight for
deletion and one physical second before midnight for insertion. Relative
to a step at midnight for both signs, the Linux positive profile
subtracts one extra nominal second just on the inserted interval.
These local profiles require only a single event. For civil labels, obtain the
nominal noon using the Gregorian epoch day times 86,400 plus 43,200.
Apply representation rules to an output after evaluating its clock map.
`Numeric.Timestamp` supplies exact fixed-point ticks and checked Int64
conversion. A UInt64 encoder additionally needs an explicit unsigned
range check, and IEEE binary64 needs unit-aware rounding. Treat timezone
folds and gaps as preimages of zone rules. Preserving a numeric error
bound through a zone conversion requires a shared offset or an extra
offset error term.
[Gregorian civil dates](gregorian-civil-date.md)
· [Exact timestamp ticks](timestamp.md)
· [IEEE 754](ieee754.md)

ECMAScript `Date` storage can use a separate `TimeClip` adapter that
checks a finite Number in the inclusive ±8,640,000,000,000,000 ms range
before truncating toward zero. All retained integer milliseconds are
exact in binary64. Java `Instant` uses signed epoch seconds and a
normalized nanosecond field. Python `datetime.timestamp()` exposes
floating seconds, and `fromtimestamp()` is subject to platform C
conversion limits. These payload and API contracts are separate from
clock conformance.
[ECMA-262, 16th ed. §§21.4.1.1, 21.4.1.31](https://262.ecma-international.org/16.0/#sec-timeclip)
· [Java SE 21 `Instant`](https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/time/Instant.html)
· [Python 3.13.0 `timestamp`](https://docs.python.org/release/3.13.0/library/datetime.html#datetime.datetime.timestamp)
· [Python 3.13.0 `fromtimestamp`](https://docs.python.org/release/3.13.0/library/datetime.html#datetime.datetime.fromtimestamp)

```sh
lake build --wfail +Silmaril.Numeric.UnixProfiles.Thms +Silmaril.Numeric.UnixProfiles.Tests
```
