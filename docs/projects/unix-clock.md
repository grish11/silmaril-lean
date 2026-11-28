# Unix clock, UTC, and leap smears

Import `Silmaril.Numeric.UnixClock.Defs` for the model and `Silmaril.Numeric.UnixClock.Thms`
for its laws. The model uses exact real seconds. The generic schedules and their finite
tables use unbounded integer day indices and offsets.

## The two coordinates

| Coordinate | Unit and origin |
| --- | --- |
| Physical | SI seconds along TAI, from **1970-01-01 00:00:00 TAI** |
| Nominal Unix | Uniform 86400-second Gregorian days, from the label **1970-01-01 00:00:00 UTC** |

The physical axis increases with elapsed SI time. The two origins name different instants.
`unixEpoch`, `civilToUnix?` and `unixToCivil` specify the nominal epoch and its Gregorian
round trips, including signed and fractional seconds. `unixSeconds` maps
`Timestamp.Ticks .utcInstant unit` to this coordinate through its exact nanosecond
denotation. The nominal conversion accepts ordinary seconds of day in `[0, 86400)`.
The signed, fractional calendar conversion extends POSIX's nonnegative integral
mapping.

POSIX specifies 86400 seconds per nominal day and leaves the relationship between a
system's current epoch count and actual UTC unspecified. `Schedule.sharp` implements
the right-edge fold defined below as one particular projection.
[POSIX.1-2024, §4.19](https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/V1_chap04.html#tag_04_19)

## Composing with a timezone conversion

The handoff type is `Timestamp.Ticks .utcInstant .nanosecond`. Its signed count
`n` denotes `n / 10^9` nominal seconds from 1970-01-01 00:00:00 UTC. A physical
instant first goes through the selected `Convention.forward`, such as
`iersUnix.forward`, to obtain nominal seconds `y`. An ordinary Gregorian label
can instead use `civilToUnix?`.

For exact composition, pass `⟨n⟩` to the timezone model with the equality
`(n : ℝ) = y * 10^9`. The laws `unixSeconds_nanoseconds_eq_iff` and
`existsUnique_unixSeconds_nanosecond_iff` establish exact denotation and
uniqueness. An existing integral Unix timestamp in a different unit can use
`Timestamp.Ticks.denote` to obtain the same nanosecond type directly. For
off-grid readings, the caller supplies an explicit quantization rule and passes
the resulting signed nanosecond count. In the reverse direction `unixSeconds`
embeds any selected nominal timestamp exactly.

A timezone conversion produces `Timestamp.Ticks .localReading .nanosecond`.
On reverse conversion, the timezone layer relates that local reading to nominal
Unix candidates. Each nominal candidate can then be passed through
`unixSeconds` and into the physical `Convention.fiber` for the chosen leap
projection. The timezone relation and the leap relation each retain their own
folds and gaps.

## Signed leap schedule and published support

A schedule keys each signed unit adjustment by the Gregorian epoch day of the
first midnight after the leap. If day `d` has physical midnight `M(d)`, its valid
physical interval is `[M(d), M(d+1))`. UTC labels carry a date and the elapsed
seconds within that interval. The encoder `Schedule.toTAI?` rejects invalid Gregorian
dates and invalid seconds of day. Its decoder `Schedule.ofTAI` round-trips both
ways on valid labels. The general schedule permits hypothetical negative leaps
and extends with constant offsets outside its finite list.

The right-edge step applies the new offset at `M(d)`. For a positive leap, the
preceding date has length 86401 and its seconds of day in `[86400, 86401)`
represent **23:59:60** and its fractions. These are distinct UTC labels.
For `0 ≤ f < 1`, the sharp nominal reading `86400 * d + f` represents both
`M(d) - 1 + f` (the leap label) and `M(d) + f` (after midnight), subject to
the convention's supported domain. For a negative leap, the preceding date has
length 86399. Its last nominal second, the label 23:59:59 and its fractions,
has an empty fiber.
[ITU-R TF.460-6, Annex 1](https://www.itu.int/rec/R-REC-TF.460-6-200202-I/en)

`iersSchedule` transcribes the IERS `Leap_Second.dat` revision through Bulletin C 72
(6 July 2026). The 1972-01-01 row establishes **TAI − UTC = 10 s**. The subsequent
27 rows are positive leaps, with the last offset change to **37 s** at
2017-01-01 00:00:00 UTC. Bulletin C 72 confirms there is no transition at the end
of December 2026. The supported UTC interval starts at 1972-01-01 00:00:00 inclusive
and ends at 2027-06-28 00:00:00 exclusive, using the file's expiry date as the cutoff.
The corresponding interval in the physical coordinate is `[63072010, 1814140837)`.
Tests check each dated row and the exact transition set.
[IERS Leap_Second.dat](https://hpiers.obspm.fr/iers/bul/bulc/Leap_Second.dat) ·
[IERS Bulletin C 72](https://hpiers.obspm.fr/iers/bul/bulc/bulletinc.72)

| Source snapshot | SHA-256 of original bytes |
| --- | --- |
| IERS `Leap_Second.dat`, through Bulletin C 72 | `6cb6f5d4b819f2e568e25db4b0b26d89dedf031fdffb18bc94d40f4e94e268d7` |
| IERS Bulletin C 72 | `310e172eadacacca3adf92cb9bd646fcc0d6320e35e996a106d2644ede3b52f0` |

Use `iersToTAI?`, `iersOfTAI?`, `iersTAIMinusUTC?` and `iersUnix` for the
supported snapshot. Pre-1972 UTC, including the actual physical instant
of the 1970 UTC epoch label, is outside this model, as are UTC dates at and after
expiry. The snapshot has no runtime source lookup. `iersSchedule` exposes the
underlying finite mathematical schedule for analysis.

## Domains, inverse fibers, and discrepancy

A `Convention` is a function on a stated physical support. `Convention.fiber`
is its relational inverse. A `Convention.Resolver` chooses a supported member of
the fiber and carries the selection law as a proof. An injective restriction has an
equivalence on its exact image via `Convention.equivRange`. For example,
`Schedule.sharpOn_injective_of_subset_day` applies to any restriction within
one UTC day.

`Convention.worstError` takes the extended nonnegative supremum of absolute
nominal differences on the intersection of the physical supports. The empty
intersection yields zero. An unbounded difference yields infinity. A sample
attains the supremum exactly when it bounds every sample. The resolver form
`Convention.Resolver.worstError` compares selected physical instants at nominal
readings in the intersection of the two reverse domains.

## Smear supports and inversion

Each `Ramp` is nondecreasing and continuous, with values in `[0, 1]`,
zero through its left endpoint and one from its right endpoint.
A window brackets the sharp transition. For the chosen right-edge step,
disagreement is possible only on the half-open window `[left, right)`.
`Schedule.smear` subtracts the signed sum of these ramps and the same baseline
as the sharp clock. The exact difference is a sum over active windows. Its
absolute value is at most their count, so disjoint windows give a one-second
worst-case bound on any common support. A window starting at its sharp
transition attains one second there if it is the only active window and the
instant is on the common support. The tests give an overlapping example with
a 1.5-second error. Outside the union of windows the two clocks agree.

`Ramp.linear` is a clamped linear interpolation with a corner at each endpoint.
A smear is continuous and reaches every reading on the full physical line,
since a finite schedule has bounded correction. An upper slope bound below
one on the total correction makes the smear strictly increasing, giving
`Schedule.smearEquiv` and, on any supported restriction, an inverse on its
exact image. With clamped linear ramps, a sufficient condition is that the
sum of the reciprocal widths is less than one. A positive one-second ramp
over a one-second window can flatten the clock.

These are mathematical APIs over reals. Clock I/O, storage representation and
overflow, time zones, text parsing, and specific vendor profiles are outside
this development.

## Checks

```sh
lake build --wfail +Silmaril.Numeric.UnixClock.Tests
```

The regression module exercises the public headers and is included in the
`Silmaril` library's build glob.
