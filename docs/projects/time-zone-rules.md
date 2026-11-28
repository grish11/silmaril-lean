# Time zone rules on nominal Unix time

`Silmaril.Numeric.TimeZone.Defs` uses the existing Timestamp kind and unit
indices. `UnixTime` is `Timestamp.Ticks .utcInstant .nanosecond`, an unbounded
signed count relative to 1970-01-01 00:00:00 on the nominal Unix coordinate.
`WallTime` is `Timestamp.Ticks .localReading .nanosecond`, measured from local
1970-01-01 00:00:00 on uniform 86,400-second days. `Ticks.denote` normalizes
seconds, milliseconds or microseconds to either coordinate without rounding.
`Offset.nanoseconds` is a signed displacement added to Unix time to obtain wall
time. `Offset.ofSeconds` embeds whole-second offsets exactly. Both offsets and
transition instants may have nanosecond precision.

A clock or UTC-label model supplies the nominal Unix coordinate before applying
zone rules. Any ambiguity in mapping physical instants or leap-second labels to
that coordinate belongs to the clock model. A zone fold instead gives multiple
distinct nominal Unix coordinates for one wall reading. Composition with a
real-valued clock requires an exact nanosecond input or an explicit quantizer in
the clock adapter. The zone component has no leap-second labels or rounding
rules. [Timestamp contract](timestamp.md) · [Gregorian contract](gregorian-civil-date.md)

## Rules and inversion

- `Rules.fixed` applies one offset at every input. `Offset.toLocal` and
  `Offset.fromLocal` are total inverses.
- `Schedule.ofTransitions?` accepts a nonempty support interval `[start, stop)`,
  the initial offset and strictly increasing transitions inside that interval.
  A transition changes the offset at its instant, inclusive. The final segment
  ends at the exclusive support boundary. An empty transition list describes a
  constant offset over the finite support.
- `Rules.offsetAt?`, `Rules.toLocal?` and `Rules.toCivil?` succeed on supported
  inputs. `CivilReading` pairs a proleptic Gregorian date with the nanosecond
  count since local midnight. `ofWall` splits signed ticks by Euclidean division
  and `toWall?` validates and encodes the fields.
- `Rules.Matches` is the forward relation at a given wall reading.
  `Rules.candidates` enumerates every supported preimage in strictly increasing
  nominal Unix order. `Rules.civilCandidates?` returns `none` for invalid civil
  fields and `some []` for a valid reading with no candidate in the support.
- `Rules.resolve?` with `.unique` requires exactly one candidate. `.earliest`
  and `.latest` choose the minimum and maximum nominal candidates. Every policy
  fails on an empty list, and no policy shifts a nonexistent reading to a
  neighboring time.

## Transition boundaries

A segment `[a, b)` with offset `o` covers exactly the wall interval
`[a + o, b + o)`. An adjacent pair `[a, t)`, `[t, b)` with offsets `p`, `q`
has a gap `[t + p, t + q)` within its translated outer span
`[a + p, b + q)`. The pair has two preimages exactly in
`[max(a + p, t + q), min(t + p, b + q))`. The outer endpoints can clip the
fold when a neighboring segment is short. Both laws include the lower endpoint
and exclude the upper endpoint.

`Rules.scheduled_candidates_length` counts the translated intervals covering
a wall reading across the whole schedule. A third segment can fill a gap of
an adjacent pair or add a third candidate to a fold. Zero candidates means no
preimage in the supplied support, which includes wall readings beyond the data
horizon. There is no assumption that offsets are restricted to a particular
range. Given caller-supplied offset bounds `[lo, hi]`, the signed difference of
two supported wall readings at the same nominal instant is the difference of
their active offsets and lies in `[lo - hi, hi - lo]`. The earliest to latest
spread of any nonempty candidate list is at most `hi - lo`.

## IANA examples

The kernel-checked examples transcribe selected rows from IANA tzdata release
2025b. The release archive has SHA-256
`11810413345fc7805017e27ea9fa4885fd74cd61b2911711ad038f5d28d71474`.
[IANA release archive](https://data.iana.org/time-zones/releases/tzdata2025b.tar.gz) ·
[North America source](https://github.com/eggert/tz/blob/2025b/northamerica) ·
[Asia source](https://github.com/eggert/tz/blob/2025b/asia)

| Zone | Nominal UTC transition | Unix seconds | Offset change | Local interval |
| --- | --- | ---: | --- | --- |
| America/New_York | 2025-03-09 07:00:00 | 1741503600 | −05:00 → −04:00 | March 9 gap [02:00, 03:00) |
| America/New_York | 2025-11-02 06:00:00 | 1762063200 | −04:00 → −05:00 | November 2 fold [01:00, 02:00) |
| Asia/Kathmandu | 1985-12-31 18:30:00 | 504901800 | +05:30 → +05:45 | January 1, 1986 gap [00:00, 00:15) |

The New York fixture covers `[2025-01-01, 2026-01-01)` and Kathmandu covers
`[1985-12-31, 1986-01-02)`, with both horizons measured at nominal UTC
midnight. The examples check the transition nanosecond and its predecessor,
local gap and fold endpoints, the two nominal readings of the folded hour,
calendar rollover and a fixed +05:45 offset. Synthetic cases cover rejected
schedules, subsecond offsets and transitions, and more than two candidates.

For independent reproduction, extract the pinned release and run the following
from the extracted source directory.

```sh
mkdir zoneinfo
zic -d "$PWD/zoneinfo" northamerica asia
TZDIR="$PWD/zoneinfo" zdump -V -c 2025,2026 America/New_York
TZDIR="$PWD/zoneinfo" zdump -V -c 1985,1987 Asia/Kathmandu
```

The executable Lean rules consume explicit transition lists and scan the
segments linearly. Data acquisition, tzdb and TZif parsing, recurring-rule
expansion, abbreviations and future updates are outside this component.
The source reproduction is separate from the Lean checks, which reduce the
transcribed inputs in the kernel without fetching external data.

```sh
lake build --wfail +Silmaril.Numeric.TimeZone.Thms +Silmaril.Numeric.TimeZone.Tests
make check CHECK_TARGETS='+Silmaril.Numeric.TimeZone.Thms +Silmaril.Numeric.TimeZone.Tests'
```
