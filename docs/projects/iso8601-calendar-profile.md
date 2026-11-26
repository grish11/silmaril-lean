# Extended calendar date/time text

The [coverage matrix](arrow-parquet-coverage.md) pins ISO 8601-1:2019 with
Amd 1:2022 and ISO 8601-2:2019 for extensions. This profile starts with the
extended calendar datetime from [RFC 3339 §§5.6–5.7][rfc3339], with the limits
below. [ISO 8601-1][iso1] · [Amd 1:2022][amd] · [ISO 8601-2][iso2]

## Accepted text

The grammar consumes the entire input. Quoted characters are case-sensitive.

```text
datetime = year "-" pair "-" pair "T" pair ":" pair ":" pair [fraction] offset
year     = 4 ASCII digits
pair     = 2 ASCII digits
fraction = "." followed by 1–9 ASCII digits
offset   = "Z" | ("+" | "-") pair ":" pair
```

- The date fields are year, month and day in that order. Four-digit years
  use astronomical numbering, including `0000` for 1 BCE. Month and day
  must name a valid proleptic Gregorian date.
- The time fields are hour, minute and second, in the ranges 00–23, 00–59
  and 00–59. Every day has 86,400 seconds.
- Offset hours and minutes are 00–23 and 00–59. A positive offset means
  east of UTC. The result preserves the distinction between `Z` and
  `+00:00`, which denote the same instant. The unknown-local-offset
  spelling `-00:00` from RFC 3339 §4.3 is rejected.
- A missing fraction means zero. If the digits represent the integer
  coefficient `c` with length `k`, the fraction is exactly
  `c / 10^k` seconds and becomes `c * 10^(9 - k)` nanoseconds. A tenth
  digit is rejected even if the excess digits are all zero.

The profile excludes basic, ordinal and week dates, expanded years,
date-only and time-only text, reduced precision, local-only strings,
lowercase or space separators, decimal commas, 24:00, leap seconds,
offset seconds, durations, intervals and repeating forms. Fixed offsets use
only the supplied number. Named zones, historical zone rules, gaps, folds
and annotations are outside the profile. The matrix pins [RFC 9557][rfc9557]
and [tzdb 2025b][tzdb] for that work. The API exposes parsing and tick conversion.

## Interpretation and checks

`Silmaril.Formats.ISO8601.parse` returns a validated local reading and its
supplied offset. The local reading has a signed Gregorian epoch day and
bounded clock fields. Its `date` projection recovers the civil date.
`localTicks` measures nanoseconds since local 1970-01-01 midnight.
`utcTicks` subtracts the signed offset in nanoseconds to produce an instant
relative to the UTC epoch. Both counts are unbounded. UTC normalization can
cross midnight, the epoch, or the limits of the four-digit input year.

`parseInt64` converts the UTC instant to second, millisecond, microsecond
or nanosecond ticks. It rejects fractional destination ticks before checking
the signed 64-bit range. It uses the fixed-point conversion from [#4187][fixed]
and the calendar validation and epoch-day conversion from [#4220][gregorian].

The [theorem header][thms] proves the validated field correspondence
(`LocalDateTime.ofCivil_eq_ok_iff`), exact fraction interpretation
(`fractionNanoseconds_eq_ok_iff`), recovery of the signed local day
(`LocalDateTime.localTicks_epochDay`), and preservation of the fraction
under UTC normalization (`OffsetDateTime.utcTicks_fraction`).
`parseInt64_eq_ok_iff` characterizes precisely which signed payloads
denote the parsed instant in the requested unit.

## Fixture provenance

The [Lean vectors][tests] use the following sources. The test module is
part of the existing `Silmaril.Formats.+` Lake glob and the
`Silmaril/**` CI path filter.

| Source and version | SHA-256 of upstream bytes | Observations |
| --- | --- | --- |
| [RFC 3339, July 2002, plain text][rfc-txt], §5.8, Internet Society. See the [copyright notice][rfc-copyright]. | `9ab2b8864a85dca73a88f49b0927bc7bc85f596926e4fd1890905777924e700a` | Fractional UTC time, offset crossing into the next day, the literal historical minute offset, and rejection of both leap-second examples. |
| [Arrow integration datetime JSON][arrow], matrix pin `5a26d35785ff8761e56d79eebff971f6f737e18c`, 1.0.0 little-endian, [Apache-2.0][arrow-license]. | `17de56ca202bf583111a2a23b33c05fe78ac39814d7bd08613c25ba74990adb2` | Batch 0, column `f11`, valid rows 0 and 2. The field is a timestamp in seconds with timezone `UTC`. The text vectors give exactly `-62135596800` and `177798586609` seconds. |

The Arrow text inputs were generated with CPython 3.13.5's standard
library, adding each signed count to the UTC epoch and replacing the
resulting `+00:00` suffix with `Z`.

```python
from datetime import datetime, timedelta, timezone

epoch = datetime(1970, 1, 1, tzinfo=timezone.utc)
for ticks in (-62135596800, 177798586609):
    text = (epoch + timedelta(seconds=ticks)).isoformat()
    print(text.removesuffix("+00:00") + "Z", ticks)
```

The other vectors are authored controls under the repository's MIT
license. They cover pre-epoch fractions, signed endpoints and their
adjacent overflow, positive and negative offset rollover, valid and
invalid leap days, and rejected spelling and precision variants.
These checks exercise text and exact tick denotation directly. Arrow IPC
and Parquet interoperability are separate coverage rows.

```sh
lake build --wfail +Silmaril.Formats.ISO8601.Thms +Silmaril.Formats.ISO8601.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
```

[rfc3339]: https://www.rfc-editor.org/rfc/rfc3339#section-5.6
[rfc-txt]: https://www.rfc-editor.org/rfc/rfc3339.txt
[rfc-copyright]: https://www.rfc-editor.org/rfc/rfc3339#page-18
[rfc9557]: https://www.rfc-editor.org/rfc/rfc9557
[iso1]: https://www.iso.org/standard/70907.html
[amd]: https://www.iso.org/standard/81867.html
[iso2]: https://www.iso.org/standard/70908.html
[tzdb]: https://github.com/eggert/tz/tree/7e1145bfdb9630c127841dc8ce808a937a300938
[fixed]: https://github.com/hiloopai/silmaril-lean/pull/4187
[gregorian]: https://github.com/hiloopai/silmaril-lean/pull/4220
[arrow]: https://github.com/apache/arrow-testing/blob/5a26d35785ff8761e56d79eebff971f6f737e18c/data/arrow-ipc-stream/integration/1.0.0-littleendian/generated_datetime.json.gz
[arrow-license]: https://github.com/apache/arrow-testing/blob/5a26d35785ff8761e56d79eebff971f6f737e18c/LICENSE.txt
[thms]: ../../Silmaril/Formats/ISO8601/Thms.lean
[tests]: ../../Silmaril/Formats/ISO8601/Tests.lean
