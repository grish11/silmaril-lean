# Canonical UTC tick text

`ISO8601.UTCText.format` writes signed UTC ticks in the existing [extended
calendar timestamp profile]. `formatInt64` accepts a signed 64-bit payload
with its supplied unit. Both use the proved `UnixRepresentation.CivilTime.ofTicks`
conversion on the nominal 86,400-second day scale. [RFC 3339 §5.6–5.7]

The spelling is `YYYY-MM-DDTHH:MM:SS[.fraction]Z`, with uppercase `T` and
`Z` and four ASCII year digits. The source unit determines the fractional
width, even when every digit is zero.

| Unit | Fractional digits | Spelling at the epoch |
| --- | ---: | --- |
| second | 0 | `1970-01-01T00:00:00Z` |
| millisecond | 3 | `1970-01-01T00:00:00.000Z` |
| microsecond | 6 | `1970-01-01T00:00:00.000000Z` |
| nanosecond | 9 | `1970-01-01T00:00:00.000000000Z` |

The formatter uses the parser's astronomical years 0000 through 9999.
Outside that interval it returns `.yearOutOfRange year` with the decoded UTC
civil year. The bound applies to the decoded year independently of integer
width. The signed 64-bit endpoints for seconds, milliseconds, and microseconds
are outside the year profile. Both nanosecond endpoints are admitted. Before
the epoch, Euclidean division retains the nonnegative fraction within the
previous second. For example, −1 ms emits `1969-12-31T23:59:59.999Z`.

`format_eq_error_iff` characterizes the typed year error. `parse_format` shows
that the existing parser recovers a UTC reading with `Z` and that exact
rescaling to the source unit returns the original ticks. The signed entry
points satisfy `parseInt64_formatInt64`. Local readings, offset spelling,
named zones, expanded years and leap seconds are outside this formatter.

## Independent fixtures

The oracle pins CPython 3.13.5 and the SHA-256 of its generated golden
observations. It uses integer `divmod` and standard-library Gregorian date
arithmetic. It shifts by independently counted 400-year Gregorian cycles to
cover year zero and the large civil years of signed endpoints. The vectors
exercise all four widths, negative fractions, whole-day rollover, both signed
endpoints in each unit, and both sides of the four-digit year boundaries.

```sh
lake build --wfail Silmaril.Formats.ISO8601.UTCText.Thms
make check CHECK_TARGETS='+Silmaril.Formats.ISO8601.UTCText.Thms +Silmaril.Formats.ISO8601.Tests +Silmaril.Numeric.UnixRepresentation.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/iso8601-utc-text/Axioms.lean
python3 -I tests/formats/iso8601-utc-text/check-fixtures.py
```

[extended calendar timestamp profile]: iso8601-calendar-profile.md
[RFC 3339 §5.6–5.7]: https://www.rfc-editor.org/rfc/rfc3339#section-5.6
