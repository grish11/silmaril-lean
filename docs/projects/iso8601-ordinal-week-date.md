# Extended ordinal and ISO week dates

The date-only profile admits the complete extended ordinal and complete
extended week representations from ISO 8601-1:2019 with Amendment 1:2022.
The [coverage matrix](arrow-parquet-coverage.md) records the wider time and
text profiles. [ISO 8601-1:2019](https://www.iso.org/standard/70907.html) ·
[Amendment 1:2022](https://www.iso.org/standard/81867.html)

```text
ordinal-date = YYYY "-" DDD
week-date    = YYYY "-W" ww "-" D
```

`YYYY` is exactly four ASCII decimal digits with astronomical year numbering
from 0000 to 9999. `DDD` is a three-digit ordinal from 001 through 365 or 366,
according to the Gregorian leap-year rule. The two-digit week is from 01
through 52 or 53 according to the week-year, and weekday `D` is one digit
from 1 (Monday) through 7 (Sunday). `W` is uppercase. The parser consumes the
whole string, and the renderer writes exactly these widths. Basic forms,
reduced precision and expanded years are outside this profile.

`Silmaril.Numeric.Gregorian.ISODate` uses signed epoch days relative to
1970-01-01, with unbounded years. Ordinal day 001 is January 1. ISO week 01
starts on the Monday of the week containing January 4. A week-year may
therefore differ from the civil year in either direction around New Year.
The numeric API checks field validity, converts to and from epoch days, and
interoperates with `CivilDate`. Four-digit limits apply at the lexical
boundary. `Silmaril.Formats.ISO8601.Date` provides date-only parsers and
renderers with exact spelling round trips. Timezone handling and legacy
rebasing are separate profiles. [Calendar date/time API](iso8601-calendar-profile.md)

## Verification

The Gregorian theorem headers prove the civil year bracket, 52-or-53-week
bound, and exact epoch-day and civil round trips for both date types. The
ISO date theorem header proves parser/renderer agreement in both directions
and characterizes the checked range of each renderer.

The independent oracle uses `datetime` from CPython 3.13.5 at commit
`6cb20a219a860eaf687b2d968b41c480c7461909`. The C source has SHA-256
`4f6a91c719ce0d4d6df39170d23753016f44b68a5f73fc661486a17436579802`.
The script checks both lexical directions and civil conversion, around
week-year transitions and Gregorian leap and century boundaries. It uses
`date.isocalendar` and `date.fromisocalendar` for week dates and independent
`date` arithmetic for ordinals, including rejection of week 53 and ordinal
366 in years that do not have them. The lexical year zero and signed-year
semantics are covered by Lean vectors because CPython's `date` ranges from
1 through 9999. [Pinned CPython source and license](https://github.com/python/cpython/blob/6cb20a219a860eaf687b2d968b41c480c7461909/Modules/_datetimemodule.c#L550-L623) ·
[PSF license](https://github.com/python/cpython/blob/6cb20a219a860eaf687b2d968b41c480c7461909/LICENSE)

```sh
lake build --wfail +Silmaril.Numeric.Gregorian.ISODate.Thms +Silmaril.Formats.ISO8601.Date.Thms +Silmaril.Formats.ISO8601.Date.Tests
make check CHECK_TARGETS='+Silmaril.Numeric.Gregorian.ISODate.Thms +Silmaril.Formats.ISO8601.Date.Thms +Silmaril.Formats.ISO8601.Date.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/iso8601-date/Axioms.lean
python3 tests/formats/iso8601-date/check-oracle.py
```
