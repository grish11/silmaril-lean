# Gregorian month intervals and canonical ISO 8601 month text

`CivilMonth` has an unbounded astronomical year and a checked month from
1 through 12. Year 0 is 1 BCE. Its `interval?` starts at the signed
epoch day of the first day of the month and ends after its last day.
Epoch day 0 is 1970-01-01. The interval is half-open and follows the
same Gregorian month and leap rules for every year.
[Gregorian model](gregorian-civil-date.md)
· [Numeric API](../../Silmaril/Numeric/Gregorian/Month/Defs.lean)

The text profile admits exactly `YYYY-MM` with four ASCII year digits
from `0000` through `9999`, one hyphen, and a two-digit month from
`01` through `12`. `parseMonth?` consumes all seven characters, and
`renderMonth?` produces the canonical spelling. The library gives
reduced precision the half-open interval denotation. For example,
`9999-12` denotes `[2932866, 2932897)`, with its exclusive bound at
the start of `10000-01` in the numeric model.
[ISO 8601-1:2019](https://www.iso.org/standard/70907.html)
· [Amendment 1:2022](https://www.iso.org/standard/81867.html)
· [W3C reduced-precision grammar, 27 August 1998](https://www.w3.org/TR/1998/NOTE-datetime-19980827)

`CivilMonth.interval?_eq_some_iff` gives the checked first day and
length, `contains_iff` selects exactly the decoded month, and
`interval_next` identifies the exclusive end with the start of the
successor, including at year rollover. `parseMonth_eq_some_iff` proves
both text round trips, `renderMonth_eq_some_iff` states the lexical
domain, and `parseMonth_length` gives the accepted character count.
[Calendar theorem header](../../Silmaril/Numeric/Gregorian/Month/Thms.lean)
· [Text theorem header](../../Silmaril/Formats/ISO8601/Month/Thms.lean)

## Independent fixtures

The oracle pins CPython 3.13.5 and separates the two sources of expected
signed bounds.

- Nine native `datetime.date` fixtures compute both bounds by subtracting
  the epoch from native dates. They cover leap and common centuries,
  endpoints around the epoch, and the W3C example `1997-07`.
- Six extended-year controls use a 400-year Gregorian translation.
  CPython `datetime.date` is limited to years 1–9999. The oracle maps
  each boundary year to the same phase in 2000–2399, subtracts the
  epoch there, and adds the signed cycle offset. CPython date subtraction
  from 2000-01-01 to 2400-01-01 independently measures the cycle at
  146097 days. CPython `calendar.monthrange` cross-checks the lengths,
  including 29 days in `0000-02` and the year-10000 endpoint of
  `9999-12`.

Each vector checks the signed bounds, the first and last included days
and their neighbors, adjacency, and the lexical result. Lean guards also reject
invalid month numbers, expanded years, non-ASCII digits, wrong widths,
and trailing text.
[Fixture manifest](../../tests/formats/iso8601-month/fixtures.json)
· [Oracle](../../tests/formats/iso8601-month/check-oracle.py)
· [Pinned CPython calendar.py](https://github.com/python/cpython/blob/6cb20a219a860eaf687b2d968b41c480c7461909/Lib/calendar.py)

```sh
targets='+Silmaril.Numeric.Gregorian.Month.Thms +Silmaril.Formats.ISO8601.Month.Thms +Silmaril.Formats.ISO8601.Month.Tests +Silmaril.Numeric.Gregorian.Tests +Silmaril.Formats.ISO8601.Date.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/iso8601-month/Axioms.lean
python3 -I tests/formats/iso8601-month/check-oracle.py
```
