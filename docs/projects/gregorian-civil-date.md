# Proleptic Gregorian civil dates

`Silmaril.Numeric.Gregorian.Defs` models a civil date as an unbounded integer
`year` and 1-based natural-number `month` and `day` fields. Years use astronomical
numbering. Year 1 is 1 CE, year 0 is 1 BCE, and year −1 is 2 BCE. Gregorian rules
apply uniformly, including across October 1582. A year is a leap year if it is
a multiple of 4 and either a multiple of 400 or indivisible by 100.
This makes year 0 a leap year. February has 28 or 29 days, April,
June, September and November have 30, and the other months have 31.

`CivilDate.valid` checks `CivilDate.Valid`. The month must be in 1–12 and the
day must be in 1 through the length of that month. `CivilDate.toEpochDay?`
returns `none` for invalid fields. For valid fields it returns an unbounded
signed `Int` day count. Day 0 is 1970-01-01, day −1 is 1969-12-31, and day 1
is 1970-01-02. `CivilDate.ofEpochDay` is total on `Int` and always returns a
valid date.

The model reuses `Std.Time` for leap years, month lengths and cumulative month
starts. It uses Euclidean division to identify the 400-year era of a signed day
and the library's finite bisection to locate the year and month inside it. The
[theorem header](../../Silmaril/Numeric/Gregorian/Thms.lean) proves the leap and
month rules, validation and rejection, the epoch anchor, the 365- or 366-day
spacing between January starts, and the 146097-day period per 400 years. It
proves both round trips on the full domain of valid civil dates and signed
epoch days.

## Timestamp interface

Epoch days supply the date component for the Arrow and Parquet epoch conventions.
The caller supplies the interpretation, such as a UTC instant or a local wall
reading. The civil-date layer exposes only the signed day count and can be built
independently of the exact fixed-point timestamp module. A future adapter can
split or compose uniform-day ticks and apply the chosen interpretation.

Subsequent work includes ISO 8601 syntax profiles for calendar, ordinal and week
dates, expanded year spellings, clock fields and leap seconds, UTC offsets and
time zones, fractional precision and its conversion rules, durations and intervals,
and the Arrow and Parquet adapters and wire codecs.

## References

- RFC 3339 (July 2002), §5.7 and Appendix C, for Gregorian month lengths and the
  leap-year rule. [RFC Editor](https://www.rfc-editor.org/rfc/rfc3339.html#section-5.7)
- W3C XML Schema Definition Language 1.1 Part 2 (5 April 2012), §3.3.7.1, for the
  astronomical year-numbering convention. [Dated recommendation](https://www.w3.org/TR/2012/REC-xmlschema11-2-20120405/datatypes.html#dateTime-value-space)
- Apache Arrow 22.0.0, `Date` and `Timestamp` in `format/Schema.fbs`, for the epoch
  conventions. [Pinned schema](https://github.com/apache/arrow/blob/5aeb5f217f1ba39c428c9b481f393bd37097f69e/format/Schema.fbs#L238-L322)
- Apache Parquet Format 2.12.0, `TIMESTAMP` in `LogicalTypes.md`, for instant and
  local epoch conventions. [Pinned specification](https://github.com/apache/parquet-format/blob/7e401bf1c970488457670f17cf103bd03acea9c1/LogicalTypes.md#L348-L425)
- ISO 8601-1:2019 and ISO 8601-2:2019 are references for future interchange work.
  [Part 1](https://www.iso.org/standard/70907.html) · [Part 2](https://www.iso.org/standard/70908.html)

## Checks

```sh
lake build --wfail +Silmaril.Numeric.Gregorian.Thms +Silmaril.Numeric.Gregorian.Tests
```
