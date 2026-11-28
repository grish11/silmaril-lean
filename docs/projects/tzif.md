# Bounded TZif v2/v3 transition blocks

`Silmaril.Formats.TZif.parse` reads a supplied byte string under a caller-provided
byte budget. The profile uses [RFC 9636 §§3.1–3.3, 4, 6.1], published October
2024. The first header and its 32-bit block size locate the second header.
Only the second block supplies time types and transition data. Its instants
are signed big-endian 64-bit seconds and its offsets are signed big-endian
32-bit seconds. Zero leap counts in both headers allow the transition
coordinates to be used on the nominal Unix scale. Offsets retain all seconds.

The parser checks the header versions and counts, selected layout, strict
transition order, indexed types and NUL-terminated designations, DST and
standard/wall and UT/local flags, and exact footer framing. Each accepted
transition refers to a `Fin` index into the selected type array. The footer is
retained as opaque printable ASCII. The 32-bit compatibility payload is
skipped by its checked length. Its records and the spelling and consistency
of the POSIX string are outside this parser's validation profile. The parser
rejects v1, v4 and leap-bearing files.

## Supported intervals

`Block.toSchedule?` takes explicit whole-second bounds `[start, stop)` and
returns a `Numeric.TimeZone.Schedule` for exact nanosecond lookup and local
inverse candidates. At the left boundary it uses the last transition at or
before `start`, or RFC 9636 type zero before the first transition. Interior
transitions take effect at their listed instant and retain their original
order. A `-00` designation marks unspecified local time. Any part of the
requested interval using such a type makes schedule construction fail.

With transitions, the last transition is the exclusive ceiling even when
there is a nonempty footer. With zero transitions, only an empty footer and a
specified type zero yield a constant schedule under the caller's bounds.
This deliberately leaves POSIX tail interpretation, version 4, leap seconds,
and zone database lookup to separate profiles.

`locate_bounds` verifies the file limit and room for footer framing.
`parse_selected_sequence` identifies the wire-order read of the selected
entries. `schedule_reflects` identifies the schedule's bounds, initial offset
and exact subsequence of the parsed entries. `schedule_support` and
`schedule_candidate_in_support` show that forward conversion and every inverse
candidate stay inside the caller's interval.

## Reproduce checks

The oracle uses CPython 3.13.5 `struct` and `zoneinfo.ZoneInfo.from_file` with
three SHA-256-pinned binary entries from the [tzdata 2025.2 wheel] (IANA 2025b).
The wheel hash and each member's hash are checked before Lean sees the bytes.
Paris exercises pre-1902 timestamps and a non-minute offset. Gaza supplies
v3 data with transitions after the signed 32-bit endpoint. UTC exercises a
transitionless file whose footer rules remain opaque. Mutations exercise
truncation, malformed indices, excessive counts and other layout failures.
The oracle also checks both support boundaries, signed and subsecond lookup,
and the synthetic empty-footer and unspecified-type cases.

```sh
lake build --wfail Silmaril.Formats.TZif.Defs Silmaril.Formats.TZif.Thms
make check CHECK_TARGETS='+Silmaril.Formats.TZif.Defs +Silmaril.Formats.TZif.Thms'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/tzif/Axioms.lean
python3 -m pip download --no-deps --only-binary=:all: tzdata==2025.2 -d /tmp/tzif-fixtures
python3 -I tests/formats/tzif/check-fixtures.py /tmp/tzif-fixtures/tzdata-2025.2-py2.py3-none-any.whl
```

[RFC 9636 §§3.1–3.3, 4, 6.1]: https://www.rfc-editor.org/rfc/rfc9636.html#section-3.1
[tzdata 2025.2 wheel]: https://pypi.org/project/tzdata/2025.2/#files
