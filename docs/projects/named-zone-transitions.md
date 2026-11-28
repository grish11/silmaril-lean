# Supplied named-zone transition tables

`Silmaril.Numeric.TimeZone.Named.Defs` accepts a name, start and stop Unix
seconds, an initial signed offset in seconds, and a list of transition
seconds and new offsets. The name is an opaque label supplied by the caller.
`NamedZone.ofTransitions?` checks a nonempty half-open support `[start, stop)`
and strictly increasing cuts in its interior. Each new offset applies at its
cut, inclusive. The adapter embeds the table into the existing nanosecond
schedule and uses that schedule for both directions. [Core time zone rules](time-zone-rules.md)

`NamedZone.toLocal?` accepts typed UTC ticks and returns the exact wall
coordinate at nanosecond precision for an instant in the support.
`NamedZone.resolveLocal` accepts typed local ticks, normalizes the input
exactly, and returns one of three outcomes.

- `noSolution` means the supplied interval contains no exact preimage. It
  includes gaps and wall readings beyond the available data.
- `unique` gives the single covered Unix coordinate.
- `ambiguous` returns at least two covered Unix coordinates. It retains every
  candidate in strictly increasing order, including folds with more than two
  preimages in a supplied table.

All four source tick units are scaled exactly. Inverse results are nominal
Unix nanoseconds, so a caller narrowing to another unit can use the existing
checked timestamp conversion. The Unix scale uses uniform days. Lookup
by name, TZif parsing, recurring rules, extrapolation, leap seconds and
legacy INT96 rebasing are outside this profile.

`NamedZone.ofTransitions_isSome_iff` states the admission check.
`toLocal_isSome_iff` identifies the defined interval. `resolveLocal_candidates`
relates the classification to the core enumeration. `mem_resolveLocal_iff`
proves exact forward inversion and completeness on that interval.
`resolveLocal_eq_noSolution_iff` characterizes an empty preimage and
`resolveLocal_pairwise` proves strict UTC order.

## Independent fixtures

The oracle uses CPython 3.13.5 `zoneinfo.ZoneInfo.from_file` on TZif members
of the pinned Python `tzdata` 2025.2 wheel, which identifies its data as IANA
2025b. It reads those bytes directly and uses no host timezone search path.
The wheel SHA-256 is
`1a403fada01ff9221ca8044d701868fa132215d84beb92242d9acd2147f667a8`.
[IANA release](https://data.iana.org/time-zones/releases/tzdata2025b.tar.gz) ·
[Python tzdata 2025.2](https://pypi.org/project/tzdata/2025.2/) ·
[Pinned CPython 3.13.5 source](https://github.com/python/cpython/tree/6cb20a219a860eaf687b2d968b41c480c7461909/Lib/zoneinfo)

The script checks the listed cut seconds and scans each supplied segment at
hourly points plus its terminal second. It compares forward images and
both local `fold` choices around the UTC and wall boundaries. It retains the
nanoseconds below Python's microsecond precision separately. Whole-second
transitions keep that residual on the same side of a cut, and the script
adds it back exactly. Coverage clipping is applied to both directions.

| Zone | Covered UTC interval | Boundary exercised |
| --- | --- | --- |
| `America/New_York` | 2025-01-01 to 2026-01-01 | One-hour spring gap and autumn fold |
| `Asia/Kathmandu` | 1985-12-31 to 1986-01-02 | Fifteen-minute gap and local date rollover |
| `Europe/Paris` | 1911-03-10 to 1911-03-12 | Pre-epoch fold with a 561-second offset change |

```sh
lake build --wfail +Silmaril.Numeric.TimeZone.Named.Thms +Silmaril.Numeric.TimeZone.Named.Tests
make check CHECK_TARGETS='+Silmaril.Numeric.TimeZone.Named.Thms +Silmaril.Numeric.TimeZone.Named.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/numeric/named-zone/Axioms.lean
curl -fLsS https://files.pythonhosted.org/packages/5c/23/c7abc0ca0a1526a0774eca151daeb8de62ec457e77262b66b359c3c7679e/tzdata-2025.2-py2.py3-none-any.whl -o /tmp/tzdata-2025.2.whl
python3 tests/numeric/named-zone/check-zoneinfo.py /tmp/tzdata-2025.2.whl
```
