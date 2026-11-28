# Checked Parquet DATE round trip through typed CSV

`Parquet.Date.ToCsv.convert` reads the checked one-column DATE source
through its existing event API. It verifies the exact declared field
name and nullability and concatenates the signed nullable Date32 slots
in footer order. An open or late group error preserves its original
cause and index. Export succeeds after EOF when the rows fit the
total CSV row limit and the canonical output fits its byte limit.
The output uses the existing typed calendar CSV grammar. A present cell
is `TYYYY-MM-DD` for valid proleptic Gregorian dates in astronomical years
`0000`–`9999` (inclusive signed days −719528 through 2932896). A nullable
null is `N`. The writer quotes all fields and writes CRLF.
[Event source](parquet-date-events.md)
· [Typed CSV profile](date32-csv.md)
· [Exporter](../../Silmaril/Formats/Parquet/Date/ToCsv/Defs.lean)

`Parquet.Date.RoundTrip.ViaCsv.convert` passes the canonical CSV to
the checked CSV-to-Parquet DATE bridge. The source Parquet read limits,
CSV export row and byte caps, and CSV import row and byte caps are
independent. Import also uses its own intermediate IPC observation limits,
Parquet writer limits and final DATE readback limits. The composed call
materializes bytes and returns a complete file after both legs succeed.
The output has one explicit INT32 DATE group with modern and converted
DATE annotations. A zero-group file or any admitted sequence containing
only empty groups passes through header-only CSV and returns an explicit
zero-row group.
[CSV-to-Parquet contract](parquet-date-from-csv.md)
· [Composition](../../Silmaril/Formats/Parquet/Date/RoundTrip/ViaCsv/Defs.lean)

The export laws characterize checked row admission, the canonical CSV
and both CSV caps. Under a shared declaration, two successful exports
have equal canonical bytes exactly when the ordered nullable signed
rows agree. The round-trip law compares the same logical descriptor
and the original footer-order concatenation with the output singleton
group. With two successful cycles, equality of the output row
observations is equivalent to equality of the inputs' row observations.
The comparison forgets source group cuts, empty-group positions,
physical annotation variants, and wire bytes.
[Export laws](../../Silmaril/Formats/Parquet/Date/ToCsv/Thms.lean)
· [Round-trip laws](../../Silmaril/Formats/Parquet/Date/RoundTrip/ViaCsv/Thms.lean)

## Independent checks

Five input files are produced by PyArrow 26.0.1, including a real zero-group
file, alternate group cuts over identical rows, a changed null position,
and reordered dates. Two supplementary inputs use the existing native
multi-group writer over PyArrow IPC to produce explicit empty PLAIN V1
groups. PyArrow validates those input groups as well. The pinned refusal
for PyArrow's own empty-group file reports `.invalidMetadata .pageInterval`.
Its empty chunk advertises zero values and page offset zero, outside the
checked footer profile. Native output files are verified with PyArrow and
Apache Thrift 0.25.0 for signed slots, nulls, exact schema, one group, raw
DATE annotations, and PLAIN V1 page bytes. CPython 3.13.5 independently
checks canonical CSV bytes and lexical rows. The controls also cover the
independent CSV row limits, a later out-of-profile date, and a Thrift
encoding edit producing an indexed late group failure.
[Fixture hashes](../../scripts/parquet-date-csv-roundtrip-oracle/fixtures.json)
· [Oracle](../../scripts/parquet-date-csv-roundtrip-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.ToCsv.Thms +Silmaril.Formats.Parquet.Date.RoundTrip.ViaCsv.Thms +Silmaril.Formats.Parquet.Date.RoundTrip.ViaCsv.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-csv-roundtrip/Axioms.lean
python3 -I scripts/parquet-date-csv-roundtrip-oracle/check.py
```

The oracle accepts `--pyarrow-path` and `--thrift-path` for separately
unpacked pinned wheels.
