# Typed civil-date CSV to one Parquet DATE group

`Parquet.Date.FromCsv.convert` takes a declared UTF-8 field name and
nullability, and admits the existing one-column typed CSV profile. The
header must match exactly. Present cells are `TYYYY-MM-DD` for valid
proleptic Gregorian dates in astronomical years `0000`–`9999`. The
corresponding inclusive signed day offsets are −719528 through 2932896.
`N` denotes null in a nullable column. The typed decoder reports the
first required null with zero-based coordinates. An empty present value
and dates outside the admitted language fail the cell parser.
[Typed CSV grammar and date laws](date32-csv.md)
· [Executable API](../../Silmaril/Formats/Parquet/Date/FromCsv/Defs.lean)

The bridge composes the existing checked CSV importer and annotated
single-batch Parquet writer. The CSV limits cap input bytes before
decoding and input rows before IPC emission. IPC observation limits
govern intermediate emission and its certification. The Parquet leg
uses that same IPC readback limit record. Its own writer limits govern
the file and page emission, and separate checked DATE readback limits
govern release of the result. The earlier leg returns its original
typed error under `.csvToIpc`. Later errors carry the original
`.ipcToParquet` cause. The bridge materializes the typed input,
intermediate IPC stream and resulting file within the component limits.
[Single-batch Parquet writer profile](arrow-date32-to-parquet.md)
· [Pinned Parquet DATE semantics](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#date)
· [Pinned Parquet Thrift IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

`convert_eq_ok_iff` characterizes success as success of the two
components with shared intermediate IPC readback limits.
`convert_readback` identifies the exact declared flat INT32 leaf,
modern and matching converted DATE annotations, a single group at
index zero, and that group's count and ordered nullable signed words.
Header-only CSV produces one explicit zero-row group. The law applies
to successful conversions under the supplied limits.
`convert_csvToIpc_error` fixes the earlier error before any Parquet
writer or readback step.
[Theorem header](../../Silmaril/Formats/Parquet/Date/FromCsv/Thms.lean)

## Independent checks

CPython 3.13.5 generates typed CSV, including a quoted header containing
a comma. PyArrow 26.0.1 independently verifies the declared schema, group
count, and exact signed values, including the pre-epoch dates and both
text-profile endpoints. PyArrow date formatting supplies the year-zero
spellings and the adjacent outside-range controls. CPython datetime
cross-checks the supported years 0001–9999. Apache Thrift 0.25.0 checks
both annotations, the PLAIN V1 page header, definition levels and exact
packed signed words of four Lean-emitted files. Two files independently
verify that required and optional header-only inputs produce one empty
group. Seven pinned CSV refusals cover required null, header and width
mismatch, invalid leap day, adjacent years and unterminated quoting.
Native guards distinguish CSV byte and row caps, the intermediate IPC
batch cap, Parquet file limit and checked readback footer limit.
[Fixture hashes](../../scripts/parquet-date-from-csv-oracle/fixtures.json)
· [Oracle](../../scripts/parquet-date-from-csv-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.FromCsv.Thms +Silmaril.Formats.Parquet.Date.FromCsv.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-from-csv/Axioms.lean
python3 -I scripts/parquet-date-from-csv-oracle/check.py
```

The oracle accepts `--pyarrow-path` and `--thrift-path` for separately
unpacked pinned wheels.
