# Checked Arrow Date32 IPC to one Parquet DATE row group

`Parquet.Date.FromIpc.convert` admits a complete little-endian Arrow IPC V5
stream through the existing DATE reader and its explicit EOS check. It
requires one flat Date32 field and exactly one record batch. A schema-only
stream reports a batch count of zero. One zero-row batch produces a real,
readable zero-row group. The file retains the field's UTF-8 name, required
or optional declaration, and signed nullable epoch-day words. Its only
column has one uncompressed PLAIN V1 data page.
[DATE stream admission](arrow-date-stream.md)
· [Executable API](../../Silmaril/Formats/Parquet/Date/FromIpc/Defs.lean)

The footer uses physical INT32, modern LogicalType DATE and matching
legacy ConvertedType DATE (code 6). The modern field is SchemaElement
field 10, with sole union member 6 and an empty DateType payload. The
annotation shares the existing bounded Compact serializer and rectangular
INT32 file assembly. The typed footer projection is unchanged. The DATE
binder checks the original annotation bytes during readback. Existing
primitive entry points select the unannotated footer.
[Parquet 2.14.0 IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)
· [DATE semantics](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#date)
· [Primitive writer](parquet-flat-int32-writer.md)
· [Checked DATE reader](parquet-date-binding.md)

Source errors retain their exact cause and precede all output checks.
After EOF, unit admission precedes batch-count admission. The profile
keeps the original day scale and covers only Date32. The writer and
readback have independent caller-supplied limits. Conversion returns a
complete in-memory file only after the existing DATE reader recovers the
one matching group. A checked conversion error carries no output bytes.

`convert_readback` gives exact source admission and the checked output
snapshot and group, with one group, the original descriptor, matching
annotation, count and ordered nullable dates. `Matches.exactWords` recovers
the exact signed Int32 slots from that observation. `convert_readError`,
`convert_wrongUnit` and `convert_batchCount` fix the error results independently
of output limits.
[Public theorem header](../../Silmaril/Formats/Parquet/Date/FromIpc/Thms.lean)

## Independent checks

CPython 3.13.5 and PyArrow 26.0.1 generate four admitted IPC streams. PyArrow
reads the native files emitted by Lean and checks the schema, group count and
ordered nullable Date32 words. The tests read the signed words via an Int32
view, covering both endpoints and dates beyond the Python `datetime.date`
range. There are separate required and optional empty-batch cases. Apache
Thrift 0.25.0 checks both raw DATE annotations, the actual V1 page header,
the level bytes, and the exact packed INT32 words. The oracle also pins
schema-only, two-batch, missing-EOS, Date64, fractional Date64, two-field and
required-null controls and checks their exact Lean errors.
[Fixture and wheel hashes](../../scripts/arrow-date32-to-parquet-oracle/fixtures.json)
· [Producer and oracle](../../scripts/arrow-date32-to-parquet-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.FromIpc.Thms +Silmaril.Formats.Parquet.Date.FromIpc.Tests +Silmaril.Formats.Parquet.FlatInt32Writer.Thms +Silmaril.Formats.Parquet.FlatInt32Writer.Examples +Silmaril.Formats.Parquet.Date.Events.Tests +Silmaril.Formats.Parquet.Date.Events.ToIpc.Tests +Silmaril.Formats.Arrow.DateStream.Tests parquet-flat-scan-regression parquet-page-regression arrow_ipc_metadata_tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/arrow-date32-to-parquet/Axioms.lean
python3 -I scripts/arrow-date32-to-parquet-oracle/check.py
```

Use `--pyarrow-path` and `--thrift-path` for separately unpacked pinned wheels.
