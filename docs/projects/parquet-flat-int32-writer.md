# Complete one-row-group Parquet INT32 writer

`Silmaril.Formats.Parquet.FlatInt32Writer.emit` writes a complete plaintext
Parquet file for a nonempty ordered list of flat required or optional INT32
columns. The input carries one explicit row count. Column names must be
unique, and every column must have exactly that many slots. Zero rows are
admitted. The file has one row group and one uncompressed PLAIN V1 page
per column. It uses the existing page writer and the pinned Parquet format
and Thrift Compact profiles.
[Page writer](parquet-plain-v1-writer.md) · [Specification pins](arrow-parquet-coverage.md)

The caller bounds column count, file bytes, footer bytes and traversal,
and the existing page budgets. Page widths are measured before materializing
data. The Compact writer debits the remaining footer byte budget at each
write. The file length stays below the signed i64 boundary and the footer
length fits its four-byte unsigned word. Compact signed fields use the
existing checked integer encoder. The file layout is leading `PAR1`, adjacent
column chunks in schema order, one `FileMetaData` struct, the exact footer
length, and trailing `PAR1`.

`emit_layout` proves ordered rectangular input, exact typed footer recovery
and validation, the framing relation, and contiguous data coverage. The
writer checks the footer and page index through the existing readers.
`emit_columns` relates each declared column to its unique page frame across
that index and proves that `ScalarPage.decode` applied to its exact file
body slice recovers the original nullable slots in order. File-level
`FlatScan` composition is a follow-up to the scanner integration. Table,
CSV, Arrow adapters, multiple groups, other physical types, codecs and
encodings are separate.
[Theorem header](../../Silmaril/Formats/Parquet/FlatInt32Writer/Thms.lean)

The independent oracle reads the unmodified emitted files using the pinned
Apache Thrift Compact reader and PyArrow 26.0.1. It checks exact footer
consumption, declared column ranges, V1 headers and sizes, schema order,
nullability and observed values. The fixtures include an all-null column,
signed endpoints, a non-ASCII field name, a zero-row group, and a 15-column
schema that exercises long Compact list headers.
[Wheel hashes](../../tests/formats/arrow-ipc/requirements.txt) ·
[Thrift archive hash and setup](parquet-flat-page.md#independent-page-fixtures)

```sh
lake build --wfail +Silmaril.Formats.Parquet.FlatInt32Writer.Thms +Silmaril.Formats.Parquet.FlatInt32Writer.Examples
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.FlatInt32Writer.Examples'
lake env lean -DautoImplicit=false -DwarningAsError=true --run scripts/parquet-flat-int32-writer/Write.lean /tmp/flat-int32-files
python3 scripts/parquet-flat-int32-writer/PyArrowOracle.py /tmp/flat-int32-files
```
