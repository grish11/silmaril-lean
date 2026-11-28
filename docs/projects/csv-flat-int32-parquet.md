# Typed UTF-8 CSV to flat INT32 Parquet

`Parquet.FlatInt32Writer.FromCsv.convert db name schema csvLimits parquetLimits wire`
uses the declared ordered INT32 schema to decode a complete typed UTF-8 CSV
table. The header must match the schema's UTF-8 field names in order. A null
field uses the typed tag `N`. A present field uses `T` followed by a canonical
signed Int32 decimal. An empty field, a bare number, and `T` without a number
are rejected. The caller supplies the schema and type.
[Typed UTF-8 CSV](typed-utf8-csv.md) ·
[Entry point](../../Silmaril/Formats/Parquet/FlatInt32Writer/FromCsv/Defs.lean)

CSV limits bound wire bytes and declared columns before decoding, then
decoded data rows before writing. The Parquet writer enforces separate
column, file, footer, header and page limits. The writer accepts zero rows
with a nonempty, distinct ordered column schema. This adapter emits every
column as OPTIONAL, retaining null and present slots in their original order.
The file contains one row group and one uncompressed PLAIN V1 page per column.
[Writer profile](parquet-flat-int32-writer.md)

Success returns the named database update and complete Parquet bytes
together. An occupied name takes precedence. CSV, naming or writer
failures return an error without a database update or bytes. The input
database is immutable. `convert_readback` uses the writer-to-scanner
theorem to identify the exact row count, ordered fields and nullable values
observed from the emitted bytes. [Theorems](../../Silmaril/Formats/Parquet/FlatInt32Writer/FromCsv/Thms.lean)

The checks cover Unicode field names, signed endpoints, null and zero,
a header-only table, name conflicts, mismatched headers, ambiguous fields
and separate resource limits. Both existing V1/V2 fixtures round-trip
through the typed CSV bridge and the checked writer, with exact slot order.
[Fixture provenance](parquet-flat-scan.md#independent-fixtures) ·
[Regression checks](../../Silmaril/Formats/Parquet/FlatInt32Writer/FromCsv/Checks.lean)

```sh
lake build --wfail +Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv.Checks
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv.Checks parquet-flat-scan-regression'
```
