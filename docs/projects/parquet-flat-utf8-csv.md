# Flat Parquet bytes to a named UTF-8 CSV table

`Parquet.Snapshot.FlatInt32.ToCsv.convert db name expected limits bytes`
takes an immutable Parquet byte value and a caller-declared ordered INT32
schema. It reads the [checked flat Parquet profile](parquet-flat-arrow.md),
converts the resulting column labels to their UTF-8 bytes, and passes the
batches to the [generic typed event converter](event-stream-utf8-csv.md).
The ordered nullable cells and terminal outcome pass through unchanged.
The output uses the existing canonical signed Int32 codec and typed CSV's
null and present tags. [Entry point](../../Silmaril/Formats/Parquet/Snapshot/FlatInt32/ToCsv/Defs.lean)

Success returns the updated named database, exact UTF-8-labelled schema, and
complete CSV bytes together. The file must bind to the expected ordered
physical names and reach EOF. The destination must be vacant and the schema
and rows must be representable in the UTF-8 CSV profile. An occupied name
takes precedence over stream errors. A late page failure returns the indexed
input error, with no database or CSV value. Existing database entries are
immutable. [Proofs](../../Silmaril/Formats/Parquet/Snapshot/FlatInt32/ToCsv/Thms.lean)

The regression uses both [pinned PyArrow fixtures](parquet-flat-scan.md#independent-fixtures)
to check exact bytes, ordered nullable rows, destination insertion, and CSV
round-trip. The second-group corruption in the V2 fixture leaves the first
12 rows observable in the reader and yields only a typed error from the
converter. [Checks](../../Silmaril/Formats/Parquet/Snapshot/FlatInt32/ToCsv/Checks.lean)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv.Checks
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv.Checks +Silmaril.Formats.Csv.EventStream.Examples'
```
