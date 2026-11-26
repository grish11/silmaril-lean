# Arrow IPC streams through a named table to UTF-8 CSV

`Silmaril.Formats.Arrow.ToCsv.Utf8.convert` uses the existing checked Arrow
IPC byte reader, ordered schema translation, and EOS-only named insertion.
It exports the table with `Csv.NamedTable.Utf8.exportCsv` and returns the
updated database, ordered schema, and CSV bytes together on success. The
caller supplies the expected schema and observation limits. Other named
entries are preserved by the existing packed update. A malformed stream or
an unrepresentable CSV field returns an error without a database result.
[IPC reader contract](arrow-ipc-stream.md) · [Typed UTF-8 CSV](typed-utf8-csv.md) ·
[Named UTF-8 CSV](named-utf8-csv.md)

The reader profile is a finite little-endian flat Arrow IPC V5 stream with
Int32 and UTF-8 fields and modern EOS. Multiple batches flatten in input
order, including empty batches. Field names keep their exact UTF-8 bytes;
position, kind, and nullability remain in the returned schema. Null and
present empty text have distinct typed CSV tags. The UTF-8 wire profile
still rejects disallowed ASCII control bytes, including tab and NUL.

`ToCsv.Utf8.convert_roundTrip` proves the exact named update and recovery of
flattened ordered Arrow rows when the checked source table can be encoded.
`convert_byteError` and `convert_encodeError` preserve those failure reasons.
`FromCsv.Stream.emitCsvUtf8_readback` composes the existing CSV adapter with
the stream writer's checked-reader law. Successful emission recovers the
exact declared fields and nullable cells in order under the same limits,
plus the explicit record-batch row count even when there are no columns.
The reverse bridge emits the decoded table in one batch.
[Forward theorems](../../Silmaril/Formats/Arrow/ToCsv/Utf8/Thms.lean) ·
[Reverse theorems](../../Silmaril/Formats/Arrow/FromCsv/Stream/Thms.lean)

The scoped examples check a multi-batch stream, late truncation, trailing
bytes, schema and name conflicts, a CSV wire encoding error, and a positive
row count at zero columns. The independent oracle reads the existing pinned
PyArrow fixture with batch sizes `[4, 0, 1, 1]`, generates canonical UTF-8
CSV with CPython's `csv.writer`, and compares exact bytes. PyArrow also reads
the re-emitted IPC and checks all six rows in order.
[Fixture provenance](../../tests/formats/arrow-ipc/fixture.json)

```sh
lake build --wfail +Silmaril.Formats.Arrow.ToCsv.Utf8.Examples +Silmaril.Formats.Arrow.FromCsv.Stream.Examples
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.ToCsv.Utf8.Examples +Silmaril.Formats.Arrow.FromCsv.Stream.Examples'
lake env lean -DautoImplicit=false -DwarningAsError=true --run scripts/arrow-to-csv-utf8-oracle/Read.lean tests/formats/arrow-ipc/nullable-int32-utf8.arrows /tmp/utf8.csv /tmp/utf8.arrows
python3 -m pip install --require-hashes -r tests/formats/arrow-ipc/requirements.txt
python3 -I scripts/arrow-to-csv-utf8-oracle/verify.py /tmp/utf8.csv /tmp/utf8.arrows
```
