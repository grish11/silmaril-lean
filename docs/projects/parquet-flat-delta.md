# Flat INT32 Parquet scan with PLAIN and DELTA_BINARY_PACKED

`Silmaril.Formats.Parquet.Snapshot.FlatInt32Delta.readAll limits schema bytes`
opens a bounded plaintext Parquet snapshot and emits complete Arrow batches
in footer order. `bind` can be supplied to the generic Snapshot reader to
pull groups on demand. Callers using the binder directly apply the file
byte cap before opening. Binding checks the ordered schema names even when
the file has no row groups. The physical schema supports flat required and
optional INT32 leaves. Logical annotations are outside this profile.

The scan checks the column path, physical type, count, encoding metadata,
codec, and checked chunk extent against the bound leaf and row group. It
accepts only uncompressed Data Page V1/V2. The checked page header's value
encoding must be advertised by its column. Raw tag 0 selects the checked
PLAIN INT32 reader and raw tag 5 selects the checked DELTA_BINARY_PACKED
INT32 reader. Both receive the exact original framed body. The scanner
preserves V1 RLE level tags and the V2 level sizes and resolved compression
flag. Scalar preparation and nullable reconstruction use the existing
[scalar][scalar] and [delta][delta] page contracts.

CRC-bearing pages, compressed columns, dictionary and index pages,
unsupported encodings, and deprecated V1 BIT_PACKED level tags are
rejected. The file, group, column, page and scalar limits bound the work.
Page admission and body failures carry the zero-based page ordinal and
absolute header offset. The Snapshot cursor adds the group ordinal, and
the scanner adds the column ordinal and bound field name. Framing runs
before body decoding in each column. A failed group emits no batch and
keeps the previously emitted batches.

`FlatScan.Delta.decodeFrame_ok_iff` characterizes the decoder chosen by the
original page tag on the original framed body and equates the entire ordered
slot list to that decoder's result. `FlatScan.Delta.decodeFrame_counts`
gives the exact slot count and the V2 present count. Existing checked
column assembly validates each page result and the column count, and
the Snapshot cursor checks the group count before publication.
[Theorems][thms]

The wire specification is Apache Parquet Format **2.14.0**, commit
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The fixture producer is
PyArrow **26.0.1**, Arrow commit `9e5d6978e9acf372cc989aaaf94e863fe8582c90`.
The independent header reader uses Apache Thrift **v0.25.0**, commit
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`.
[Thrift IDL][idl] · [Encodings][encodings] · [Producer and Thrift pins][pins]

The clean fixtures each contain three eight-row groups, a required PLAIN
column, and an optional delta column, with two pages in each column.
PyArrow checks the ordered rows. Thrift checks the page tags and chunk
windows. The damaged V2 file changes the delta scalar count at byte 336
from three to zero. PyArrow independently rejects group 1 and reads
groups 0 and 2. Lean emits group 0 and terminates with a typed delta count
mismatch at group 1, column 1 (`optional_i32`), page 1, header byte 307.
The regressions also exercise unsupported and unadvertised actual tags,
CRC and codec rejection, the scalar budget, and default PLAIN rejection.
[Regressions][checks] · [Oracle][oracle]

| Fixture | SHA-256 |
| --- | --- |
| `plain-delta-v1.parquet` | `cc784756239efd9671de83cf4c81af50fc76cc31c495ceb91e4a330df5f8ed46` |
| `plain-delta-v2.parquet` | `9446e4a75fb333c32a1ee1bb0e62e031f9cbaf595f444a098400a4381ed85cdc` |
| `plain-delta-v2-bad-count.parquet` | `a586f8bbe0d596463a71e9ea73ffcab6c8699906e1f321225abd80c9ce14f40d` |

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-flat-delta/Oracle.py "$fixture_tmp"
diff -r data/parquet-flat-delta "$fixture_tmp"
lake build --wfail +Silmaril.Formats.Parquet.Snapshot.FlatInt32Delta.Checks
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Snapshot.FlatInt32Delta.Checks +Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.CRCChecks +Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Examples parquet-flat-scan-regression'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-flat-delta/Axioms.lean
```

[scalar]: parquet-scalar-page.md#header-and-body-adapter
[delta]: parquet-delta-page.md
[thms]: ../../Silmaril/Formats/Parquet/FlatScan/Delta/Thms.lean
[checks]: ../../Silmaril/Formats/Parquet/Snapshot/FlatInt32Delta/Checks.lean
[oracle]: ../../scripts/parquet-flat-delta/Oracle.py
[idl]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift
[encodings]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md
[pins]: parquet-flat-page.md#independent-page-fixtures
