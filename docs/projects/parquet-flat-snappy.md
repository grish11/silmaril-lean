# Snappy flat PLAIN INT32 Parquet scan

`Silmaril.Formats.Parquet.Snapshot.FlatInt32Snappy.readAll limits schema bytes`
opens a bounded plaintext Parquet snapshot and emits complete Arrow batches
in footer order. `bind` supplies the same profile to the checked Snapshot
reader for on-demand groups. Callers using the binder directly enforce the
file byte cap before opening. The schema supports flat required and optional
physical INT32 leaves with the caller's ordered column names.

The column scan checks the matched path, physical type, row count, PLAIN
encoding profile, codec **SNAPPY (1)**, and local chunk extent. It frames
the chunk on the immutable file and checks the page kind, CRC policy,
and both declared size caps before extracting the original on-disk
body. The physical reader admits PLAIN Data Page V1 with RLE level
tags and Data Page V2 with checked flat level extents. It rejects
CRC-bearing pages, dictionary and index pages, deprecated V1 BIT_PACKED
levels, and any other column codec or value encoding. Logical annotation
interpretation is outside the profile.

- **V1** passes the entire on-disk body to the bounded raw Snappy reader.
  ScalarPage checks the expanded size and splits optional definitions
  from the PLAIN values after decompression.
- **V2** checks the uncompressed definition prefix, including its extent
  within both declared sizes. It subtracts that prefix from both sizes and
  uses the resolved `is_compressed` flag to decode only the value suffix.
  True, including the Parquet default for an omitted flag, selects Snappy.
  False selects the raw value body with exact size checks, even though
  the column declares Snappy.

The [scalar page contract][scalar] accounts for the compressed and expanded
extents. The codec checks the exact input extent before dispatch and bounds
expansion to the declared size. The scalar decoder reconstructs nulls and
values in page order. Snapshot publishes a group only after every column
and row check succeeds. Page admission and decode errors carry their zero-based
group, column, and page ordinals, the bound column name, and the absolute
header offset. A failed group leaves earlier complete batches available.

`FlatScan.Snappy.scanColumn_framed` proves the admitted codec and the
original `Page.readChunk` equation for a successful column scan.
`FlatScan.Snappy.decodeFrame_wire` binds the page adapter to its exact
framed input and the header's original scalar parameters with codec 1.
It exposes `ScalarPage.PreparedWire`, the exact mask and ordered PLAIN
values, the slot count, and the V2 present count.
[Theorem header][thms] · [Raw Snappy][snappy]

## Independent fixtures

The specification is Apache Parquet Format **2.14.0**, commit
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The codec is raw Snappy 1.2.2,
commit `6af9287fbdb913f0794d0148c6aa43b58e63c8e3`. PyArrow **26.0.1**
(Arrow commit `9e5d6978e9acf372cc989aaaf94e863fe8582c90`) writes the files.
Apache Thrift **v0.25.0**, commit `27e8a425ffb498e190df3a12e239326bf5ba9ed6`,
independently reads the page header extents, level lengths, and flags.
[IDL][idl] · [Compression][compression] · [Producer package pins][pins]

Each clean file has three 32-row groups, one required and one nullable
column, and two pages per column and group. The oracle checks ordered
PyArrow readback and checks the codec-covered slices independently against
the PLAIN words. Eight V2 pages have compressed values and four have raw
values in their Snappy column. Each damaged file increases the Snappy
output size at group 1, column 1, page 1 by one byte. PyArrow independently
rejects group 1. The scanner emits precisely group 0 and then reports
`Payload.Error.outputSizeMismatch` through the scalar adapter.

| Fixture | SHA-256 |
| --- | --- |
| `snappy-plain-v1.parquet` | `61dc65ee47db5a9d286cf73202bd4a6e75e2f176cdb23f0ddf0125a49e682751` |
| `snappy-plain-v1-bad-size.parquet` | `9365742c19acf32a484b449cb62942a1223e59cf26b0ba0b7830ff4c49c7af4b` |
| `snappy-plain-v2.parquet` | `a48aa8e71f262b4c1a9e32e22d097a018cf41e5c870cc1097cb7511bbe0af785` |
| `snappy-plain-v2-bad-size.parquet` | `9a3ec7cb4c361b94f48ea98878b5765123fbd6097d1fd07f357aaa2325304356` |

The mutated V1 body begins at file byte 320, with header at 301. The
mutated V2 suffix begins at file byte 347, after the three raw definition
bytes, with header at 320. The Lean regressions also check a wrong declared
raw V2 suffix size, separate compressed and output budgets, the scanner page
cap, unsupported tags and codecs, and an explicit CRC.
[Regressions][checks] · [Oracle][oracle]

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-flat-snappy/Oracle.py "$fixture_tmp"
diff -r data/parquet-flat-snappy "$fixture_tmp"
lake build --wfail +Silmaril.Formats.Parquet.Snapshot.FlatInt32Snappy.Checks
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Snapshot.FlatInt32Snappy.Checks +Silmaril.Formats.Parquet.Snapshot.FlatInt32Delta.Checks +Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.CRCChecks +Silmaril.Formats.Parquet.Date.Tests parquet-flat-scan-regression'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-flat-snappy/Axioms.lean
```

[scalar]: parquet-scalar-page.md
[thms]: ../../Silmaril/Formats/Parquet/FlatScan/Snappy/Thms.lean
[snappy]: parquet-raw-snappy.md
[checks]: ../../Silmaril/Formats/Parquet/Snapshot/FlatInt32Snappy/Checks.lean
[oracle]: ../../scripts/parquet-flat-snappy/Oracle.py
[idl]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift
[compression]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Compression.md
[pins]: parquet-flat-page.md#independent-page-fixtures
