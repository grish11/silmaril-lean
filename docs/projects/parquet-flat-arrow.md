# Flat PLAIN Parquet bytes as Arrow batches

`Parquet.Snapshot.FlatInt32.readAll` opens one immutable Parquet byte value
against a caller-declared, ordered `Scan.Schema String Unit`. Cells are
nullable `Int32` values. The open first validates the plaintext footer and
then checks the flat schema and its ordered column names. Its binder reuses
the [flat row-group assembler](parquet-flat-scan.md) and the
[PLAIN scalar page decoder](parquet-scalar-page.md) on the snapshot's same
bytes and each indexed row-group descriptor. Successful groups contribute one
Arrow batch in footer order. A bad group yields its ordinal and typed error
after the earlier batches. [Arrow adapter](../../Silmaril/Formats/Parquet/Snapshot/FlatInt32/Defs.lean)

The accepted profile is the intersection of the plaintext snapshot footer
checks and the row-group assembler's flat required and optional INT32,
uncompressed PLAIN V1/V2 profile. The values are physical INT32 cells, with
logical annotations left uninterpreted. The profile rejects compressed or
dictionary columns, nested or repeated leaves, and CRC-bearing pages. The
snapshot limits bound the footer. The group and scalar limits bound assembly
and page decoding.
The byte values and their lifetime follow the
[snapshot contract](parquet-snapshot.md).

## Hive scans

`Manifest.flatInt32SnapshotOpener` supplies the concrete decoder to the
existing manifest opener, using the original declared path to look up bytes.
`Manifest.scan` opens each reached declaration and stops after the first
failed file or group. Projection operates after row-group decoding, and
partition filtering sees the unprojected nullable virtual values.
[Hive adapter](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/FlatInt32/Defs.lean)

`scanSnapshotsThenFilter` reads all reached files through the first
non-EOF outcome and then filters and projects. The strict scan has the same
ordered rows and terminal outcome, including the selected prefix after a
failure. Skip-open produces that same observation under
`SnapshotReachesEOF` for each rejected declaration. This premise observes
real standalone snapshot exhaustion under the same binder, including lookup,
open and every group read. A rejected file that opens and later fails can
distinguish the two scan policies. [Composition laws](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Scan/Thms.lean)

## Fixtures and checks

The existing PyArrow 26.0.1 V1 and V2 files provide two row groups each,
including required values and nullable cells. The checks run both full Arrow
reads, then project and prune a manifest with multiple files, repeated
paths, and false and unknown partition results. Each all-clean declaration
independently reaches EOF through `Snapshot.readAll`.

The late-error regression changes byte 234, the first PageHeader byte of
the second V2 group, to the Compact STOP octet. The original footer remains
intact. The read preserves the first group and reports the second group's
header error. The Hive cases distinguish failure in a retained file from
failure hidden by skip-open in a rejected file. The fixture hashes, producer
recipe and independently checked page spans are in the
[row-group fixture guide](parquet-flat-scan.md#independent-fixtures).
[Lean checks](../../Silmaril/Formats/Parquet/Snapshot/FlatInt32/Checks.lean)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Snapshot.FlatInt32.Checks
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Snapshot.FlatInt32.Checks parquet-flat-scan-regression'
```
