# Checked Arrow IPC files to flat Parquet

`Silmaril.Formats.Csv.ParquetIpc.FromFile.convert` takes an immutable
Arrow IPC file, a declared ordered nullable INT32 schema, explicit IPC
and Parquet limits, and a destination name in the typed database. It
uses `Arrow.FileReader.readRows` to admit the file and materialize every
footer-indexed batch. It passes those typed rows directly to the existing
stream conversion's named insertion and flat Parquet writer.

The destination must be vacant. The field order, exact names, INT32 types,
and nullable flags must match the declaration. The writer emits one flat
Parquet row group with OPTIONAL INT32 columns. A schema-only file produces an
empty row group. Empty batches contribute zero rows. The return value is
the exact one-key database update and the emitted Parquet bytes.

At a vacant destination, a file-reader error retains its original
`Arrow.Error` payload and there is no completed result. For example,
the fixture's damaged final record leaves the index and first two
records readable, and full conversion returns the body-length error.
The aggregate reader returns the original cause. Its indexed API also
identifies the affected record. The bridge uses the existing flat
little-endian IPC file and uncompressed PLAIN INT32 writer profiles.
[Flat IPC file reader](arrow-ipc-file.md) · [Shared stream bridge](arrow-ipc-to-parquet.md)

`FromFile.convert_readback` identifies the checked index, its exact
ordered batch observations, the named update, and a successful checked
Parquet scan with the same flattened nullable slots. The stream and file
entry points share the typed conversion and its readback proof through
`FromIpc.convertWithReader`. The file proof specializes that result using
`FileReader.readRows_indexed`.
[Theorem header](../../Silmaril/Formats/Csv/ParquetIpc/FromFile/Thms.lean)

The pinned CPython 3.13.5 and PyArrow 26.0.1 fixture pair covers a two-column
file with batch lengths `[2, 0, 3]`, signed endpoints, and nulls, and a
schema-only file. A length-field edit in the last record checks late failure.
PyArrow independently reads both emitted Parquet files and the good prefix
of the damaged input. Lean also checks exact ordered schema, preservation
of an existing name, and conflict precedence.
[Fixture hashes](../../scripts/arrow-file-to-parquet-oracle/pins.json)

```sh
lake build --wfail +Silmaril.Formats.Csv.ParquetIpc.FromFile.Checks +Silmaril.Formats.Csv.ParquetIpc.FromIpc.Checks
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Formats/Csv/ParquetIpc/FromFile/Checks.lean
python3.13 scripts/arrow-file-to-parquet-oracle/check.py --out /tmp/arrow-file-to-parquet
```
