# Arrow IPC to flat INT32 Parquet

`Silmaril.Formats.Csv.ParquetIpc.FromIpc.convert` accepts an immutable IPC byte
stream, an ordered schema, a named INT32 table database, a vacant destination,
and separate IPC observation and Parquet writer limits. It runs the existing
IPC reader through explicit EOS, checks the full field declaration, and uses
`Arrow.ToCsv.typedRows` to recover the typed rows. The handoff to
`FlatInt32Writer.FromCsv.convertRows` carries typed nullable cells in memory.
[Entry point](../../Silmaril/Formats/Csv/ParquetIpc/FromIpc/Defs.lean) ·
[IPC reader profile](arrow-ipc-stream.md) ·
[Flat writer profile](parquet-flat-int32-writer.md)

The shared schema has a nonempty ordered list of distinct field names. All IPC
fields must be nullable signed INT32, with exact names and positions. The
writer emits OPTIONAL fields in that order, in one uncompressed PLAIN V1
row group. It preserves the flattened order of rows from all IPC batches.
An empty batch contributes zero rows, and a zero-row IPC stream can produce
a zero-row Parquet group. The IPC reader applies its byte, field, batch, row,
and cell limits. Parquet writing applies its independent limits.

The adapter checks name occupancy first. Success returns the exact named
update and complete Parquet bytes together. At a vacant destination, late
truncation and missing EOS propagate the existing IPC input error, including
its original payload. Schema and writer failures return their respective
errors. `convert_readback` identifies the input observation, named update,
output schema, row count, and every nullable slot. `convert_read_error`
specifies the complete failed result.
[Public laws](../../Silmaril/Formats/Csv/ParquetIpc/FromIpc/Thms.lean)

The two-column IPC fixtures come from PyArrow 26.0.1, with batch sizes
`[2, 0, 1]` and `[0]`. The nonempty fixture includes null, zero, and both
signed endpoints. PyArrow locates byte 784 at the end of its final data
batch. The Lean regressions cut at 783 for late body truncation and at 784
for missing EOS. The oracle pins the exact input hashes and checks the
emitted Parquet schema, row count, and cells independently.
[Fixture and oracle](../../tests/formats/arrow-ipc-to-parquet/check.py) ·
[Pinned wheel requirements](../../tests/formats/arrow-ipc/requirements.txt) ·
[Lean checks](../../Silmaril/Formats/Csv/ParquetIpc/FromIpc/Checks.lean)

```sh
lake build --wfail +Silmaril.Formats.Csv.ParquetIpc.FromIpc.Checks
make check CHECK_TARGETS='+Silmaril.Formats.Csv.ParquetIpc.FromIpc.Checks +Silmaril.Formats.Csv.ParquetIpc.Checks +Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv.Checks'
python3 -m pip install --require-hashes -r tests/formats/arrow-ipc/requirements.txt
mkdir -p /tmp/silmaril-ipc-parquet
for name in multi-batch zero-rows; do
  lake env lean -DwarningAsError=true --run tools/arrow-ipc-to-parquet/Emit.lean \
    "tests/formats/arrow-ipc-to-parquet/$name.arrows" "/tmp/silmaril-ipc-parquet/$name.parquet"
done
python3 -I tests/formats/arrow-ipc-to-parquet/check.py --parquet-dir /tmp/silmaril-ipc-parquet
```
