# Typed CSV and named tables to complete Arrow IPC streams

`Silmaril.Formats.Arrow.FromCsv.Stream` exposes `emitCsv`, `emitCsvUtf8`, and
`emitNamed`. Each call checks the supplied field declaration and adapts the
source to one Int32/UTF-8 `Writer.BatchInput`. The stream writer receives the
original ordered field list, the batch with its explicit row count, and the
supplied `ObservationLimits`. A successful stream contains the schema, one
record batch, and modern EOS. A header-only CSV emits an empty batch. A
zero-column CSV with rows emits a batch with its positive row count.
[Physical adapter](csv-to-arrow-batch.md) · [Stream writer](arrow-ipc-stream.md#flatbuffers-and-stream-writer)

The ASCII and UTF-8 entry points use their existing typed CSV decoders and
cell codecs. The UTF-8 entry point retains valid non-ASCII label and value
bytes under the existing CSV wire rules. Named input uses the same packed
database observation regardless of its import path. Schema and required-null
checks come from the existing batch adapter. `EmitError.adapter` preserves
adapter errors and `EmitError.writer` preserves IPC errors, including the
writer's budget errors.
[Typed UTF-8 CSV profile](typed-utf8-csv.md)

`emitAdapted_ok_iff` and the three `*_preserves` laws identify the successful
`StreamWriter.emit` call, the exact declared fields, the source row count,
and the ordered nullable observation of its one input batch. The adapter and
writer error laws preserve the original error values. These are component
laws. The general whole-stream read/write theorem belongs to the stream
writer. Complete-stream readback is also exercised by the scoped examples
and an independent PyArrow reader.
[Theorem header](../../Silmaril/Formats/Arrow/FromCsv/Stream/Thms.lean)

```sh
lake build --wfail +Silmaril.Formats.Arrow.FromCsv.Stream.Thms +Silmaril.Formats.Arrow.FromCsv.Stream.Examples
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.FromCsv.Stream.Examples'
python3 -I scripts/csv-to-arrow-stream-oracle/verify.py /tmp/csv-ipc --extract-ascii
lake env lean -DautoImplicit=false -DwarningAsError=true --run scripts/csv-to-arrow-stream-oracle/Write.lean /tmp/csv-ipc
python3 -m pip install --require-hashes -r tests/formats/arrow-ipc/requirements.txt
python3 -I scripts/csv-to-arrow-stream-oracle/verify.py /tmp/csv-ipc
```

The oracle uses the Arrow project's pinned PyArrow 26.0.1 and NumPy 2.5.5
versions. It checks the original CPython ASCII fixture, an input with a
non-ASCII header and cells, a named table with repeated rows, a two-row
zero-column batch, and an empty batch. The checks compare field positions,
types, nullability, nullable cells, batch counts, and explicit row counts.
[Wheel hashes](../../tests/formats/arrow-ipc/requirements.txt) · [ASCII fixture provenance](arrow-ipc-to-csv.md)
