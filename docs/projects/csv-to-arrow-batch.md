# Typed CSV and named rows to an Arrow physical batch

`Silmaril.Formats.Arrow.FromCsv.ofCsv` decodes the existing tagged typed CSV
profile using a caller-declared list of Arrow Int32 and UTF-8 fields. It checks
the exact ordered header and uses the concrete CSV cell codecs. `ofNamed`
reads the named database observation and checks its ordered labels, kinds and
nullability against the same declaration. `ofRows` accepts rows already indexed
by the declared schema, including rows from another typed CSV decoder.
[Typed CSV](typed-csv.md) · [CSV cell codecs](csv-cell-codecs.md) ·
[Shared field translation](arrow-ipc-to-csv.md)

The adapter uses the existing aligned transpose. It retains the declared field
names and nullability, records the source row count even with zero fields, and
rejects a null in any required column. The row input can carry arbitrary Lean
strings. The byte input obeys the existing typed CSV ASCII wire profile.

`ofRows_preserves`, `ofCsv_preserves`, and `ofNamed_preserves` recover the exact
ordered nullable row observation, declared fields and source row count for
successful adapters. `emitBatch_roundTrip` composes this with the existing
physical writer and proves that a successfully emitted batch decodes to the
same rows and count. The writer checks physical layout, offsets and configured
budgets when called. The interface produces one `Writer.BatchInput`, for a
physical body and metadata AST when emitted. Complete stream framing and EOS
writing are separate.
[Physical writer](arrow-ipc-stream.md#physical-batch-writer)

```sh
lake build --wfail +Silmaril.Formats.Arrow.FromCsv.Thms +Silmaril.Formats.Arrow.FromCsv.Examples
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.FromCsv.Examples'
```

The examples write and read the batch formed from the pinned CPython fixture,
exercise a two-row zero-column batch, and check repeated non-ASCII text from a
named table. Errors distinguish a missing name, conflicting schema, reordered
CSV header, and a required null.
