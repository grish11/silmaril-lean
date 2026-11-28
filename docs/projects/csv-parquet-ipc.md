# Typed CSV through Parquet and Arrow IPC

`Silmaril.Formats.Csv.ParquetIpc.convert` takes a vacant table name, a
declared ordered schema, UTF-8 CSV bytes, and separate CSV, Parquet writer,
snapshot, and IPC limits. It writes a flat INT32 Parquet file, opens and reads
that immutable snapshot through EOS, exports the named table as typed UTF-8
CSV, and writes a complete Arrow IPC stream from that export. It returns
the named update and all three wire results together on success.
[Entry point](../../Silmaril/Formats/Csv/ParquetIpc/Defs.lean)

The common profile has a nonempty schema of distinct names. Every column is
Parquet OPTIONAL and Arrow nullable signed INT32, in the declared order.
The UTF-8 CSV uses `N` for null and `T` plus canonical Int32 decimal for
present values. A header-only input produces a zero-row Parquet group and
one zero-row IPC batch. The CSV byte and declared column caps are checked
before parsing. The decoded row cap is checked after parsing the complete
input. The remaining limits apply at the writer, checked snapshot, and
little-endian IPC V5 stages.
[CSV and Parquet profile](csv-flat-int32-parquet.md) ·
[Snapshot export](parquet-flat-utf8-csv.md) ·
[IPC writer profile](arrow-ipc-stream.md)

`convert_of_admitted` proves completion if the CSV-to-Parquet call succeeds,
the snapshot limits match the writer's `Limits.snapshotLimits` for the decoded
table dimensions, and the original CSV is admitted by the IPC emitter under
the declared fields and IPC limits. The proof obtains a successful UTF-8
re-encoding from the successful source decode and reuses the IPC admission
for that typed table. `convert_readback` proves the ordered schema and
nullable rows agree through snapshot EOS, CSV decoding, and IPC readback
under the same reader-limit condition. It also identifies the exact update
at the requested name. The equality is over the decoded observations.

Errors retain the first stage and its original cause. An occupied name
takes precedence at CSV-to-Parquet entry. Snapshot read and CSV export errors
are tagged with `exportCsv`, preserving the indexed read cause where present.
IPC admission and writing errors are tagged with `writeIpc`. All failures
return the error alone. Both named operations check the original immutable
database, and the result updates only the requested name.
[Public theorems](../../Silmaril/Formats/Csv/ParquetIpc/Thms.lean)

The checks exercise a two-column zero-row table, mixed nulls and signed
endpoints, occupied names, an out-of-order header, a snapshot read limit,
and an IPC budget failure.
[Lean checks](../../Silmaril/Formats/Csv/ParquetIpc/Checks.lean)

```sh
lake build --wfail +Silmaril.Formats.Csv.ParquetIpc.Checks
make check CHECK_TARGETS='+Silmaril.Formats.Csv.ParquetIpc.Checks +Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv.Checks'
```
