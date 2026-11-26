# Checked Parquet DATE and Arrow Date32 IPC named imports

`Silmaril.Formats.Relational.NamedTable.Date32` imports either checked
one-column wire profile into the same named table type. The caller supplies the
destination key, exact field name, nullability, and the source reader's limits.
The single field uses the existing `Parquet.Date.Events.Kind.date32 nullable`.
Every row holds one nullable signed Int32 count of days since 1970-01-01.

- `importParquet` consumes `Parquet.Date.Events.readAll` in footer group order.
  It retains the checked DATE name, required or optional repetition, and signed
  INT32 slots. The [Parquet reader profile](parquet-date-events.md) defines
  supported annotations, pages, and limits.
- `importIpc` consumes `Arrow.DateStream.read` through exact EOS and admits its
  single little-endian Date32 field. It uses the Date32 inverse for the reader's
  civil observations, retaining each validity bit and signed 32-bit word,
  including both endpoints. The [Arrow reader profile](arrow-date-stream.md)
  defines the V5 framing and limits. A completed Date64 read is rejected.

The shared named insertion gate requires a vacant destination and exact
descriptor on successful exhaustion. A name conflict takes precedence over
source errors. At a vacant name, a late group or batch failure returns the
original zero-based index and cause without returning a database. Schema
mismatches are reported for completed reads. Imports materialize the ordered
rows in memory. The contract covers these two wire profiles and the full signed
Date32 domain, independently of calendar CSV text or Date64 narrowing.

The public `importParquet_ok_iff` and `importIpc_ok_iff` laws characterize
success and the exact database update. `imports_equal_of_rows` proves that
exhausted sources with matching descriptors and equal ordered rows give
the same named update across different group and batch boundaries.
`recover_wire_slot` and `read_date32_slots` connect the IPC validity and
value buffers to the recoverable Date32 observations. The indexed failure
laws are `importParquet_group_error` and `importIpc_batch_error`.
[Theorem header](../../Silmaril/Formats/Relational/NamedTable/Date32/Thms.lean)

CPython 3.13.5, PyArrow 26.0.1, and Apache Thrift 0.25.0 reproduce the
[fixture hashes](../../scripts/date32-named-import-oracle/check.py).
The Parquet pair reuses the [DATE producer and page edit](../../scripts/parquet-date-oracle/check.py).
The matching IPC has batch lengths `[4, 0, 3]`. Both sources carry both signed
endpoints, year zero, a leap day, and a null slot. The damaged Parquet file
fails at group 1. The truncated IPC keeps its first two complete batches and
fails at batch 2. The Lean driver also checks descriptor mismatches, an occupied
name, preservation of an existing entry, and Date64 rejection.

```sh
lake build --wfail +Silmaril.Formats.Relational.NamedTable.Date32.Checks
lake env lean -DwarningAsError=true Silmaril/Formats/Relational/NamedTable/Date32/Checks.lean
python3.13 scripts/date32-named-import-oracle/check.py
```
