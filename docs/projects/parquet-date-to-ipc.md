# Checked Parquet DATE to Arrow Date32 IPC

`Parquet.Date.Events.ToIpc.convert` reads one checked Parquet DATE snapshot
through the existing typed event source and writes a complete, single-field,
little-endian Arrow Date32 IPC V5 stream. It retains the exact UTF-8 field
name and declared nullability. Each completed source row group becomes one
record batch with the original signed Int32 epoch-day words, nulls and slot
order. `emit` also accepts the existing typed event trace and retains empty
batches as explicit zero-row records. Input admission and its default CRC
policy follow the DATE event source. Output admission follows the writer's
observation and IPC budgets.
[DATE binding and pinned Parquet spec](parquet-date-binding.md)
· [DATE events](parquet-date-events.md)
· [Date32 writer and pinned Arrow spec](arrow-date32-writer.md)
· [Executable API](../../Silmaril/Formats/Parquet/Date/Events/ToIpc/Defs.lean)

Source open, read and close failures keep their original typed cause. A group
error keeps the original zero-based index and underlying scanner error.
The source must reach EOF before the writer is called, so a late source
failure takes precedence over an exhausted writer budget. Result bytes are
available only after successful emission and checked readback. The input
and its event trace are held in memory. It returns the complete stream as one
byte buffer. This profile is limited to Date32 with the original epoch-day
scale.

`convert_readback` connects every returned stream to an EOF-terminated
source trace with its exact schema and ordered nullable batches.
`convert_openError` and `convert_readError` give the precise failure result,
including the same late cause when earlier batches were complete.
[Theorem header](../../Silmaril/Formats/Parquet/Date/Events/ToIpc/Thms.lean)

## Verification

CPython 3.13.5 and PyArrow 26.0.1 generate two pinned, two-group Parquet files
and reference IPC streams. PyArrow checks the input DATE annotation and reads
the actual IPC output emitted by Lean. The cases cover an optional and a
required field, the name `日付`, both signed Int32 endpoints, pre-epoch dates,
epoch day zero, leap day and an optional null. The physical check independently
decodes the IPC field node and buffers and compares the little-endian words,
validity bits and padding.

The damaged input reuses the pinned Apache Thrift 0.25.0 edit of the second
group's PLAIN encoding to RLE_DICTIONARY. PyArrow reads the first group and
rejects the second. Lean checks the retained prefix and confirms that conversion
returns only the original indexed error, even with a zero output batch budget.
Native synthetic traces cover an empty middle batch, a schema-only stream,
a null in a required field, and early close.
[Hashes](../../scripts/parquet-date-to-ipc-oracle/fixtures.json)
· [Oracle](../../scripts/parquet-date-to-ipc-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.Events.ToIpc.Thms +Silmaril.Formats.Parquet.Date.Events.ToIpc.Tests +Silmaril.Formats.Parquet.Date.Events.Thms +Silmaril.Formats.Parquet.Date.Events.Tests +Silmaril.Formats.Arrow.DateStream.Writer.Tests parquet-flat-scan-regression arrow_ipc_metadata_tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-to-ipc/Axioms.lean
python3 -I scripts/parquet-date-to-ipc-oracle/check.py
```

Use `--pyarrow-path` and `--thrift-path` for separately unpacked pinned wheels.
