# Checked Date32 IPC batches to Parquet DATE row groups

`Parquet.Date.FromIpc.Multi.convert` reads a complete little-endian Arrow
IPC V5 stream with one Date32 field and one or more explicit record
batches. It writes a single required or optional INT32 DATE leaf and one
uncompressed PLAIN V1 row group per input batch, in order. Every empty
batch has a zero-row group and a chunk containing a real data page header.
A schema-only Date32 stream gives `.source (.batchCount 0)`. The original
UTF-8 name, nullable signed epoch-day slots, and batch boundaries are
preserved.
[Checked IPC reader](arrow-date-stream.md)
· [Single-batch converter](arrow-date32-to-parquet.md)
· [Executable API](../../Silmaril/Formats/Parquet/Date/FromIpc/Multi/Defs.lean)

The same Compact encoder serializes the group list for both writer
profiles. It sums the group row counts for the footer's total and writes
modern DATE plus matching ConvertedType 6 once in the schema. The
existing single-batch and primitive entry points retain their emitted
layout.
[Parquet 2.14.0 Thrift IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)
· [DATE semantics](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#date)
· [PLAIN V1 writer](parquet-plain-v1-writer.md)

The source must reach exact EOS before unit, count and output checks.
Aggregate preflight bounds physical groups, including empties, total
rows, and the Compact collection and schema sizes. It measures each
page's header and body before allocating page bodies. The remaining file
budget, after magic words, measured pages and the footer-length word,
caps the actual Compact footer serialization. The footer and file also
have their absolute 32-bit unsigned and 63-bit positive extent bounds.
Assembly verifies the actual page lengths against the plan.

The converter opens the written file once with the existing DATE binder
and reads the retained snapshot in footer order. It returns the complete
in-memory file after the descriptor, annotations, group count, total
rows, and every group's count and slots agree. A late source failure
retains the original Arrow error and index, and a failed group readback
returns the corresponding Parquet index and cause. A typed failure
contains no completed file.

`budget_exact`, `placements_at`, `preflight_exact` and `emit_extent`
connect the admitted limits, positive contiguous page spans, measured
sizes, and materialized file length. `convert_readback` identifies the source through
EOS and the single checked output snapshot. `readback_at` gives the exact
ordered nullable signed words for any admitted batch index.
`convert_readError` and `convert_noBatches` fix the source-error precedence
and the schema-only result.
[Theorem header](../../Silmaril/Formats/Parquet/Date/FromIpc/Multi/Thms.lean)

## Independent verification

CPython 3.13.5 and PyArrow 26.0.1 generate three IPC streams, with an empty
middle batch, required empty leading and trailing batches, and fifteen
explicit empty batches. The last case exercises Compact's long group-list
header. PyArrow reads each native Lean output group independently, comparing
the schema, group count, total rows, and nullable signed Int32 words.
Thrift 0.25.0 checks the DATE annotations and the exact PLAIN V1 page headers,
body bytes, and contiguous chunk extents. PyArrow reads the two complete
batches before rejecting a truncated final body. The Lean controls use those same
inputs and two truncated variants to check the original late source error,
late group readback, schema-only refusal, an all-empty group cap, an
aggregate row cap above each individual group size, and the exact whole-file
cap versus a one-byte-short cap.
[Fixture and tool hashes](../../scripts/date32-ipc-to-parquet-groups-oracle/fixtures.json)
· [Independent oracle](../../scripts/date32-ipc-to-parquet-groups-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.FromIpc.Multi.Thms +Silmaril.Formats.Parquet.Date.FromIpc.Multi.Tests +Silmaril.Formats.Parquet.Date.FromIpc.Thms +Silmaril.Formats.Parquet.Date.FromIpc.Tests +Silmaril.Formats.Parquet.FlatInt32Writer.Thms +Silmaril.Formats.Parquet.FlatInt32Writer.Examples +Silmaril.Formats.Parquet.Date.Events.ToIpc.Tests parquet-flat-scan-regression parquet-page-regression arrow_ipc_metadata_tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/date32-ipc-to-parquet-groups/Axioms.lean
python3 -I scripts/date32-ipc-to-parquet-groups-oracle/check.py
```

Use `--pyarrow-path` and `--thrift-path` for separately unpacked pinned wheels.
