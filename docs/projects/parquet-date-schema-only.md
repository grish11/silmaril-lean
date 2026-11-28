# Opt-in schema-only Date32 IPC to Parquet DATE

`Parquet.Date.FromIpc.SchemaOnly.convert` admits one Date32 field through
the existing checked little-endian IPC V5 reader and exact EOS. It
requires zero explicit record batches. One explicit zero-row batch gives
`batchCount 1`. A Date64 schema gives the unit error. Original IPC reader
errors take precedence over shape and output checks. The regular
multibatch converter continues to return its zero-batch refusal.
[Executable API](../../Silmaril/Formats/Parquet/Date/FromIpc/SchemaOnly/Defs.lean)
· [Multibatch admission](date32-ipc-to-parquet-groups.md)

The pinned Parquet IDL requires `FileMetaData.num_rows` and
`row_groups : list<RowGroup>` and specifies no positive list minimum.
The file layout places the metadata after the chunks, which gives a
footer at byte four when there are zero groups. PyArrow 26.0.1 produces this
shape when a Parquet writer is closed immediately after declaring the
schema. The checked DATE reader accepts those files.
[Parquet 2.14.0 `FileMetaData` IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L1407-L1430)
· [Pinned file layout](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md#file-format)

The bridge reuses the bounded Compact group-list serializer with zero
groups. It writes version 1, root plus one required or optional INT32
leaf, modern DATE and converted type 6, `num_rows = 0`, and an empty
`row_groups` list. The byte layout is leading PAR1, Compact metadata,
its unsigned 32-bit little-endian length, and trailing PAR1. The writer
bounds the schema collection and name lengths and gives the footer
the remaining whole-file budget after the 12 framing bytes. It checks
the emitted file with the existing DATE binder and exact descriptor
and count checks before releasing bytes.
[DATE admission](parquet-date-binding.md)
· [Checked logical observation](date-roundtrip.md)

`encode_extent` proves the exact framing, bounded byte length and
empty group-list serializer input. `convert_readback` ties the original
Date32 declaration to the checked output with zero rows and zero groups,
the same logical observation, and a typed DATE EOF trace with zero batches.
`convert_nonempty` and `convert_readError` fix the refusal results.
[Public theorem header](../../Silmaril/Formats/Parquet/Date/FromIpc/SchemaOnly/Thms.lean)

## Native IPC and round trips

`Date.Events.ToIpc.convert` already emits a native Date32 schema followed by
EOS when the checked Parquet footer has zero groups. `zero_group_readback`
gives the exact field name, nullability and DAY unit, with an empty batch
list. One explicit zero-row IPC record has a singleton batch list and
is refused by `SchemaOnly.convert_nonempty` with `batchCount 1`.

The opt-in `RoundTrip.SchemaOnly.ipc_roundtrip` and `parquet_roundtrip`
compose the landed readback contracts. Both legs must succeed and their
limits agree on the intermediate file or stream. The former uses the same
`Date.Limits` at the Parquet boundary. The latter reads with the native
IPC writer's `ObservationLimits.ipc`. The result is the full same logical
descriptor with zero explicit batches. Both Parquet observations in
`parquet_roundtrip` have zero checked footer groups by `parquet_at`.
[Schema-only round-trip theorems](../../Silmaril/Formats/Parquet/Date/RoundTrip/SchemaOnly/Thms.lean)
· [Shared observation laws](../../Silmaril/Formats/Parquet/Date/RoundTrip/Thms.lean)

## Pinned verification

CPython 3.13.5 and PyArrow 26.0.1 produce two genuine zero-group Parquet
files and two schema-only IPC streams with required and optional Unicode
field names. Lean converts both PyArrow Parquet inputs to schema-only IPC
through the existing forward path and feeds those streams to the new
bridge. PyArrow reads all four Lean-emitted files. Apache Thrift 0.25.0
checks exact footer consumption, the empty typed row-group list, both
annotations, zero rows and placement immediately after PAR1. The controls
cover one explicit zero-row batch, Date64, missing EOS and the exact file
cap versus one byte below it.
[Fixture and tool hashes](../../scripts/parquet-date-schema-only-oracle/fixtures.json)
· [Oracle](../../scripts/parquet-date-schema-only-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.RoundTrip.SchemaOnly.Thms +Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly.Thms +Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly.Tests +Silmaril.Formats.Parquet.Date.RoundTrip.Thms +Silmaril.Formats.Parquet.Date.RoundTrip.Tests +Silmaril.Formats.Parquet.Date.FromIpc.Multi.Tests +Silmaril.Formats.Parquet.Date.Events.ToIpc.Tests parquet-flat-scan-regression arrow_ipc_metadata_tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-schema-only/Axioms.lean
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/date-schema-only-roundtrip/Axioms.lean
python3 -I scripts/parquet-date-schema-only-oracle/check.py
```

Use `--pyarrow-path` and `--thrift-path` for separately unpacked pinned wheels.
