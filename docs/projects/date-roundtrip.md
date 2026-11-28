# Checked DATE round trips between Arrow IPC and Parquet

`Parquet.Date.RoundTrip.Observation` records one Date32 field's name,
declared nullability and ordered lists of nullable signed Int32 epoch days.
Each inner list corresponds to one explicit batch or row group. The
IPC projection has unit DAY. The Parquet relation opens one checked
snapshot and reads every footer index in order. It projects the logical
descriptor and the same signed words. The raw annotation and file layout are
outside this observation.
[Observation API](../../Silmaril/Formats/Parquet/Date/RoundTrip/Defs.lean)

The endpoints use the existing one-column profiles. IPC uses the checked
little-endian DATE V5 stream with explicit EOS and unit DAY. Parquet input
uses the checked required or optional flat INT32 DATE binder with
uncompressed PLAIN V1 or V2 and rejects page CRCs. The reverse writer emits PLAIN V1 and both
modern DATE and matching converted type 6. The input binder admits modern
DATE, matching modern and converted DATE, or converted-only DATE.
[IPC profile](arrow-date-stream.md)
· [Parquet DATE admission](parquet-date-binding.md)
· [Parquet to IPC](parquet-date-to-ipc.md)
· [IPC to Parquet groups](date32-ipc-to-parquet-groups.md)

Both round-trip laws require each conversion to succeed. For
`ipc_roundtrip`, the reverse writer and forward reader use the same
`Date.Limits` on the intermediate file. The source and returned IPC budgets
may differ. For `parquet_roundtrip`, the reverse reader uses the forward
IPC writer's `ObservationLimits.ipc` on the intermediate stream. The
Parquet endpoint budgets may differ. The laws obtain a positive number of
explicit batches from successful multibatch preflight. One zero-row group
has one explicit empty batch. A schema-only file can yield schema-only
IPC, which the reverse converter refuses with `batchCount 0`.

`ipc_roundtrip` gives a single observation for the source and returned IPC
streams and the checked Parquet intermediate. `parquet_roundtrip` gives a
single observation for both checked Parquet endpoints and the IPC
intermediate. `parquet_at` identifies the exact checked footer count and,
at every observed index, the original group reader, ordered nullable words
and row count. These proofs use the existing one-way contracts and the
Date32 scalar inverses.
[Theorem header](../../Silmaril/Formats/Parquet/Date/RoundTrip/Thms.lean)

## Pinned probes

CPython 3.13.5 and PyArrow 26.0.1 produce three Date32 IPC inputs with
optional and required fields, signed endpoints, nulls, leading, middle and
trailing empties, and a stream with three explicit empty batches. The
oracles compare the returned IPC descriptor and batches and read every
group of both Lean-emitted Parquet files independently. Thrift 0.25.0 checks
the DATE leaf annotations and exact V1 page bodies and extents.

A previously pinned converted-only Parquet fixture uses a labeled Thrift
edit of a PyArrow footer. Its return trip recovers the logical descriptor
and signed slots while emitting both DATE annotations. An independent
PyArrow file with zero row groups produces schema-only IPC and exercises
the typed reverse refusal.
[Fixture and tool hashes](../../scripts/date-roundtrip-oracle/fixtures.json)
· [Oracle](../../scripts/date-roundtrip-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.RoundTrip.Thms +Silmaril.Formats.Parquet.Date.RoundTrip.Tests +Silmaril.Formats.Parquet.Date.FromIpc.Multi.Thms +Silmaril.Formats.Parquet.Date.FromIpc.Multi.Tests +Silmaril.Formats.Parquet.Date.Events.ToIpc.Thms +Silmaril.Formats.Parquet.Date.Events.ToIpc.Tests parquet-flat-scan-regression arrow_ipc_metadata_tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/date-roundtrip/Axioms.lean
python3 -I scripts/date-roundtrip-oracle/check.py
```

Use `--pyarrow-path` and `--thrift-path` for separately unpacked pinned wheels.
