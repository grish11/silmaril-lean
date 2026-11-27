# Native mixed Arrow IPC to ordered Parquet row groups

`Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.convert source sink input`
reads one immutable IPC V5 stream through the existing [mixed native
reader and typed observation][reader]. The compatible descriptor is
exactly one Int32 field followed by one BinaryView field. The Parquet
schema takes their exact names and required/optional flags in that
order. The sink requires distinct, nonempty names. BinaryView slots
become physical BYTE_ARRAY values by copying their opaque octets.
Nulls, present empty values, embedded zero and non-UTF-8 bytes remain
distinct.

The adapter completes native framing and exact EOS checks before
planning. Each record batch supplies the two typed lists for one
[mixed Parquet V1 row group][writer] at the same ordinal. Empty batches
become real zero-row groups with page headers. A schema-only input has
zero batches and returns `plan noBatches` under the sink's nonempty-plan
policy. A reversed schema returns `plan fieldOrder`. Other IPC kinds
remain subject to the checked reader's typed profile.

Source and sink limits are separate. The source applies the carrier,
framing, row/cell, and view bounds. The sink applies its own group,
aggregate row, file, footer, page, and scalar bounds, then its checked
mixed-reader limits. The adapter uses the checked source observation in
memory before constructing a complete file. It returns no file on a
source, planning or sink failure. Late truncation and missing EOS retain
their original native reader error and index.

[`prepare_exact`][laws] relates the labels and ordered pairs to the
source observation. `convert_indexed` relates each checked IPC batch to
the actual Parquet group's original wire chunks and exact ordered
nullable slots. `convert_schema_only` expresses the distinct no-batch
case. Source and sink error laws retain their stage and cause.

The [oracle][oracle] runs PyArrow 26.0.1 on eight pinned Arrow carriers
and compares the three genuine Lean files through PyArrow and Thrift
0.25.0. Success includes group shapes `[3, 0, 2]`, `[2, 1]`, and
`[0]`, nullable and required fields, and opaque binary inputs. The
oracle checks exact names, nullability, body bytes and indexed rows,
with ten typed refusal controls.

```sh
lake build --wfail +Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Checks
python3.13 scripts/arrow-mixed-ipc-to-parquet-oracle/check.py --out /tmp/arrow-mixed-ipc-to-parquet
```

[reader]: arrow-mixed-named-table.md
[writer]: parquet-mixed-v1-multi-writer.md
[laws]: ../../Silmaril/Formats/Parquet/MixedV1Writer/FromIpc/Thms.lean
[oracle]: ../../scripts/arrow-mixed-ipc-to-parquet-oracle/check.py
