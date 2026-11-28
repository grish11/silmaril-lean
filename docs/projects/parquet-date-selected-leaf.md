# Strict selected DATE leaf to native Date32 IPC

`Date.Leaf.openLeaf` takes a zero-based **physical column ordinal** in a
strictly validated flat Parquet file. The shared column-order reader checks
the original raw schema element at ordinal plus one, accounting for the
root. The selected leaf must be required or optional INT32 and carry a
well-formed modern DATE annotation, with converted type absent or equal to
DATE (6). Converted-only DATE is admitted when the modern annotation is
absent. Malformed, conflicting and missing DATE annotations are errors.
DATE values are signed whole days since 1970-01-01.
[Parquet 2.14.0 logical types](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#date)
· [Pinned Parquet IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

The checked binding retains the source snapshot and selected ordinal.
`Date.Leaf.readGroup` uses the original row-group and chunk positions,
checks the exact singleton path and INT32 physical type, and requires the
selected byte span to be disjoint from every other original chunk span.
The strict flat INT32 scanner handles uncompressed PLAIN V1 and V2 data
pages with the existing framing, levels, count and default CRC checks.
Payload decoding is limited to the selected chunks. The strict one-column reader and the
separate single-column page-less compatibility API keep their existing
admission rules.
[Binding and group reader](../../Silmaril/Formats/Parquet/Date/Leaf/Defs.lean)
· [Selection and wire laws](../../Silmaril/Formats/Parquet/Date/Leaf/Thms.lean)
· [Page-less profile](parquet-date-pageless.md)

`Date.Leaf.Events.readAll` enumerates the original footer order. Its
first-error law retains exactly the preceding complete batches with the
original group index and typed cause. `Date.Leaf.Events.toIpc` waits for
successful source exhaustion before invoking the native Date32 writer.
Successful readback recovers the exact field name and nullability, one
batch per original group, and the ordered signed nullable slots. Input
snapshot, page and scan limits are separate from the writer's output
limits. The output is a single-field Date32 stream.
[Event and IPC laws](../../Silmaril/Formats/Parquet/Date/Leaf/Events/Thms.lean)

## Independent checks

PyArrow 26.0.1 produces two three-column files with DATE in the second
or third physical column, alongside an unannotated INT32 and a string
column. The files exercise optional V1 and required V2 pages, signed
Int32 endpoints, negative days, nulls, and multiple groups. Apache Thrift
0.25.0 independently reads the raw DATE annotations. PyArrow checks the
original selected spans and the field descriptor, batch cuts and signed
nullable words of the Lean-emitted IPC streams. A Thrift-guided edit to a
neighbor page leaves the selected output unchanged. Refusal controls cover
an unannotated ordinal, wrong physical type, absent ordinal, overlap, late
selected-page encoding failure, and an IPC batch cap.
[Pinned PyArrow and IPC source](https://github.com/apache/arrow/tree/9e5d6978e9acf372cc989aaaf94e863fe8582c90)
· [Fixture fingerprints and observations](../../scripts/parquet-date-selected-leaf-oracle/fixtures.json)
· [Oracle](../../scripts/parquet-date-selected-leaf-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.Leaf.Thms +Silmaril.Formats.Parquet.Date.Leaf.Events.Thms +Silmaril.Formats.Parquet.Date.Leaf.Events.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-selected-leaf/Axioms.lean
python3 -I scripts/parquet-date-selected-leaf-oracle/check.py
```

The oracle accepts `--pyarrow-path` and `--thrift-path` for separately
unpacked pinned wheels.
