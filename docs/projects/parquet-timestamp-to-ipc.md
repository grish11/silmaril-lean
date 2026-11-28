# Modern Parquet TIMESTAMP to native Arrow IPC

`Parquet.Timestamp.Leaf.Events.ToIpc.convert` selects one flat, annotated
INT64 TIMESTAMP leaf by its serialized footer ordinal. The root has ordinal
zero. It uses the checked leaf reader's uncompressed PLAIN V1/V2 profile
and emits a native little-endian Arrow V5 stream. The bridge preserves
the leaf name, nullability, and original millis, micros, or nanos unit.
The checked Parquet `isAdjustedToUTC` flag supplies `some "UTC"` for
instants and an absent Arrow annotation for local readings. The signed
nullable ticks travel at the original unit.

[Checked selected-leaf reader](parquet-timestamp-leaf.md) ·
[Typed source events](parquet-timestamp-events.md) ·
[Native TIMESTAMP writer](arrow-timestamp-stream-writer.md)

The source opener caps file bytes, footer group count, and the checked
declared total rows. Existing leaf limits bound groups, pages and payload
decoding. The bridge pulls the selected leaf to EOS in footer order and
then calls the native writer. A source failure returns its original typed
cause and footer index when present. Destination admission follows the
complete successful source trace. The writer applies its independent
batch, body, metadata and aggregate budgets. Each successful group becomes
one explicit Arrow batch, including an admitted empty group.

## Contracts

- `openBound_sound` establishes the exact selected source and input bounds.
  `selectedBinding_exact` preserves the field descriptor and epoch
  interpretation.
- `emit_trace_error` and `convert_first_error` preserve the original first
  failed group, including when the destination budget would fail.
- `emit_readback` preserves the event schema and all nested slot lists.
  `convert_readback` relates the native IPC to the original completed footer
  group reads. The native writer's framing law supplies its exact EOS.

[Theorem header](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Events/ToIpc/Thms.lean)

## Independent readback

The oracle regenerates the six existing pinned PyArrow 26.0.1 TIMESTAMP
files with V2 pages and the independently checked Thrift 0.25.0 framed
empty group. It also pins an existing V1 multi-column producer and selects
its TIMESTAMP at ordinal 5. PyArrow reads the Parquet projection and the
actual Lean-produced IPC independently, matching the descriptor, signed
endpoints, ordered nullable counts, V5 framing and exact consumption
through EOS. The six V2 streams have batch sizes `[3, 0, 3]`. The V1
projection has batch sizes `[6, 6]`.

The existing late-corruption file and a pinned derivative with two damaged
groups check that the original typed source error takes precedence over
destination refusal. Other controls cover the root and a decoy column,
input file, group and row budgets, and destination batch and row budgets.

[Oracle and pinned producer checks](../../scripts/parquet-timestamp-to-ipc-oracle/check.py) ·
[Lean guards](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Events/ToIpc/Tests.lean) ·
[Pinned wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-to-ipc-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-to-ipc
/tmp/parquet-timestamp-to-ipc/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-to-ipc/bin/python -I scripts/parquet-timestamp-to-ipc-oracle/check.py
```
