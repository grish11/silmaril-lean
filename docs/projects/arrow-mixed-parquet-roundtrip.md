# Mixed Arrow IPC round trip through Parquet

[`read_roundTrip`][law] composes [native IPC to mixed Parquet][forward]
and the [nonlegacy selected Parquet to IPC converter][reverse]. The
shared profile is native IPC V5 with exactly one Int32 field followed
by one BinaryView field. The Parquet carrier has one flat, uncompressed
PLAIN V1 row group per source batch. Names, order and required/optional
flags are exact. The observation retains signed Int32 values and
nullable raw octets with no UTF-8 interpretation.

The law assumes successful checked input observation and forward
conversion. It selects the two reverse fields from the original
descriptor, using the forward writer's group readback limits for
reverse admission. The reverse scan may set its own aggregate row cap.
Reverse conversion must succeed under the returned IPC reader's native
limits, and the returned carrier must fit that reader's byte cap.
Under those hypotheses, the exact-EOS checked read of the returned
carrier gives the entire original descriptor and ordered batch
observation. The law concerns observed cells and boundaries. IPC
metadata and buffer encodings may differ.

The original ordinal of every explicit empty RecordBatch survives as
a zero-row group and then an empty batch. A schema-only input is refused
by the forward converter's nonempty-plan policy before Parquet emission.
Invalid names, late source errors, and limit refusals stay at the
corresponding existing conversion stage.

The [oracle][oracle] runs the forward producer and verifies its genuine
Lean Parquet bytes through PyArrow and Thrift. It then converts those
files back to IPC and compares both physical IPC carriers with pinned
PyArrow 26.0.1 through exact V5 Schema/RecordBatch framing and EOS. The
three cases have shapes `[3, 0, 2]`, `[2, 1]`, and `[0]`. They cover
mixed null and empty payloads, signed endpoints, non-UTF-8 octets, and
required and optional fields. Three additional controls cover the
reverse aggregate Parquet row cap, the returned IPC writer's batch
cap, and the returned IPC carrier byte cap.

```sh
lake build --wfail +Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip.Checks
python3.13 scripts/arrow-mixed-parquet-roundtrip-oracle/check.py --out /tmp/arrow-mixed-parquet-roundtrip
```

[law]: ../../Silmaril/Formats/Parquet/MixedV1Writer/FromIpc/RoundTrip/Thms.lean
[forward]: arrow-mixed-ipc-to-parquet.md
[reverse]: parquet-mixed-to-ipc.md
[oracle]: ../../scripts/arrow-mixed-parquet-roundtrip-oracle/check.py
