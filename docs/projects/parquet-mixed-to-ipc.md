# Convert checked mixed Parquet batches to Arrow IPC V5

`Parquet.Int32ByteArrayGroup.ToIpc.convert` takes immutable Parquet bytes,
two explicit field selections and the separately supplied Parquet and
mixed Arrow limits. The selected flat uncompressed PLAIN INT32 and
BYTE_ARRAY leaves become an INT32 field followed by a BinaryView field
with their exact names and nullability. The converter uses
`Prepare.prepare` to exhaust the checked source, then passes the schema
and paired batches to `MixedFlat.StreamWriter.emit`.
[Parquet preparation](parquet-mixed-source-preparation.md) ·
[Mixed Arrow writer](arrow-mixed-flat.md)

Each original footer group contributes one ordered RecordBatch. An
admitted empty group retains its zero-row batch. A schema-only input
retains both declarations and produces zero batches. The readback law
gives the exact schema, row counts, paired signed nullable INT32 and
nullable octets in each original group, and a checked witness that the
wire terminates at exact EOS. Null, an empty octet string and embedded
zero remain distinct.
[Theorem header](../../Silmaril/Formats/Parquet/Int32ByteArrayGroup/ToIpc/Thms.lean)

Source admission and the first selected read failure keep their exact
cause under the source tag. A late failure leaves the previous complete
groups in the separate source trace. Writer refusals keep their original
stage and index after successful preparation. A completed conversion
returns the entire stream.

## Independent verification

CPython 3.13.5, PyArrow 26.0.1 and Thrift 0.25.0 reproduce the seven
preparation input pins. PyArrow opens six actual Lean-emitted V5
streams and compares both field declarations, paired values, batch
sizes and final EOS independently against the selected Parquet rows.
The cases cover the V1 and V2 fixtures with differing page cuts, an
intact sibling selection from a damaged file, the empty-middle
`[3, 0, 2]` shape, nullable INT32 with signed endpoints, and a
schema-only stream. [Source fixture pins](../../scripts/parquet-mixed-preparation-oracle/sha256.json)

The controls cover source byte-cap precedence, selected late failures,
and exact writer errors at both the record and running-budget stages.
The final-group source failure after `[3, 0]` reports group 2, column 1,
page 0 and header byte 108. The indexed writer refusals include the
running row cap at batch 2 and a BinaryView value over 12 bytes at
batch 1, field 1.

```sh
lake build --wfail +Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Checks +Silmaril.Formats.Parquet.Int32ByteArrayGroup.Prepare.Checks
python3.13 -B scripts/parquet-mixed-to-ipc-oracle/check.py --out /tmp/parquet-mixed-to-ipc
```
