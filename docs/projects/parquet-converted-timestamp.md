# Converted-only Parquet TIMESTAMP to Arrow IPC

Pass `.allowConvertedOnly` to `Timestamp.readMetadataWith`,
`Timestamp.Leaf.openLeafWith`, or `Timestamp.Leaf.Events.ToIpc.convertWith`
to admit legacy INT64 TIMESTAMP annotations. These entry points select the
original serialized leaf ordinal, with the root at zero. For a leaf whose
Compact SchemaElement has no LogicalType field 10, ConvertedType field 6
must be a checked i32 with code 9 (`TIMESTAMP_MILLIS`) or code 10
(`TIMESTAMP_MICROS`). The descriptor uses that exact unit and the UTC epoch.
The Arrow field then carries the exact timezone string `UTC`. Signed Int64
ticks retain their original unit and count throughout.

A present LogicalType uses the checked modern parser. A matching legacy tag
agrees on unit and leaves the modern adjusted flag in control, so a modern
local value remains local. A conflicting tag or malformed modern annotation
is an error. The default metadata, leaf and IPC entry points require the
modern annotation.

[Parquet TIMESTAMP compatibility](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#timestamp) ·
[ConvertedType wire codes](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift) ·
[Annotation laws](../../Silmaril/Formats/Parquet/Timestamp/Thms.lean)

## Checked leaf, events and IPC

The admitted physical profile is a selected flat required or optional INT64
leaf with uncompressed PLAIN V1 or V2 pages and the existing RLE definition
level checks. Binding retains the checked snapshot and original leaf ordinal.
Group reads use its original chunk path, physical type, row count and disjoint
page frames. `Leaf.Events.readBound` emits those groups in footer order, with
a batch for every successfully read group, including an empty group. A read
failure keeps the complete prefix in events and propagates the original group
index and cause through IPC conversion before writer admission.

The converter checks file bytes, groups and total rows before reading groups.
Footer, page, level and destination IPC budgets use the existing limits.
Successful output reads back to the exact selected descriptor and the
reference group's ordered nullable ticks through EOS. INT96 and calendar
rebasing have separate entry points.

[Leaf laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Thms.lean) ·
[Event laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Events/Thms.lean) ·
[IPC laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Events/ToIpc/Thms.lean)

## Pinned interoperability

The oracle uses CPython 3.13.5, PyArrow 26.0.1 and Thrift 0.25.0. PyArrow
generates the data pages. Deterministic Compact Thrift edits produce the
converted-only footers and check that the data bytes remain identical. The
V1 millis case selects an optional leaf at ordinal three in a multicolumn
file. The V2 micros case selects a required leaf and has an explicit empty
group, supplied by a zero-row Thrift page because PyArrow's original group
has no page of its own. Both include signed Int64 endpoints. A modern local
dual-annotation control retains its absent Arrow timezone. PyArrow reads
the original selected groups and actual Lean-emitted IPC. Typed controls
include a conflicting dual annotation, a wrong modern union with a valid
legacy code, a wrong selection, a group limit, and a corrupt last page
with its earlier empty batch retained.

[Oracle and fixture generation](../../scripts/parquet-converted-timestamp-oracle/check.py) ·
[SHA-256 pins](../../scripts/parquet-converted-timestamp-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Tests +Silmaril.Formats.Parquet.Timestamp.Leaf.Thms'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-converted-timestamp-oracle/Axioms.lean
python3 -m venv /tmp/parquet-converted-timestamp
/tmp/parquet-converted-timestamp/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-converted-timestamp/bin/python -I scripts/parquet-converted-timestamp-oracle/check.py
```
