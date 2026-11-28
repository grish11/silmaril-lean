# Checked flat Parquet footer ColumnOrder

`Footer.ColumnOrder.readFlat limits snapshot column` resolves a zero-based
column ordinal in a checked flat snapshot. It returns the typed physical
schema leaf, the original raw schema and order items with their wire extents,
and an optional typed order marker. The flat profile admits required and
optional physical leaves. The schema root is serialized at ordinal zero,
so the leaf is at schema ordinal `column + 1` and the marker at order ordinal
`column`. Both lists come from FileMetaData in the same checked footer.
[Public API](../../Silmaril/Formats/Parquet/Footer/ColumnOrder/Defs.lean) · [Pinned FileMetaData layout](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L1440-L1457)

The footer-byte cap applies before slicing. Compact depth, fields, collection
size and byte limits apply while traversing the original footer. The exact
root STOP and both list ends must match their advertised extents. Each
selected item occupies a checked interval within its list payload and
ends immediately after its own STOP. If field 7 is present, its length
must match the number of flat leaves. An absent field yields `none`.
Too few or too many entries yield `orderCount expected actual`. Duplicate,
wrong-type, and malformed union fields have typed errors.

The marker reader verifies singleton struct shape and exact payload
consumption. The three defined arms have empty payloads. They are
TYPE_ORDER, IEEE_754_TOTAL_ORDER, and INT96_TIMESTAMP_ORDER. A well-framed
unknown struct arm retains its tag. Marker observation provides wire
metadata. Physical and logical type compatibility, comparison semantics,
and statements about decoded rows belong to consumers.
[Pinned marker structs and union](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L1078-L1102) · [Pinned defined arms](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L1198-L1233)

On a selected leaf, `convertedType` reads field 6 as an exact optional
i32. `logicalMember` reads field 10 as an exact optional struct union,
returning the raw selected member and its payload extent. These accessors
leave the member's logical interpretation to the type-specific APIs.

## Proof and signed compatibility

- `readSelection_wire` ties the source to the checked footer slice. It
  records the exact root STOP, the original field 2 and 7 payloads, and
  each selected item at its original ordinal.
- `readFlat_wire` links the selected raw schema item to the typed snapshot
  lookup at the same ordinal. It proves each item lies within its original
  list and reparses to the retained fields and endpoint.
- `readMarker_sound` proves the observed arm, struct payload extent, and
  the empty payload required for known markers.
- `readOrderFields_eq_reference`, `checkOrder_eq_reference`, and
  `diagnose_eq_reference` compare the entire signed result to the
  original selector and post-read diagnostic. The new raw selector erases
  its item spans to the original callback values and translates its typed
  errors into the original signed errors. Selection failures precede
  annotation presence. Annotation presence precedes any marker
  interpretation, and the marker tag precedes its payload check.
  `read_eq_reference` carries the equality through the whole read result.
[Accessor theorem header](../../Silmaril/Formats/Parquet/Footer/ColumnOrder/Thms.lean) · [Signed compatibility theorem header](../../Silmaril/Formats/Parquet/ColumnIndex/Signed/Compatibility/Thms.lean)

The shared accessor is opt-in. The signed diagnostic uses its raw selection
stage. DATE and TIMESTAMP keep their existing typed annotation APIs.

## Pinned producer and controls

PyArrow 26.0.1 produces two optional physical INT32 leaves. The first
contains signed values including the negative endpoint and has no
annotation. The second is UINT_32 and carries both the converted code and
the modern logical union. Apache Thrift 0.25.0 independently checks the
file's exact footer, original schema and order item spans, marker arms, and
annotation fields. The fixture SHA-256 is
`e429fed1f404dc10876d68b5a4785bd804279fae80e0836375e850ce986180b0`.

The second-marker controls distinguish the two original order ordinals.
They test marker bytes on the original physical INT32 leaf, without
claiming floating-point or timestamp semantics. Other controls cover
missing, short, and surplus lists, wrong field and element types, empty
or multi-arm unions, nonempty known markers, and the footer cap. Signed
controls combine annotation presence with bad order metadata and verify
the original error precedence.
[Fixture](../../data/parquet-footer-column-order/two-leaves.parquet) · [Oracle](../../scripts/parquet-footer-column-order/Oracle.py) · [Extents and hashes](../../scripts/parquet-footer-column-order/observations.txt) · [Producer pins](parquet-column-index.md#pinned-independent-fixture)

```sh
set -o pipefail
replay=$(mktemp -d)
python3 scripts/parquet-footer-column-order/Oracle.py "$replay/two-leaves.parquet" |
  diff -u scripts/parquet-footer-column-order/observations.txt -
cmp data/parquet-footer-column-order/two-leaves.parquet "$replay/two-leaves.parquet"
lake build --wfail +Silmaril.Formats.Parquet.Footer.ColumnOrder.Examples \
  +Silmaril.Formats.Parquet.ColumnIndex.Signed.Examples
```
