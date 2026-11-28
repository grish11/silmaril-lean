# Checked Parquet read for a two-leaf optional struct

`NestedPoint.read limits snapshot group` reads the original physical
columns 0 and 1 of one checked row group. The admitted nested profile
has one optional, unannotated struct containing a required INT32 leaf
and an optional INT64 leaf in that order. The actual names come from
the checked footer paths. Each column chunk must contain exactly one
uncompressed, CRC-free PLAIN V1 data page using RLE level tags.

`readLeaf` uses the nested footer selector with the requested physical
and schema profile. It resolves the exact row group's chunk with the
same path and physical type. It checks codec 0 explicitly before
framing, rejects dictionary and index page offsets, and obtains the
chunk's frames from the same immutable snapshot. The body cap is
checked before slicing the singleton frame's payload. The checked
presence decoder accounts for the header sizes, level section and
scalar suffix. Both the chunk value count and the decoded slot count
must equal the footer group row count.

The required leaf has a value exactly when the parent is present.
The optional leaf's parent mask includes both its null-child and
value states. The masks must agree at every row. The PLAIN decoders
consume each scalar suffix at the exact number of value states. The
original masks restore the ordered nullable slots before pairing.
The output `Option (Int32 × Option Int64)` distinguishes an absent
parent, a present parent with a null child, and a present child value.
[Footer binding](parquet-nested-footer-leaf.md) · [Definition-level contract](parquet-nested-definition-presence.md)

## Verification contracts

- `readLeaf_wire` witnesses the original checked schema and physical
  ordinal, selected group's chunk, codec, exact singleton frame chain,
  original payload slice, and checked presence result.
- `assemble_parentMismatch` proves that unequal parent masks produce
  the typed error before scalar decoding. `assemble_wire` ties both
  PLAIN results to the original suffixes and reconstructs their exact
  masks and value sequences. The paired row count equals the source
  slot count.
- `read_wire` composes both leaf witnesses for the same snapshot and
  group with the ordered assembly result.
[Lean theorem header](../../Silmaril/Formats/Parquet/NestedPoint/Thms.lean)

This bounded slice covers a singleton page per leaf. Different sibling
page boundaries, repeated fields, other physical pairs, compression,
and scanner dispatch remain outside this profile.

## Pinned producer and controls

PyArrow 26.0.1 produces and reads the existing optional `point` fixture.
Thrift 0.25.0 independently locates both exact leaf pages. The observed
rows are `(-7, some 2^42)`, an absent parent, and `(0, none)`. The
negative controls change only the original optional definition bits
to disagree about parent positions, remove a value state while keeping
its scalar word, or produce level 3. A separate control changes the
second chunk's codec tag to Snappy while preserving its page bytes.
Lean also checks the footer shape, group index, and body-cap refusals.
[Fixture and producer pins](parquet-nested-footer-leaf.md#independent-fixtures) · [Independent oracle](../../scripts/parquet-nested-point/Oracle.py) · [Observations](../../scripts/parquet-nested-point/observations.txt)

```sh
set -o pipefail
python3 scripts/parquet-nested-point/Oracle.py |
  diff -u scripts/parquet-nested-point/observations.txt -
lake build --wfail +Silmaril.Formats.Parquet.NestedPoint.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.NestedPoint.Examples
```
