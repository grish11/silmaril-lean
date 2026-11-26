# Parquet V1 page for nullable LIST of nullable INT32

`ListPage.decodeV1` is a bounded page decoder for the canonical physical
profile below. The caller supplies the matched V1 header and complete
body, the admitted schema, the column codec, and the expected number of
rows on the page. In the producer fixture one page covers the entire
checked row group, so its footer row count supplies that expectation.

```text
optional group items (LIST) {
  repeated group list {
    optional int32 element;
  }
}
```

The canonical path has maximum repetition level 1 and definition level 3.
At repetition zero, definition zero denotes a null list, one an empty
list, two a list starting with a null element, and three a list starting
with a present value. Repetition one can extend only a previously opened
nonempty list and must have definition two or three. The decoder starts
without an open list and rejects a continuation, even when its
definition level would otherwise admit an element.
[Pinned canonical LIST schema](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#lists) · [Pinned nested encoding](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md#nested-encoding)

The wrapper checks codec 0, CRC absence, PLAIN values, both RLE level
tags, and exact body size. Two bounded little-endian length words delimit
the repetition and definition streams, in that order. Both exact Hybrid
decodes use the header's slot count with widths 1 and 2. The existing
final packed-run padding rules apply. Only definition level 3 consumes
a signed little-endian INT32 word. The exact PLAIN reader rejects
insufficient or surplus words. The row reconstruction validates
transitions and compares the result to the supplied row count.
[Pinned V1 body order](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md#data-pages) · [Pinned Hybrid encoding](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#run-length-encoding--bit-packing-hybrid-rle--3)

`reconstruct_wire` proves that the rows emit exactly the original event
sequence, including list starts and element order.
`reconstruct_continuation` proves the leading continuation refusal.
`decodeBody_wire` ties those events to the original ordered level slots
and exact PLAIN values and accounts for every input byte.
`decodeV1_wire` also binds the header tags, sizes, slot count, and codec.
[Lean contract](../../Silmaril/Formats/Parquet/ListPage/Thms.lean)

This slice expects one page of complete rows and closes its final list
at the page boundary. It carries no row state across pages. A page body
alone cannot establish that a following page does not continue its
final list. Callers must establish that scope, as with the one-page
group fixture. File-level LIST schema admission and framing, older LIST
layouts, recursively nested elements, V2, and scanner routing are
outside this profile.

## Producer fixture

PyArrow 26.0.1 generates the canonical schema and reads back
`[None, [], [None], [-7, None, 0], [9, None]]`. Apache Thrift 0.25.0
independently verifies the original LIST annotation and path, codec,
five footer rows, eight header level slots, and page extents. The
oracle independently unpacks both streams and checks the PLAIN words.
The fixture SHA-256 is
`e54b974102a55ace9849e3b060fb77a967309c0999c59713ccf85410530c510e`.
Lean exercises the decoder on the actual frame from the checked
snapshot. Corruption controls include leading and post-empty
continuations, a repeated empty marker, a wrong header slot count, a
wrong expected row count, and invalid scalar extent.
[Fixture](../../data/parquet-list-v1/nullable-int32.parquet) · [Producer pins](parquet-column-index.md#pinned-independent-fixture) · [Oracle](../../scripts/parquet-list-v1/Oracle.py) · [Observations](../../scripts/parquet-list-v1/observations.txt)

```sh
set -o pipefail
replay=$(mktemp -d)
python3 scripts/parquet-list-v1/Oracle.py "$replay/nullable-int32.parquet" |
  diff -u scripts/parquet-list-v1/observations.txt -
cmp data/parquet-list-v1/nullable-int32.parquet "$replay/nullable-int32.parquet"
lake build --wfail +Silmaril.Formats.Parquet.ListPage.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListPage.Examples
```
