# Parquet nested sibling alignment across independent page cuts

`NestedPoint.Multi.read limits snapshot group` extends the required
INT32 and optional INT64 pair under one optional, unannotated struct.
Each leaf uses its own original page sequence from the checked snapshot.
The separate singleton reader keeps its existing API and checks.

For each column, the binder verifies the selected physical type, leaf
repetition, original path, local chunk, codec 0, and absence of
dictionary and index page offsets. The reader bounds the rows, chunk
extent, framed page count, and individual payload bytes. The footer
chunk count and the sum of V1 header counts must agree with the
original group count before any values are decoded. Every page then
passes the checked presence decoder for uncompressed, CRC-free PLAIN
V1 bodies with RLE levels. Its own scalar suffix is decoded at the
exact count of present values. No page can borrow scalar bytes from
another page.

Both columns concatenate their reconstructed row slots and definition
states in original frame order. Once both walks succeed, the reader
compares their parent masks and pairs the row slots. The parent
comparison uses the concatenated row positions, so the page cuts and
number of pages can differ. A late disagreement returns
`.parentPresence`. A scalar or level error is reported first with the
original column ordinal and frame header offset.
[Singleton profile](parquet-nested-point.md) · [Definition-level contract](parquet-nested-definition-presence.md)

## Proofs

- `decodeFrame_wire` ties the exact same-source payload slice to the
  level semantics, its own PLAIN decode, reconstructed slot mask and
  ordered values, and header-derived slot and state counts.
- `readColumn_wire` witnesses both original ordinals, path and chunk,
  exact frame chain, and a pointwise wire witness for every page. The
  output is the concatenation of those pages and has the original
  group count.
- `read_wire` relates both independent column walks and establishes
  identical parent masks and the exact ordered row pairing and count.
  `read_parentMismatch` proves the typed result when both walks
  succeed and the row-level masks differ.
[Lean theorem header](../../Silmaril/Formats/Parquet/NestedPoint/Multi/Thms.lean)

The profile covers the named physical pair and V1 pages. Repeated
fields, deeper structs, other encodings and codecs, and scanner routing
are outside this slice.

## Pinned producer

PyArrow 26.0.1 produced a 12-row fixture with page slot counts
`[6, 6]` for INT32 and `[2, 4, 2, 4]` for INT64. The writer uses
uncompressed PLAIN, `data_page_size=16`, and `write_batch_size=2`.
Apache Thrift 0.25.0 reads the original page windows, and the oracle
independently checks the RLE and packed definition levels against
PyArrow's full rows and PLAIN scalar bytes. The pinned fixture SHA-256
is `cb5b8ede855189f8ff69a3437ba2adfda76f6bfc8614bae17ff71f33b2849bbc`.

The last optional page supplies three file-derived controls. They
shift one absent position while preserving the value count, advertise
one fewer row slot, or request three INT64 values from two original
words. Lean also checks the caps and singleton behavior.
[Fixture](../../data/parquet-nested-multipage/unequal-cuts.parquet) · [Producer pins](parquet-column-index.md#pinned-independent-fixture) · [Oracle](../../scripts/parquet-nested-multipage/Oracle.py) · [Observed extents and hashes](../../scripts/parquet-nested-multipage/observations.txt)

```sh
set -o pipefail
replay=$(mktemp -d)
python3 scripts/parquet-nested-multipage/Oracle.py "$replay/unequal-cuts.parquet" |
  diff -u scripts/parquet-nested-multipage/observations.txt -
cmp data/parquet-nested-multipage/unequal-cuts.parquet "$replay/unequal-cuts.parquet"
lake build --wfail +Silmaril.Formats.Parquet.NestedPoint.Multi.Examples
```
