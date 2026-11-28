# Verify Parquet ColumnIndex claims against signed INT32 rows

`ColumnIndex.Signed.read limits binding group` reads one bound flat INT32
column in the selected group of an immutable checked Snapshot. It uses
`FlatColumn.readColumn` and the native PLAIN scalar callback. The initial
profile admits uncompressed, CRC-free V1 and V2 data pages with the
reader's existing flat RLE level rules.

The outer `Except (FlatColumn.Error FlatScan.AdapterError)` carries the
original full-reader error, including any failure in the last page.
A complete read returns all decoded rows with a separate diagnostic.
An absent ColumnIndex gives `.ok none`. Present metadata goes through
the existing wire validator, signed-order admission, and the checks
against decoded slots. A diagnostic error preserves the decoded rows.
This interface offers full validation and has no page-selection operation.
[Full reader contract](../../Silmaril/Formats/Parquet/FlatColumn/Thms.lean) · [ColumnIndex wire contract](parquet-column-index.md)

## Wire meaning and signed profile

The pinned Parquet IDL makes each `null_pages` flag describe whether the
page is entirely null. Such entries carry empty bound placeholders and
the reader must inspect the flag before using the bound lists. Here the flag
is checked against the original slots. All-null pages contribute no
endpoints to the comparisons. A supplied null count must equal the
decoded count. An omitted null-count list makes no count claim.

For each other page, the endpoints are decoded as signed little-endian
INT32 words. They must contain every present value inclusively. Parquet
allows valid bounds that do not occur in the page, so equality to the
actual extrema is unnecessary. ASCENDING and DESCENDING describe the
lower and upper sequences separately in original page order. Checks use
nonstrict comparisons, including across all-null gaps. Ordered intervals
can overlap. UNORDERED imposes no sequence constraint and uses the same
per-page containment checks.
[Pinned ColumnIndex IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L1285-L1348) · [Pinned PageIndex spec](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/PageIndex.md#technical-approach) · [Pinned PLAIN INT32 encoding](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#plain-plain--0)

Signed interpretation has a separate admission check. The exact raw
footer gives the selected schema entry at `binding.leafOrdinal` and the
order at `binding.columnOrdinal`, since the order list is leaf-indexed.
The profile requires singleton `TYPE_ORDER` with an empty struct payload,
and absence of both converted and logical annotations. Unannotated
physical INT32 uses signed comparison. Missing order and annotated or
other sort-order profiles have separate diagnostic outcomes. The wire
validator continues to interpret the bound words as opaque bytes.
[Pinned physical type ordering](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L1102-L1198) · [Pinned footer order field](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L1441-L1457)

## Lean contracts

- `read_error_iff` and `read_ok_iff` identify the exact full-reader error
  and rows and make the diagnostic conditional on read success.
- `checkOrder_sound` witnesses the selected raw footer leaf, absence of
  the annotation fields, and the exact selected `TYPE_ORDER` member.
- `checkPage_sound`, `checkEach_sound`, and `declaredCount_eq` connect the
  checked flags, optional null counts, bound words and signed containment
  with their original positional claims.
- `ordered_iff` proves that checking adjacent endpoints implements the
  requested pairwise monotonicity. `check_sound` applies this independently
  to both endpoint sequences.
- `splitPages_eq` recovers the exact full-reader callback output for
  each page by cutting the flattened rows at the checked page lengths.
  `read_verified` binds the resulting proof to the original snapshot,
  selected group and column, identical framing limits, original frame
  list, and original decoded slots.

The index diagnostic reparses framing through the existing validator.
The full reader performs the sole value decode. The shared proof seam is
`@[expose] FlatColumn.pageSlots`, the existing header-to-count definition.
[Public theorem header](../../Silmaril/Formats/Parquet/ColumnIndex/Signed/Thms.lean)

## Reproducible controls

PyArrow 26.0.1 produces the pinned V1 and V2 PLAIN fixtures. Apache Thrift
0.25.0 independently checks the raw footer, page and index extents, bounds
and counts. Both files have signed extremes, ascending and descending
overlapping intervals, all-null pages between non-null pages, and an
unordered group whose endpoint sequences change direction. The V2 fixture
SHA-256 is `bc056132b17307c091698d43841db26dbffc1e8a41eba5c4a7ac1aafff74760a`.

The V1 mutations preserve wire validity while varying all-null claims, null
counts, containment, and each ordering check separately. Positive controls
include a loose bound and absent null counts. Footer controls cover absent
and unsupported order and a real UINT_32 annotation on the original
physical words. A malformed definition section in the last page produces
the original typed read error even with corrupt index metadata.
[Producer and dependency pins](parquet-column-index.md#pinned-independent-fixture) · [Oracle](../../scripts/parquet-column-index-signed/Oracle.py) · [Observations](../../scripts/parquet-column-index-signed/observations.txt) · [Lean controls](../../Silmaril/Formats/Parquet/ColumnIndex/Signed/Examples.lean)

```sh
set -o pipefail
replay=$(mktemp -d)
python3 scripts/parquet-column-index-signed/Oracle.py "$replay/column-index-v2.parquet" |
  diff -u scripts/parquet-column-index-signed/observations.txt -
cmp data/parquet-column-index/column-index-v2.parquet "$replay/column-index-v2.parquet"
lake build --wfail +Silmaril.Formats.Parquet.ColumnIndex.Signed.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ColumnIndex.Signed.Examples
```
