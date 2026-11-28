# Checked Parquet ColumnIndex wire metadata

`ColumnIndex.readFile limits source group column` opens a bounded plaintext
snapshot and selects one zero-based column in a row group. Callers with an
existing checked snapshot can use `ColumnIndex.validate`. An absent
ColumnIndex reference pair yields `ok none` at the selected ordinal.
A present reference requires a successful `OffsetIndex.validate` on the
same snapshot, group and column. This admits its existing flat INT32
profile and uses its original ordered frames. A missing OffsetIndex gives
a typed error. The common Snapshot opener rejects partial references and
invalid footer intervals.
[OffsetIndex profile and frame witness](parquet-offset-index.md)

The validator checks the advertised signed half-open span against the
footer and a byte cap before extracting it. The span follows the selected
data chunk and is disjoint from its OffsetIndex. Compact traversal and
typed list reads use the same collection cap and must consume exactly the
advertised slice, including STOP. The required lists must contain one flag,
lower bound and upper bound for each checked page. All-null claims carry
empty placeholders. Other claims carry two four-byte INT32 words. Missing
null counts remain distinct from present zero counts. A present count
vector has one entry per page, with each count between zero and the
header-derived page row count. The all-null flag agrees with a count
equal to the page row count.

`Index.pages` gives the ordered association of checked original entries
and the raw claims. The index retains the declared boundary-order tag and
original bound bytes. The order of bound values depends on the footer's
`column_orders` and the schema annotations. This slice interprets those
bounds as opaque words and imposes no comparison, including between
successive page ranges. Bounded traversal skips auxiliary fields such as
the repetition and definition histograms. Success certifies wire shape
and declared association. The truth of advertised statistics about
decoded rows requires a separate contract. Page selection and value
decoding continue through their existing readers.
[Pinned page index format](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/PageIndex.md) · [Pinned ColumnIndex IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L1275-L1356)

## Lean contract

- `readExact_ok_iff` and `readPrefix_stop` bind full consumption to the
  original Compact STOP.
- `checkShape_sound` proves list cardinalities, null placeholders, bound
  widths and the present null-count rules. `pages_aligned` recovers the
  original checked page and claim lists from the ordered pairs.
- `validate_present` gives the exact bounded ColumnIndex span, the
  earlier selected chunk and disjoint paired OffsetIndex, the original
  framing witness on that snapshot, and the shape proof.
- `validate_absent_iff` specifies reference absence and `readFile_ok_iff`
  connects file validation to the immutable checked Snapshot.
[Public theorem header](../../Silmaril/Formats/Parquet/ColumnIndex/Thms.lean)

## Pinned independent fixture

PyArrow **26.0.1**, commit `9e5d6978e9acf372cc989aaaf94e863fe8582c90`,
produces the optional PLAIN INT32 file, SHA-256
`1b5710ef7f7291983c2bae4b62a20b34574982268e32fbbea227912b878653a5`.
Apache Thrift **0.25.0**, commit
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`, independently parses the actual
footer, both indexes and original V1 page headers. PyArrow reads back the
rows and checks the producer's advertised min/max words and counts on this
fixture. The three groups exhibit ascending, descending and unordered
tags. Both ordered groups contain all-null pages and overlapping ranges
between non-null pages. The values include both INT32 endpoints.

The Lean examples compare raw bound bytes and exact frame offsets, then
exercise invalid tags and field types, wrong bound widths and count
vectors, negative and inconsistent null counts, duplicate fields,
missing or corrupt paired references, span overlaps, and truncated or
surplus input. The Thrift oracle independently verifies several
metadata mutations from the pinned file and records their hashes.
[Fixture](../../data/parquet-column-index/column-index.parquet) · [Independent oracle](../../scripts/parquet-column-index/Oracle.py) · [Observed bytes and hashes](../../scripts/parquet-column-index/observations.txt) · [Lean controls](../../Silmaril/Formats/Parquet/ColumnIndex/Examples.lean)

Run from the repository root with the pinned Python dependencies on
`PYTHONPATH`. [Dependency pins](parquet-flat-page.md#independent-page-fixtures)

```sh
set -o pipefail
replay=$(mktemp -d)
python3 scripts/parquet-column-index/Oracle.py "$replay/column-index.parquet" |
  diff -u scripts/parquet-column-index/observations.txt -
cmp data/parquet-column-index/column-index.parquet "$replay/column-index.parquet"
lake build --wfail +Silmaril.Formats.Parquet.ColumnIndex.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ColumnIndex.Examples
```
