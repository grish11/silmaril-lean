# Bounded Parquet INT96 selected-leaf reads

`Silmaril.Formats.Parquet.Int96.File.openFile` checks one in-memory
plaintext Parquet snapshot and selects a flat INT96 leaf by exact name
and required or optional layout. The retained `FlatColumn.Binding`
relates its serialized schema ordinal to the column-chunk ordinal in
that snapshot. Files may contain other flat columns. Reads take no
further byte source, schema, or interpretation argument.
[Checked physical binder](https://github.com/hiloopai/silmaril-lean/pull/4781) ·
[Parquet 2.14.0 Thrift IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

Choose `Policy.prolepticUtc` or `Policy.prolepticLocal` at open. Each
present slot is a mathematical nanosecond coordinate on that policy's
epoch scale, including coordinates beyond signed Int64 nanoseconds.
The footer supplies the physical leaf and framing facts. The caller
supplies the interpretation. Arrow narrowing, writer classification,
timezone adjustment, and Spark rebasing require separate profiles.

The file-byte and total declared row limits are checked at open. The
snapshot validates the footer's row totals, metadata and schema. The
column walk applies its chunk, framing, page and per-group slot caps.
It admits codec 0 (UNCOMPRESSED), PLAIN V1 and V2 pages, and the flat
required and optional level profiles. The callback uses the matched
leaf, column codec, original header and exact body slice. Page
interpretation and mask, extent, count and logical-slot checks are
those of the existing INT96 page adapter.
[INT96 page profile](parquet-int96-page.md)

`Checked.readGroup` reads a single index. `Checked.readAll` visits all
footer ordinals from zero in immutable order and stops at the first
failure. `readFile` combines open and full consumption. A trace has one
list per complete group and the original terminal read error if any.
A failed group contributes zero rows, even when an earlier page in that
group decoded successfully. In particular, the nested page error
retains group and column indices, column name, page index, absolute
header offset and the page's logical slot index.

## Public contracts

- `openFile_sound` ties the checked source and selected leaf to the
  supplied bytes and records the admitted bounds.
- `readGroup_eq_readColumn` preserves the original physical result or
  error. `readGroup_wire` exposes the binder's original chunk and ordered page
  witnesses, with the callback's exact body and the footer row count.
- `readAll_sound` characterizes full success and the exact prefix before
  the first failed read. `readAll_complete` and `readAll_first_error`
  construct the respective observed traces from those binder reads.

[Theorem header](../../Silmaril/Formats/Parquet/Int96/File/Thms.lean)

## Independent fixtures

PyArrow 26.0.1 writes three row groups with two pages per selected
column chunk and an INT32 decoy before the INT96 leaf. The required V1
file uses nanoseconds and covers signed Int64 endpoints and negative
epochs. The optional V2 file uses microseconds and covers mixed nulls,
year 1500 and a mathematical coordinate beyond the Int64 nanosecond
range. PyArrow independently reads signed counts by row group. Python
and Thrift 0.25.0 also check the exact PLAIN words and page extents.

The corrupt file changes only the subday of a present word in group 1,
column 1, page 1, at header offset 298. Its logical slot 2 follows a null
and a valid word. The invalid value is one full day of nanoseconds,
which violates the INT96 word profile. The complete-group trace keeps
only group 0. A separate indexed read verifies that group 2 remains
readable. The scoped Lean test root loads the exact pinned files and
tests both interpretations and the nested failure.

[Fixture generator and SHA-256 pins](../../scripts/parquet-int96-file/check-fixtures.py) ·
[Lean tests](../../Silmaril/Formats/Parquet/Int96/File/Tests.lean) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Int96.File.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Int96.File.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-int96-file/Axioms.lean
python3 -m venv /tmp/parquet-int96-file
/tmp/parquet-int96-file/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-int96-file/bin/python -I scripts/parquet-int96-file/check-fixtures.py
```
