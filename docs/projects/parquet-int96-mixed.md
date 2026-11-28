# Mixed PLAIN and dictionary INT96 chunks

`Silmaril.Formats.Parquet.Int96.Mixed.read` reads one bounded uncompressed
INT96 column chunk for a flat required or optional leaf. The caller supplies
the original source, footer boundary, expected row count, leaf metadata,
limits, and an explicit proleptic UTC or local interpretation. The output
has exact mathematical nanoseconds and retains the type of that
interpretation. Rebasing, Arrow narrowing, and file-level mixed dispatch
are separate profiles.

[INT96 wire words and interpretation](parquet-int96.md) ·
[Standalone PLAIN page profile](parquet-int96-page.md) ·
[Standalone dictionary chunk profile](parquet-int96-dictionary.md)

The checked column span starts at the declared dictionary offset. The
frame there has page type DICTIONARY_PAGE and PLAIN encoding 0 for its
12-byte words. Its decoded entries form the only dictionary for this
chunk. The declared data offset points to the next frame. Subsequent
frames must be data pages, each with its own actual version and encoding
tag. Tag 0 reads exact PLAIN words. Tag 8 reads RLE_DICTIONARY references
against the leading entries. The dispatcher reads the original body for
the branch selected by the header. A producer may switch encodings within
the chunk, and frame order determines slot order.

Column admission uses the dictionary profile's codec 0 and bounded extent,
matching flat leaf path and row count, and permissible metadata encoding
tags. The frame walk bounds each original header and body in that extent.
The reader checks the sum of the data-frame slot counts before decoding
their values. Both branches use the same scalar limits and their existing
V1/V2 definition-level and exact extent checks. Repeated leaves,
CRC-bearing frames, late dictionaries, index pages, and data encoding
tag 2 are outside this profile.

The chunk error carries the original dictionary offset if present.
A selected frame error also carries the zero-based frame ordinal and
absolute header offset, with the leading dictionary at ordinal zero.
Branch errors preserve the original typed cause. A bad PLAIN word or
dictionary reference includes the logical slot, counting preceding nulls.
A bad dictionary word instead includes its entry index in frame zero.

[Parquet 2.14.0 encoding definitions](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md) ·
[Thrift IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

## Contracts

- `planData_sound` retains the original frame, ordinal and header
  parameters and relates the dispatch tag to the declared encoding.
- `decodePage_dispatch` identifies the exact original decoder call and
  indexed error wrapper. `decodePage_wire` proves its declared slot count.
- `read_wire` retains the same-source frame walk and leading dictionary.
  The page results are ordered by the original frames and flatten to
  exactly the declared row count. The existing PLAIN and dictionary wire
  laws provide each branch's exact nullable word or reference observation.

[Theorem header](../../Silmaril/Formats/Parquet/Int96/Mixed/Thms.lean)

## Independent fixtures

PyArrow 26.0.1 produces two optional uncompressed timestamp files,
one with V1 data pages and one with V2 data pages. The writer reaches its
36-byte dictionary budget and falls back to PLAIN in each file. PyArrow
independently reads all 24 signed nullable nanosecond counts from each.
Thrift 0.25.0 checks the original frame offsets, exact extent, four
ordered dictionary words, and the four data frames with encodings
`8, 8, 0, 0`. It checks definition masks and either the original packed
references or the signed PLAIN words for each frame.

The pinned derivatives create a bad PLAIN word at V1 frame 3, header
offset 123, logical slot 2, and a missing reference at V2 frame 2,
header offset 83, logical slot 3. Both logical indices count a preceding
null. In the second derivative the leading dictionary is shortened and
the original data frames are preserved byte for byte. The Lean guards
also cover missing and misplaced dictionaries, wrong data offset,
legacy tag 2, count mismatch, truncation and resource caps. An alternating
frame order checks independent per-header dispatch. Regression guards
exercise the standalone readers' typed refusal of the opposite
data encoding.

[Fixture generator and SHA-256 pins](../../scripts/parquet-int96-mixed/check-fixtures.py) ·
[Lean guards](../../Silmaril/Formats/Parquet/Int96/Mixed/Tests.lean) ·
[Pinned wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Int96.Mixed.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Int96.Mixed.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-int96-mixed/Axioms.lean
python3 -m venv /tmp/parquet-int96-mixed
/tmp/parquet-int96-mixed/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-int96-mixed/bin/python -I scripts/parquet-int96-mixed/check-fixtures.py
```
